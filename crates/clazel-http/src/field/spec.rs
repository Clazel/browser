//! Executable-style specification of HTTP field syntax, transcribed from
//! RFC 9110 "HTTP Semantics". Nothing here runs; it defines what "correct"
//! means. Every definition cites its section and quotes the grammar it
//! transcribes; each `// N.` comment is a step in the cited text.
//!
//! Source (pinned; an RFC never changes after publication): RFC 9110, June
//! 2022, <https://www.rfc-editor.org/rfc/rfc9110>:
//! - §5.1 field names; §5.2 field lines and the combined field value; §5.3
//!   field order (comma SP, and the `Set-Cookie` note); §5.5 field values;
//!   §5.6.1 lists (`#rule`), recipient requirements; §5.6.2 tokens; §5.6.3
//!   whitespace; §5.6.4 quoted strings; §5.6.6 parameters;
//! - §7.6.1 `Connection`; §8.6 `Content-Length`;
//! - §10.1.4 `transfer-coding` and `transfer-parameter` (RFC 9112 §6.1 says
//!   `Transfer-Encoding = #transfer-coding` and takes the production from
//!   there);
//! - the core rules `ALPHA`, `DIGIT`, `DQUOTE`, `HTAB`, `SP`, `VCHAR` are
//!   RFC 5234 Appendix B.1.
//!
//! Modelling choices (each a deliberate deviation in form, never in
//! meaning):
//! - A string is a `Seq<u8>`: field values are octets (§5.5).
//! - ABNF is read by a parser that decides each choice with the next octet.
//!   That is exact here: a `token` is the longest run of `tchar`s (no rule
//!   that can follow a token starts with a `tchar`); `OWS` is the longest
//!   run of SP and HTAB (the rule after it starts with something else);
//!   `parameter-value` is a `quoted-string` exactly when it starts with
//!   DQUOTE (`tchar` excludes it); and inside a `quoted-string`, `qdtext`
//!   excludes DQUOTE and "\", so each octet decides between `qdtext`,
//!   `quoted-pair` and the closing DQUOTE. A run is measured by its length
//!   ([`run_len`]) and the rest of the string is a suffix ([`Seq::skip`]).
//! - "Case-insensitive" (§5.1, §5.6.6, §7.6.1) is comparison after mapping
//!   `A`-`Z` to `a`-`z` ([`ascii_lowercase`]); RFC 5234 §2.3 says the
//!   letters of a quoted ABNF string are matched that way.
//! - A list (§5.6.1.2) of elements whose own grammar can contain a comma
//!   only inside a `quoted-string` (every list in this crate: tokens,
//!   transfer codings with parameters, digits) is read by splitting at each
//!   comma that is not inside a quoted string, and stripping OWS from each
//!   piece ([`split_values`]). A piece is then checked against the
//!   element's grammar. A DQUOTE outside a quoted string starts one, as in
//!   the grammar, where a DQUOTE can only start a `quoted-string`; a
//!   piece with a stray DQUOTE is never a valid element, so no list is
//!   accepted that the grammar would reject, and no comma inside a
//!   well-formed quoted string separates elements. [`list_elements`] drops
//!   the empty pieces, as §5.6.1.2 requires ("empty elements do not
//!   contribute to the count of elements present"); the count of
//!   elements that remain is the caller's: for `1#element` it requires at
//!   least one.
//! - The `1*DIGIT` of `Content-Length` (§8.6) is a `nat` here
//!   ([`decimal_value`]); the executable parser reports a value above
//!   `u64::MAX` as too large, which is how §8.6 says to handle
//!   "potentially large decimal numerals".
//! - §8.6's list case ("the same decimal value repeated as a
//!   comma-separated list") is read as the same digits repeated, so `42, 42`
//!   is a repeat and `42, 042` is not: §8.6 lets a recipient reject the
//!   message, and rejecting is the safe reading when two parsers could
//!   disagree about what `042` means. A list with an empty member
//!   (`42,,42`) is not a list of that value either: [`split_values`] keeps
//!   empty pieces, [`list_elements`] is the one that drops them, and
//!   `Content-Length` uses the former.
//! - Several field lines of one name are combined with ", " (§5.3: "separated
//!   by a comma (",") and optional whitespace ... For consistency, use
//!   comma SP"). A field line's value is the value after §5.5's removal of
//!   leading and trailing whitespace ([`strip_ows`]); the framing layer
//!   (RFC 9112 §5, Phase 3 item 3.2) does that.
//! - `Set-Cookie` is never combined (§5.3's note): [`combined_field_value`]
//!   is `None` for it, and [`set_cookie_lines`] gives its lines one by one.
//! - A transfer coding's parameters use RFC 9110 §10.1.4's
//!   `transfer-parameter` (BWS allowed around "=", and no empty
//!   parameters), a different production from §5.6.6's `parameter`; one
//!   function reads both, selected by [`ParameterGrammar`].
//! - A `quoted-string` parameter value is kept unquoted (§5.6.4: "handle a
//!   quoted-pair as if it were replaced by the octet following the
//!   backslash"). Per §5.6.6 "the quoted and unquoted values are
//!   equivalent", so the parameter record does not say which was used.
//!   Parameter names are kept as received; compare them with
//!   [`field_name_eq`].

#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ===========================================================================
// RFC 5234 core rules, and RFC 9110 §5.5 / §5.6.2 / §5.6.4 character classes.
// ===========================================================================

/// RFC 5234 B.1: `ALPHA = %x41-5A / %x61-7A`.
pub open spec fn is_alpha(c: u8) -> bool {
    (0x41 <= c <= 0x5A) || (0x61 <= c <= 0x7A)
}

/// RFC 5234 B.1: `DIGIT = %x30-39`.
pub open spec fn is_digit(c: u8) -> bool {
    0x30 <= c <= 0x39
}

/// RFC 5234 B.1: `VCHAR = %x21-7E`.
pub open spec fn is_vchar(c: u8) -> bool {
    0x21 <= c <= 0x7E
}

/// §5.5: `obs-text = %x80-FF`.
pub open spec fn is_obs_text(c: u8) -> bool {
    0x80 <= c <= 0xFF
}

/// RFC 5234 B.1: `SP = %x20`.
pub open spec fn is_sp(c: u8) -> bool {
    c == 0x20
}

/// RFC 5234 B.1: `HTAB = %x09`.
pub open spec fn is_htab(c: u8) -> bool {
    c == 0x09
}

/// An octet of `OWS`, `RWS` or `BWS` (§5.6.3): `SP / HTAB`.
pub open spec fn is_ows_octet(c: u8) -> bool {
    is_sp(c) || is_htab(c)
}

/// §5.5: `field-vchar = VCHAR / obs-text`.
pub open spec fn is_field_vchar(c: u8) -> bool {
    is_vchar(c) || is_obs_text(c)
}

/// An octet of `1*( SP / HTAB / field-vchar )` (§5.5).
pub open spec fn is_field_content_octet(c: u8) -> bool {
    is_sp(c) || is_htab(c) || is_field_vchar(c)
}

/// §5.6.2: `tchar = "!" / "#" / "$" / "%" / "&" / "'" / "*" / "+" / "-" /
/// "." / "^" / "_" / "`" / "|" / "~" / DIGIT / ALPHA`.
pub open spec fn is_tchar(c: u8) -> bool {
    c == 0x21 || c == 0x23 || c == 0x24 || c == 0x25 || c == 0x26 || c == 0x27
        || c == 0x2A || c == 0x2B || c == 0x2D || c == 0x2E || c == 0x5E || c == 0x5F
        || c == 0x60 || c == 0x7C || c == 0x7E || is_digit(c) || is_alpha(c)
}

/// §5.6.2: "Delimiters are chosen from the set of US-ASCII visual
/// characters not allowed in a token (DQUOTE and "(),/:;<=>?@[\]{}")."
pub open spec fn is_delimiter(c: u8) -> bool {
    c == 0x22 || c == 0x28 || c == 0x29 || c == 0x2C || c == 0x2F || c == 0x3A || c == 0x3B
        || c == 0x3C || c == 0x3D || c == 0x3E || c == 0x3F || c == 0x40 || c == 0x5B
        || c == 0x5C || c == 0x5D || c == 0x7B || c == 0x7D
}

/// §5.6.4: `qdtext = HTAB / SP / %x21 / %x23-5B / %x5D-7E / obs-text`.
pub open spec fn is_qdtext(c: u8) -> bool {
    c == 0x09 || c == 0x20 || c == 0x21 || (0x23 <= c <= 0x5B) || (0x5D <= c <= 0x7E)
        || is_obs_text(c)
}

/// The octet after the backslash of a `quoted-pair` (§5.6.4):
/// `quoted-pair = "\" ( HTAB / SP / VCHAR / obs-text )`.
pub open spec fn is_quoted_pair_octet(c: u8) -> bool {
    is_htab(c) || is_sp(c) || is_vchar(c) || is_obs_text(c)
}

/// The classes of octets a string can be required to consist of.
pub enum Class {
    /// `tchar` (§5.6.2)
    Tchar,
    /// `DIGIT`
    Digit,
    /// `SP / HTAB` (§5.6.3)
    Ows,
    /// `SP / HTAB / field-vchar` (§5.5)
    FieldContent,
    /// the octet after a backslash in a `quoted-pair` (§5.6.4)
    QuotedPair,
}

/// Does `c` belong to `class`?
pub open spec fn in_class(class: Class, c: u8) -> bool {
    match class {
        Class::Tchar => is_tchar(c),
        Class::Digit => is_digit(c),
        Class::Ows => is_ows_octet(c),
        Class::FieldContent => is_field_content_octet(c),
        Class::QuotedPair => is_quoted_pair_octet(c),
    }
}

/// Every octet of `s` is in `class`.
pub open spec fn all_in(s: Seq<u8>, class: Class) -> bool
    decreases s.len()
{
    s.len() == 0 || (in_class(class, s[0]) && all_in(s.drop_first(), class))
}

/// The length of the longest prefix of `s` made of octets in `class`.
pub open spec fn run_len(class: Class, s: Seq<u8>) -> nat
    decreases s.len()
{
    if s.len() > 0 && in_class(class, s[0]) {
        1 + run_len(class, s.drop_first())
    } else {
        0
    }
}

// ===========================================================================
// §5.1 field names, §5.6.2 tokens.
// ===========================================================================

/// §5.6.2: `token = 1*tchar`.
pub open spec fn is_token(s: Seq<u8>) -> bool {
    s.len() > 0 && all_in(s, Class::Tchar)
}

/// §5.1: `field-name = token`.
pub open spec fn is_field_name(s: Seq<u8>) -> bool {
    is_token(s)
}

/// ASCII lowercase: `A`-`Z` become `a`-`z` (RFC 5234 §2.3).
pub open spec fn ascii_lowercase(s: Seq<u8>) -> Seq<u8> {
    s.map_values(|c: u8| if 0x41 <= c <= 0x5A { (c + 0x20) as u8 } else { c })
}

/// §5.1: "Field names are case-insensitive". Also §5.6.6 (parameter names)
/// and §7.6.1 (connection options).
pub open spec fn field_name_eq(a: Seq<u8>, b: Seq<u8>) -> bool {
    ascii_lowercase(a) == ascii_lowercase(b)
}

// ===========================================================================
// §5.6.3 whitespace.
// ===========================================================================

/// §5.6.3: `OWS = *( SP / HTAB )`.
pub open spec fn is_ows(s: Seq<u8>) -> bool {
    all_in(s, Class::Ows)
}

/// §5.6.3: `RWS = 1*( SP / HTAB )`.
pub open spec fn is_rws(s: Seq<u8>) -> bool {
    s.len() > 0 && all_in(s, Class::Ows)
}

/// §5.6.3: `BWS = OWS`.
pub open spec fn is_bws(s: Seq<u8>) -> bool {
    is_ows(s)
}

/// `s` without its leading OWS (the rest after the longest `OWS` prefix).
pub open spec fn strip_leading_ows(s: Seq<u8>) -> Seq<u8> {
    s.skip(run_len(Class::Ows, s) as int)
}

/// `s` without its trailing OWS.
pub open spec fn strip_trailing_ows(s: Seq<u8>) -> Seq<u8>
    decreases s.len()
{
    if s.len() > 0 && is_ows_octet(s.last()) {
        strip_trailing_ows(s.drop_last())
    } else {
        s
    }
}

/// `s` without leading and trailing OWS (§5.5: "A field value does not
/// include leading or trailing whitespace").
pub open spec fn strip_ows(s: Seq<u8>) -> Seq<u8> {
    strip_trailing_ows(strip_leading_ows(s))
}

// ===========================================================================
// §5.5 field values.
// ===========================================================================

/// §5.5: `field-value = *field-content`, `field-content = field-vchar [
/// 1*( SP / HTAB / field-vchar ) field-vchar ]`: empty, or beginning and
/// ending with a `field-vchar`, with only SP, HTAB and `field-vchar`
/// between.
pub open spec fn is_field_value(s: Seq<u8>) -> bool {
    s.len() == 0 || (is_field_vchar(s[0]) && is_field_vchar(s.last())
        && all_in(s, Class::FieldContent))
}

// ===========================================================================
// §5.2 field lines, the combined field value, and §5.3's Set-Cookie note.
// ===========================================================================

/// A field line (§5.2): a field name and a field line value (already
/// without leading and trailing whitespace).
pub struct FieldLine {
    /// the field name
    pub name: Seq<u8>,
    /// the field line value
    pub value: Seq<u8>,
}

/// "set-cookie".
pub open spec fn lit_set_cookie() -> Seq<u8> {
    seq![0x73u8, 0x65, 0x74, 0x2D, 0x63, 0x6F, 0x6F, 0x6B, 0x69, 0x65]
}

/// The field line values of the lines of `section` named `name` (compared
/// case-insensitively, §5.1), in the order received (§5.3: "The order in
/// which field lines with the same name are received is therefore
/// significant").
pub open spec fn field_values_named(section: Seq<FieldLine>, name: Seq<u8>) -> Seq<Seq<u8>>
    decreases section.len()
{
    if section.len() == 0 {
        seq![]
    } else if field_name_eq(section[0].name, name) {
        seq![section[0].value] + field_values_named(section.drop_first(), name)
    } else {
        field_values_named(section.drop_first(), name)
    }
}

/// The values joined into one, in order, "separated by a comma (",") and
/// optional whitespace ... For consistency, use comma SP" (§5.3).
pub open spec fn combine(values: Seq<Seq<u8>>) -> Seq<u8>
    decreases values.len()
{
    if values.len() == 0 {
        seq![]
    } else if values.len() == 1 {
        values[0]
    } else {
        values[0] + seq![0x2Cu8, 0x20u8] + combine(values.drop_first())
    }
}

/// Is `name` `Set-Cookie`? (§5.3's note: it "cannot be combined into a
/// single field value".)
pub open spec fn is_set_cookie(name: Seq<u8>) -> bool {
    field_name_eq(name, lit_set_cookie())
}

/// The combined field value of `name` in `section` (§5.2: "its combined
/// field value consists of the list of corresponding field line values
/// within that section, concatenated in order, with each field line value
/// separated by a comma"). `None` if there is no such line, and for
/// `Set-Cookie`, which is never combined.
pub open spec fn combined_field_value(section: Seq<FieldLine>, name: Seq<u8>) -> Option<Seq<u8>> {
    let values = field_values_named(section, name);
    if is_set_cookie(name) || values.len() == 0 {
        None
    } else {
        Some(combine(values))
    }
}

/// The `Set-Cookie` lines of `section`, each on its own (§5.3's note).
pub open spec fn set_cookie_lines(section: Seq<FieldLine>) -> Seq<Seq<u8>> {
    field_values_named(section, lit_set_cookie())
}

// ===========================================================================
// §5.6.1 lists.
// ===========================================================================

/// Where the list splitter is relative to a `quoted-string` (§5.6.4).
pub enum QState {
    /// outside a quoted string
    Plain,
    /// inside one, after the opening DQUOTE
    Quoted,
    /// inside one, just after a backslash: the next octet is a `quoted-pair`'s
    Escaped,
}

/// The pieces of a comma-separated list (see the modelling choices):
/// `cur` is the piece so far, `acc` the finished pieces, each stripped of
/// OWS. Reads `input` one octet at a time.
pub open spec fn split_scan(input: Seq<u8>, state: QState, cur: Seq<u8>, acc: Seq<Seq<u8>>) -> Seq<Seq<u8>>
    decreases input.len()
{
    if input.len() == 0 {
        // The last piece ends with the input.
        acc.push(strip_ows(cur))
    } else {
        let c = input[0];
        let rest = input.drop_first();
        match state {
            QState::Plain => {
                if c == 0x2C {
                    // "," separates elements (§5.6.1: "each separated by a
                    // single comma (",") and optional whitespace").
                    split_scan(rest, QState::Plain, seq![], acc.push(strip_ows(cur)))
                } else if c == 0x22 {
                    // DQUOTE starts a quoted-string (§5.6.4).
                    split_scan(rest, QState::Quoted, cur.push(c), acc)
                } else {
                    split_scan(rest, QState::Plain, cur.push(c), acc)
                }
            },
            QState::Quoted => {
                if c == 0x5C {
                    // "\" starts a quoted-pair.
                    split_scan(rest, QState::Escaped, cur.push(c), acc)
                } else if c == 0x22 {
                    // The closing DQUOTE.
                    split_scan(rest, QState::Plain, cur.push(c), acc)
                } else {
                    split_scan(rest, QState::Quoted, cur.push(c), acc)
                }
            },
            // The octet after the backslash, whatever it is.
            QState::Escaped => split_scan(rest, QState::Quoted, cur.push(c), acc),
        }
    }
}

/// All the pieces of the comma-separated list `input`, empty ones
/// included, each stripped of OWS. Always at least one.
pub open spec fn split_values(input: Seq<u8>) -> Seq<Seq<u8>> {
    split_scan(input, QState::Plain, seq![], seq![])
}

/// `v` without its empty members.
pub open spec fn drop_empty(v: Seq<Seq<u8>>) -> Seq<Seq<u8>>
    decreases v.len()
{
    if v.len() == 0 {
        seq![]
    } else if v[0].len() == 0 {
        drop_empty(v.drop_first())
    } else {
        seq![v[0]] + drop_empty(v.drop_first())
    }
}

/// The elements of `#element` (§5.6.1.2): "Empty elements do not
/// contribute to the count of elements present. A recipient MUST parse and
/// ignore a reasonable number of empty list elements ... a recipient MUST
/// accept lists that satisfy the following syntax: `#element => [ element ]
/// *( OWS "," OWS [ element ] )`". The pieces are not yet checked against
/// the element's grammar.
pub open spec fn list_elements(input: Seq<u8>) -> Seq<Seq<u8>> {
    drop_empty(split_values(input))
}

/// Every member of `v` is a token.
pub open spec fn all_tokens(v: Seq<Seq<u8>>) -> bool
    decreases v.len()
{
    v.len() == 0 || (is_token(v[0]) && all_tokens(v.drop_first()))
}

// ===========================================================================
// §5.6.4 quoted strings.
// ===========================================================================

/// §5.6.4, the body of a `quoted-string` after its opening DQUOTE:
/// `*( qdtext / quoted-pair ) DQUOTE`. `value` is what has been read so
/// far, with each `quoted-pair` "replaced by the octet following the
/// backslash". Returns the value and what follows the closing DQUOTE, or
/// `None` if `input` does not hold one.
pub open spec fn quoted_body(input: Seq<u8>, value: Seq<u8>) -> Option<(Seq<u8>, Seq<u8>)>
    decreases input.len()
{
    if input.len() == 0 {
        // No closing DQUOTE.
        None
    } else if input[0] == 0x22 {
        // DQUOTE ends the string.
        Some((value, input.drop_first()))
    } else if input[0] == 0x5C {
        // quoted-pair = "\" ( HTAB / SP / VCHAR / obs-text )
        if input.len() >= 2 && is_quoted_pair_octet(input[1]) {
            quoted_body(input.drop_first().drop_first(), value.push(input[1]))
        } else {
            None
        }
    } else if is_qdtext(input[0]) {
        quoted_body(input.drop_first(), value.push(input[0]))
    } else {
        None
    }
}

/// §5.6.4: `quoted-string = DQUOTE *( qdtext / quoted-pair ) DQUOTE`, read
/// at the start of `input`: its value (unquoted) and what follows it.
pub open spec fn parse_quoted_string(input: Seq<u8>) -> Option<(Seq<u8>, Seq<u8>)> {
    if input.len() > 0 && input[0] == 0x22 {
        quoted_body(input.drop_first(), seq![])
    } else {
        None
    }
}

/// The octets of `v` as they go between the DQUOTEs of a `quoted-string`:
/// "A sender SHOULD NOT generate a quoted-pair in a quoted-string except
/// where necessary to quote DQUOTE and backslash octets occurring within
/// that string" (§5.6.4).
pub open spec fn quote_octets(v: Seq<u8>) -> Seq<u8>
    decreases v.len()
{
    if v.len() == 0 {
        seq![]
    } else if v[0] == 0x22 || v[0] == 0x5C {
        seq![0x5Cu8, v[0]] + quote_octets(v.drop_first())
    } else {
        seq![v[0]] + quote_octets(v.drop_first())
    }
}

/// Can `v` be sent in a `quoted-string`? Every octet must be one a
/// `quoted-pair` can carry (or, equivalently, `qdtext`, DQUOTE or "\").
pub open spec fn is_quotable(v: Seq<u8>) -> bool {
    all_in(v, Class::QuotedPair)
}

/// The `quoted-string` a sender writes for `v` (§5.6.4).
pub open spec fn quote(v: Seq<u8>) -> Seq<u8> {
    seq![0x22u8] + quote_octets(v) + seq![0x22u8]
}

// ===========================================================================
// §5.6.6 parameters, §10.1.4 transfer-parameter.
// ===========================================================================

/// A parameter (§5.6.6): a name and a value (unquoted).
pub struct Parameter {
    /// `parameter-name`, as received
    pub name: Seq<u8>,
    /// `parameter-value`, with a `quoted-string` unquoted
    pub value: Seq<u8>,
}

/// Which production reads the parameters.
pub enum ParameterGrammar {
    /// §5.6.6: `parameters = *( OWS ";" OWS [ parameter ] )`, `parameter =
    /// parameter-name "=" parameter-value`.
    Parameters,
    /// §10.1.4: `*( OWS ";" OWS transfer-parameter )`, `transfer-parameter
    /// = token BWS "=" BWS ( token / quoted-string )`.
    TransferCoding,
}

/// `parameter-value = ( token / quoted-string )` (§5.6.6), read at the
/// start of `input`: the value and what follows it.
pub open spec fn parse_parameter_value(input: Seq<u8>) -> Option<(Seq<u8>, Seq<u8>)> {
    if input.len() > 0 && input[0] == 0x22 {
        parse_quoted_string(input)
    } else {
        let n = run_len(Class::Tchar, input);
        if n > 0 {
            Some((input.take(n as int), input.skip(n as int)))
        } else {
            None
        }
    }
}

/// One parameter at the start of `input` (§5.6.6 `parameter` or §10.1.4
/// `transfer-parameter`): the parameter and what follows it.
pub open spec fn parse_parameter(input: Seq<u8>, grammar: ParameterGrammar) -> Option<(Parameter, Seq<u8>)> {
    // parameter-name = token
    let n = run_len(Class::Tchar, input);
    if n == 0 {
        None
    } else {
        let name = input.take(n as int);
        let after_name = input.skip(n as int);
        // `BWS` before "=" in a transfer-parameter only.
        let before_equals = match grammar {
            ParameterGrammar::Parameters => after_name,
            ParameterGrammar::TransferCoding => strip_leading_ows(after_name),
        };
        if before_equals.len() > 0 && before_equals[0] == 0x3D {
            // `BWS` after "=" in a transfer-parameter only.
            let after_equals = match grammar {
                ParameterGrammar::Parameters => before_equals.drop_first(),
                ParameterGrammar::TransferCoding => strip_leading_ows(before_equals.drop_first()),
            };
            match parse_parameter_value(after_equals) {
                Some((value, rest)) => Some((Parameter { name: name, value: value }, rest)),
                None => None,
            }
        } else {
            None
        }
    }
}

/// Is a parameter present after `OWS ";" OWS` (whose rest is `input`)?
/// §5.6.6 makes it optional (`[ parameter ]`): it is there exactly when a
/// `tchar` comes next, since otherwise the repetition can only go on with
/// `OWS ";"` or end. §10.1.4 requires one.
pub open spec fn parameter_present(input: Seq<u8>, grammar: ParameterGrammar) -> bool {
    match grammar {
        ParameterGrammar::Parameters => input.len() > 0 && is_tchar(input[0]),
        ParameterGrammar::TransferCoding => true,
    }
}

/// The repetition `*( OWS ";" OWS ... )` over all of `input`, with the
/// parameters read so far in `acc`. `None` if `input` does not match.
pub open spec fn parameters_loop(input: Seq<u8>, grammar: ParameterGrammar, acc: Seq<Parameter>) -> Option<Seq<Parameter>>
    decreases input.len() via parameters_loop_decreases
{
    if input.len() == 0 {
        // The repetition ends here.
        Some(acc)
    } else {
        // OWS
        let after_ows = strip_leading_ows(input);
        if after_ows.len() == 0 || after_ows[0] != 0x3B {
            // The repetition needs ";" after OWS (so OWS cannot end the string).
            None
        } else {
            // ";" OWS
            let rest = strip_leading_ows(after_ows.drop_first());
            if parameter_present(rest, grammar) {
                match parse_parameter(rest, grammar) {
                    Some((p, after)) => parameters_loop(after, grammar, acc.push(p)),
                    None => None,
                }
            } else {
                parameters_loop(rest, grammar, acc)
            }
        }
    }
}

/// Termination of [`parameters_loop`]: every round consumes the ";".
#[via_fn]
pub proof fn parameters_loop_decreases(input: Seq<u8>, grammar: ParameterGrammar, acc: Seq<Parameter>) {
    if input.len() > 0 {
        super::termination::lemma_run_len_le(Class::Ows, input);
        let after_ows = strip_leading_ows(input);
        if after_ows.len() > 0 && after_ows[0] == 0x3B {
            super::termination::lemma_run_len_le(Class::Ows, after_ows.drop_first());
            let rest = strip_leading_ows(after_ows.drop_first());
            if parameter_present(rest, grammar) {
                super::termination::lemma_parse_parameter_rest(rest, grammar);
            }
        }
    }
}

/// `parameters` (§5.6.6) or the parameters of a `transfer-coding`
/// (§10.1.4) over all of `input`.
pub open spec fn parse_parameters(input: Seq<u8>, grammar: ParameterGrammar) -> Option<Seq<Parameter>> {
    parameters_loop(input, grammar, seq![])
}

// ===========================================================================
// §10.1.4 transfer-coding, RFC 9112 §6.1 Transfer-Encoding, §7.6.1 Connection.
// ===========================================================================

/// A `transfer-coding`: its name (a token, as received) and its parameters.
pub struct TransferCoding {
    /// the coding's name
    pub name: Seq<u8>,
    /// its `transfer-parameter`s
    pub parameters: Seq<Parameter>,
}

/// §10.1.4: `transfer-coding = token *( OWS ";" OWS transfer-parameter )`,
/// over all of `element`.
pub open spec fn parse_transfer_coding(element: Seq<u8>) -> Option<TransferCoding> {
    let n = run_len(Class::Tchar, element);
    if n == 0 {
        None
    } else {
        match parse_parameters(element.skip(n as int), ParameterGrammar::TransferCoding) {
            Some(parameters) => Some(TransferCoding { name: element.take(n as int), parameters: parameters }),
            None => None,
        }
    }
}

/// Every element of `elements` as a transfer coding, or `None` if one is not.
pub open spec fn parse_transfer_codings(elements: Seq<Seq<u8>>) -> Option<Seq<TransferCoding>>
    decreases elements.len()
{
    if elements.len() == 0 {
        Some(seq![])
    } else {
        match (parse_transfer_coding(elements[0]), parse_transfer_codings(elements.drop_first())) {
            (Some(first), Some(rest)) => Some(seq![first] + rest),
            _ => None,
        }
    }
}

/// RFC 9112 §6.1: `Transfer-Encoding = #transfer-coding`, as the combined
/// field value `value` (§5.2). The codings in order, empty list elements
/// dropped (§5.6.1.2); `None` if an element is not a `transfer-coding`.
pub open spec fn parse_transfer_encoding(value: Seq<u8>) -> Option<Seq<TransferCoding>> {
    parse_transfer_codings(list_elements(value))
}

/// §7.6.1: `Connection = #connection-option`, `connection-option = token`,
/// as the combined field value `value`. The options in order, as received
/// (they are case-insensitive: compare with [`field_name_eq`]); `None` if
/// an element is not a token.
pub open spec fn parse_connection(value: Seq<u8>) -> Option<Seq<Seq<u8>>> {
    let options = list_elements(value);
    if all_tokens(options) {
        Some(options)
    } else {
        None
    }
}

// ===========================================================================
// §8.6 Content-Length.
// ===========================================================================

/// `1*DIGIT` (§8.6: `Content-Length = 1*DIGIT`).
pub open spec fn is_digits(s: Seq<u8>) -> bool {
    s.len() > 0 && all_in(s, Class::Digit)
}

/// The number written by the decimal digits `s` (empty is 0).
pub open spec fn decimal_value(s: Seq<u8>) -> nat
    decreases s.len()
{
    if s.len() == 0 {
        0
    } else {
        decimal_value(s.drop_last()) * 10 + ((s.last() - 0x30) as nat)
    }
}

/// Every member of `v` is `e`.
pub open spec fn all_equal(v: Seq<Seq<u8>>, e: Seq<u8>) -> bool
    decreases v.len()
{
    v.len() == 0 || (v[0] == e && all_equal(v.drop_first(), e))
}

/// §8.6, `Content-Length` of the combined field value `value`: "Content-Length
/// = 1*DIGIT", or "a Content-Length header field value consisting of the
/// same decimal value repeated as a comma-separated list (e.g,
/// "Content-Length: 42, 42")", which "MAY either reject the message as
/// invalid or replace that invalid field value with a single instance of
/// the decimal value". We replace it. `None` is invalid.
pub open spec fn parse_content_length(value: Seq<u8>) -> Option<nat> {
    let members = split_values(value);
    if members.len() > 0 && is_digits(members[0]) && all_equal(members, members[0]) {
        Some(decimal_value(members[0]))
    } else {
        None
    }
}

/// `Content-Length` of the field line values of a message's `Content-Length`
/// lines: they are combined (§5.2) and read as above. `None` if there is
/// no line, and if the lines are invalid.
pub open spec fn parse_content_length_lines(lines: Seq<Seq<u8>>) -> Option<nat> {
    if lines.len() == 0 {
        None
    } else {
        parse_content_length(combine(lines))
    }
}

} // verus!
