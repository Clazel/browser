//! A second transcription of the Set-Cookie header field's value, from the
//! server-side grammar of RFC 6265bis §4.1.1 (`set-cookie-string`), and a
//! proof that [`super::spec`]'s user-agent algorithm (§5.6) reads the
//! strings of that grammar as it does (docs/VERIFICATION.md, "Trust without
//! reviewers", item 2).
//!
//! The transcription section was written from the grammar alone, before
//! `spec.rs`, `contract.rs`, `lemmas.rs` or `exec.rs` of this module were
//! read; it uses nothing from them. Only the proof section at the end uses
//! `spec.rs`.
//!
//! Source (pinned as in [`super::spec`]): draft-ietf-httpbis-rfc6265bis-22,
//! 1 December 2025, §4.1.1 Syntax (`set-cookie-string`, `cookie-pair`,
//! `cookie-name`, `cookie-value`, `cookie-octet`, `cookie-av`,
//! `expires-av`, `sane-cookie-date`, `max-age-av`, `domain-av`,
//! `domain-value`, `path-av`, `path-value`, `secure-av`, `httponly-av`,
//! `samesite-av`, `samesite-value`, `extension-av`, `av-octet`) and its
//! prose ("The name of an attribute-value pair is not case-sensitive",
//! "extension-av MUST NOT contain leading or trailing WSP"); `token` from
//! RFC 9110 §5.6.2, `BWS` and `OWS` from §5.6.3, `IMF-fixdate` from §5.6.7
//! (the builders in [`crate::date::independent`]); `subdomain` from RFC 1034
//! §3.5 as enhanced by RFC 1123 §2.1; core rules from RFC 5234 B.1.
//!
//! [`set_cookie_string`] returns `None` for a string that does not match
//! `set-cookie-string`, and otherwise the name, value and attributes the
//! string denotes.
//!
//! What is proven ([`lemma_set_cookie_agrees`], stated by
//! [`set_cookie_agrees`]): for every string `s`, request path and time, if
//! `set_cookie_string(s)` is `Some(c)` and `c` is in the class
//! ([`in_class`]), then `parse_a_set_cookie_string` (§5.6) returns exactly
//! the cookie with `c`'s name and value and, as its attribute list,
//! [`denote_avs`] of `c`'s `cookie-av`s (the list the user agent builds
//! from them, in order). The class ([`in_class`], [`av_in_class`]):
//! - the name and value total at most 4096 octets (§5.6 step 5);
//! - a `Max-Age`, `Domain` or `Path` value is at most 1024 octets (§5.6
//!   step 6), and a `Path` value does not end in white space (the grammar
//!   leaves it in the last `path-value`, and the user agent strips it);
//! - an `Expires` date has a four-digit year of 100 or more (a smaller
//!   one is a two-digit year to §5.1.1 steps 3 and 4), by
//!   [`crate::date::independent::lemma_imf_fixdate_agrees`];
//! - no `extension-av` is, up to white space around its first "=", one of
//!   the seven attribute names in any case. The grammar matches such
//!   strings as `extension-av` (`Max-Age=0`, `Secure=x`, `Domain=.a.b`,
//!   `Expires=garbage`), but the user agent reads them as the attribute.
//!
//! "No attribute repeated" (RFC 6265bis §4.1.1: "servers MUST NOT produce
//! two attributes with the same name") is not needed: both sides keep every
//! attribute, in order, so the equality holds with repeats as well, and
//! covers the strings without them. The user agent accepts far more than the
//! grammar (no `=`, an empty name, `;` runs, control-free but ungrammatical
//! octets, `Max-Age=-1`, a leading "." in `Domain`, ...); the statement says
//! nothing about those. [`lemma_example_pair`] shows the class is not empty.
//!
//! Two representations were fixed after reading `spec.rs`, and say so: the
//! result keeps `Max-Age`'s digits as written (so the 1024-octet limit is a
//! property of the string), and [`denote_av`] is the user agent's reading
//! of each production (§5.6.1 to §5.6.7), written for the values the
//! grammar allows. The grammar transcription itself was not changed.
//!
//! Modelling choices:
//! - A string is a `Seq<u8>`. A `;` is not a `cookie-octet`, an `av-octet`,
//!   a `tchar` or a character of any other production, so the grammar's
//!   `;` separators are exactly the `;` octets: the string is split at
//!   every `;`, and each piece is one `cookie-pair` or `cookie-av` with its
//!   surrounding `BWS` and `OWS`.
//! - `BWS` and `OWS` are the same, `*( SP / HTAB )`. Before a `;` it is
//!   removed from the end of its piece, and after one (or at the start) from
//!   the start of it. The last piece has no `BWS` after it.
//! - The grammar is ambiguous in four places, and this reading settles each
//!   one: (1) `BWS` is taken as long as possible, so a `path-value` or an
//!   `extension-av` does not end in white space before a `;` (RFC 6265bis
//!   forbids that for `extension-av`; for the last piece there is no `BWS`
//!   to take it, and the white space stays in the value); (2) a piece
//!   that matches a named production (`expires-av`, ..., `samesite-av`)
//!   is read as that production, and as an `extension-av` only if it does
//!   not match any; (3) attribute names are case-insensitive, as the prose
//!   says (the ABNF strings are; `%s` is not used); (4) a `cookie-value`
//!   in `DQUOTE`s keeps them.
//! - `domain-value` is `subdomain`: labels of letters, digits and hyphens
//!   that start and end with a letter or a digit, joined by ".". RFC 1034's
//!   63-octet limit on a label is a remark ("must be 63 characters or less")
//!   and is not transcribed.
//! - `sane-cookie-date` is `IMF-fixdate`: a value is one when some fields
//!   the production allows build it ([`crate::date::independent`]). Such a
//!   date may be one no calendar has (month 12 is "Dec", but day 99 is
//!   allowed by `2DIGIT`).
//! - `Max-Age` is `non-zero-digit *DIGIT`: the result keeps the digits, and
//!   [`number_of`] is the number they denote.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------
// Core rules.
// ---------------------------------------------------------------------

/// RFC 5234 B.1: `ALPHA`.
pub open spec fn g_alpha(c: u8) -> bool {
    (0x41 <= c <= 0x5A) || (0x61 <= c <= 0x7A)
}

/// RFC 5234 B.1: `DIGIT`.
pub open spec fn g_digit(c: u8) -> bool {
    0x30 <= c <= 0x39
}

/// RFC 5234 B.1: `DQUOTE = %x22`.
pub open spec fn g_dquote(c: u8) -> bool {
    c == 0x22
}

/// RFC 9110 §5.6.3: `BWS = OWS`, `OWS = *( SP / HTAB )`: one octet of it.
pub open spec fn g_ows(c: u8) -> bool {
    c == 0x20 || c == 0x09
}

/// RFC 9110 §5.6.2: `tchar = "!" / "#" / "$" / "%" / "&" / "'" / "*" / "+"
/// / "-" / "." / "^" / "_" / "`" / "|" / "~" / DIGIT / ALPHA`.
pub open spec fn g_tchar(c: u8) -> bool {
    c == 0x21 || c == 0x23 || c == 0x24 || c == 0x25 || c == 0x26 || c == 0x27 || c == 0x2A || c == 0x2B
        || c == 0x2D || c == 0x2E || c == 0x5E || c == 0x5F || c == 0x60 || c == 0x7C || c == 0x7E
        || g_digit(c) || g_alpha(c)
}

/// `cookie-octet = %x21 / %x23-2B / %x2D-3A / %x3C-5B / %x5D-7E`.
pub open spec fn g_cookie_octet(c: u8) -> bool {
    c == 0x21 || (0x23 <= c <= 0x2B) || (0x2D <= c <= 0x3A) || (0x3C <= c <= 0x5B) || (0x5D <= c <= 0x7E)
}

/// `av-octet = %x20-3A / %x3C-7E`.
pub open spec fn g_av_octet(c: u8) -> bool {
    (0x20 <= c <= 0x3A) || (0x3C <= c <= 0x7E)
}

/// Every octet of `s` meets `p`.
pub open spec fn all_of(s: Seq<u8>, p: spec_fn(u8) -> bool) -> bool {
    forall|i: int| 0 <= i < s.len() ==> p(#[trigger] s[i])
}

/// The lowercase of an ALPHA octet (and every other octet unchanged); how
/// a case-insensitive ABNF string is compared.
pub open spec fn lower(c: u8) -> u8 {
    if 0x41 <= c <= 0x5A { (c + 0x20) as u8 } else { c }
}

/// `s` is the string `lit` in any case. `lit` is given in lower case.
pub open spec fn is_ci(s: Seq<u8>, lit: Seq<u8>) -> bool {
    s.len() == lit.len() && forall|i: int| 0 <= i < s.len() ==> lower(#[trigger] s[i]) == lit[i]
}

/// `s` without the `BWS` at its start.
pub open spec fn skip_bws(s: Seq<u8>) -> Seq<u8>
    decreases s.len()
{
    if s.len() > 0 && g_ows(s[0]) { skip_bws(s.skip(1)) } else { s }
}

/// `s` without the `BWS` at its end.
pub open spec fn trim_bws_end(s: Seq<u8>) -> Seq<u8>
    decreases s.len()
{
    if s.len() > 0 && g_ows(s[s.len() - 1]) { trim_bws_end(s.drop_last()) } else { s }
}

/// The number `non-zero-digit *DIGIT` (any digits) denotes.
pub open spec fn number_of(s: Seq<u8>) -> nat
    decreases s.len()
{
    if s.len() == 0 { 0 } else { number_of(s.drop_last()) * 10 + ((s[s.len() - 1] - 0x30) as nat) }
}

/// The length of the longest run of `tchar` at the start of `s`.
pub open spec fn token_len(s: Seq<u8>) -> nat
    decreases s.len()
{
    if s.len() > 0 && g_tchar(s[0]) { 1 + token_len(s.skip(1)) } else { 0 }
}

// ---------------------------------------------------------------------
// §4.1.1: cookie-pair.
// ---------------------------------------------------------------------

/// `cookie-value = *cookie-octet / ( DQUOTE *cookie-octet DQUOTE )`
pub open spec fn is_cookie_value(v: Seq<u8>) -> bool {
    all_of(v, |c: u8| g_cookie_octet(c))
        || (v.len() >= 2 && g_dquote(v[0]) && g_dquote(v[v.len() - 1])
            && all_of(v.subrange(1, v.len() - 1), |c: u8| g_cookie_octet(c)))
}

/// `cookie-pair = cookie-name BWS "=" BWS cookie-value`, with
/// `cookie-name = token = 1*tchar`: the name and the value.
pub open spec fn cookie_pair(s: Seq<u8>) -> Option<(Seq<u8>, Seq<u8>)> {
    let n = token_len(s);
    let after_name = skip_bws(s.skip(n as int));
    if n >= 1 && after_name.len() > 0 && after_name[0] == 0x3D {
        let value = skip_bws(after_name.skip(1));
        if is_cookie_value(value) { Some((s.take(n as int), value)) } else { None }
    } else {
        None
    }
}

// ---------------------------------------------------------------------
// §4.1.1: cookie-av.
// ---------------------------------------------------------------------

/// `samesite-value = "Strict" / "Lax" / "None"`.
pub enum ServerSameSite {
    /// "Strict".
    Strict,
    /// "Lax".
    Lax,
    /// "None".
    None,
}

/// A `cookie-av`.
pub enum ServerAv {
    /// `expires-av`: the `sane-cookie-date`, as written.
    Expires(Seq<u8>),
    /// `max-age-av`: the digits, as written.
    MaxAge(Seq<u8>),
    /// `domain-av`: the `domain-value`, as written.
    Domain(Seq<u8>),
    /// `path-av`: the `path-value`, as written.
    Path(Seq<u8>),
    /// `secure-av`.
    Secure,
    /// `httponly-av`.
    HttpOnly,
    /// `samesite-av`.
    SameSite(ServerSameSite),
    /// `extension-av`: as written.
    Extension(Seq<u8>),
}

/// `sane-cookie-date = IMF-fixdate`: a string the production builds from
/// some fields it allows.
pub open spec fn is_sane_cookie_date(v: Seq<u8>) -> bool {
    exists|f: crate::date::independent::HttpDateFields|
        crate::date::independent::fields_allowed(f) && #[trigger] crate::date::independent::imf_fixdate(f) == v
}

/// `domain-value = subdomain`, `subdomain = label *( "." label )`,
/// `label = let-dig [ [ ldh-str ] let-dig ]`: letters, digits, hyphens and
/// ".", where every label (a maximal run between "."s, or an end of the
/// string) is non-empty and starts and ends with a letter or digit; that is,
/// the string starts and ends with one, and so do the neighbours of every
/// ".".
pub open spec fn is_subdomain(s: Seq<u8>) -> bool {
    s.len() >= 1 && is_let_dig(s[0]) && is_let_dig(s[s.len() - 1])
        && (forall|i: int| 0 <= i < s.len() ==> (is_let_dig(#[trigger] s[i]) || s[i] == 0x2D || s[i] == 0x2E))
        && (forall|i: int| 0 < i < s.len() - 1 && #[trigger] s[i] == 0x2E ==> is_let_dig(s[i - 1]) && is_let_dig(s[i + 1]))
}

/// `let-dig = letter / digit` (RFC 1123 §2.1 allows a digit first).
pub open spec fn is_let_dig(c: u8) -> bool {
    g_alpha(c) || g_digit(c)
}

/// `piece` is `name BWS "=" BWS value`, `name` being the string in lower
/// case, case-insensitively: the value.
pub open spec fn av_value(piece: Seq<u8>, name: Seq<u8>) -> Option<Seq<u8>> {
    if piece.len() >= name.len() && is_ci(piece.take(name.len() as int), name) {
        let after_name = skip_bws(piece.skip(name.len() as int));
        if after_name.len() > 0 && after_name[0] == 0x3D { Some(skip_bws(after_name.skip(1))) } else { None }
    } else {
        None
    }
}

/// The attribute names, in lower case.
pub open spec fn name_expires() -> Seq<u8> {
    seq![0x65u8, 0x78, 0x70, 0x69, 0x72, 0x65, 0x73]
}

/// "max-age".
pub open spec fn name_max_age() -> Seq<u8> {
    seq![0x6Du8, 0x61, 0x78, 0x2D, 0x61, 0x67, 0x65]
}

/// "domain".
pub open spec fn name_domain() -> Seq<u8> {
    seq![0x64u8, 0x6F, 0x6D, 0x61, 0x69, 0x6E]
}

/// "path".
pub open spec fn name_path() -> Seq<u8> {
    seq![0x70u8, 0x61, 0x74, 0x68]
}

/// "secure".
pub open spec fn name_secure() -> Seq<u8> {
    seq![0x73u8, 0x65, 0x63, 0x75, 0x72, 0x65]
}

/// "httponly".
pub open spec fn name_httponly() -> Seq<u8> {
    seq![0x68u8, 0x74, 0x74, 0x70, 0x6F, 0x6E, 0x6C, 0x79]
}

/// "samesite".
pub open spec fn name_samesite() -> Seq<u8> {
    seq![0x73u8, 0x61, 0x6D, 0x65, 0x73, 0x69, 0x74, 0x65]
}

/// `max-age-av`'s value: `non-zero-digit *DIGIT`.
pub open spec fn is_max_age_value(v: Seq<u8>) -> bool {
    v.len() >= 1 && 0x31 <= v[0] <= 0x39 && all_of(v, |c: u8| g_digit(c))
}

/// `samesite-value`, case-insensitively.
pub open spec fn samesite_value(v: Seq<u8>) -> Option<ServerSameSite> {
    if is_ci(v, seq![0x73u8, 0x74, 0x72, 0x69, 0x63, 0x74]) { Some(ServerSameSite::Strict) }
    else if is_ci(v, seq![0x6Cu8, 0x61, 0x78]) { Some(ServerSameSite::Lax) }
    else if is_ci(v, seq![0x6Eu8, 0x6F, 0x6E, 0x65]) { Some(ServerSameSite::None) }
    else { None }
}

/// `cookie-av` on a piece without its `OWS` and `BWS`: the production it
/// matches (a named one in preference to `extension-av`), or `None`.
pub open spec fn cookie_av(piece: Seq<u8>) -> Option<ServerAv> {
    if is_ci(piece, name_secure()) {
        Some(ServerAv::Secure)
    } else if is_ci(piece, name_httponly()) {
        Some(ServerAv::HttpOnly)
    } else if av_value(piece, name_expires()) matches Some(v) && is_sane_cookie_date(v) {
        Some(ServerAv::Expires(av_value(piece, name_expires()).unwrap()))
    } else if av_value(piece, name_max_age()) matches Some(v) && is_max_age_value(v) {
        Some(ServerAv::MaxAge(av_value(piece, name_max_age()).unwrap()))
    } else if av_value(piece, name_domain()) matches Some(v) && is_subdomain(v) {
        Some(ServerAv::Domain(av_value(piece, name_domain()).unwrap()))
    } else if av_value(piece, name_path()) matches Some(v) && all_of(v, |c: u8| g_av_octet(c)) {
        Some(ServerAv::Path(av_value(piece, name_path()).unwrap()))
    } else if av_value(piece, name_samesite()) matches Some(v) && samesite_value(v) is Some {
        Some(ServerAv::SameSite(samesite_value(av_value(piece, name_samesite()).unwrap()).unwrap()))
    } else if piece.len() >= 1 && all_of(piece, |c: u8| g_av_octet(c)) {
        Some(ServerAv::Extension(piece))
    } else {
        None
    }
}

// ---------------------------------------------------------------------
// §4.1.1: set-cookie-string.
// ---------------------------------------------------------------------

/// The string split at every `;`, read left to right: `current` is the
/// piece being collected and `done` the pieces so far.
pub open spec fn split_loop(s: Seq<u8>, current: Seq<u8>, done: Seq<Seq<u8>>) -> Seq<Seq<u8>>
    decreases s.len()
{
    if s.len() == 0 {
        done.push(current)
    } else if s[0] == 0x3B {
        split_loop(s.skip(1), seq![], done.push(current))
    } else {
        split_loop(s.skip(1), current.push(s[0]), done)
    }
}

/// The string split at every `;`.
pub open spec fn split_semicolons(s: Seq<u8>) -> Seq<Seq<u8>> {
    split_loop(s, seq![], seq![])
}

/// A piece without the `BWS` or `OWS` around it: before a `;` the `BWS`
/// at its end goes, and the one at its start always does. `last`: it is
/// the last piece, with no `;` after it.
pub open spec fn piece_body(piece: Seq<u8>, last: bool) -> Seq<u8> {
    skip_bws(if last { piece } else { trim_bws_end(piece) })
}

/// What a `set-cookie-string` denotes.
pub struct ServerCookie {
    /// `cookie-name`.
    pub name: Seq<u8>,
    /// `cookie-value`, with its `DQUOTE`s if it has them.
    pub value: Seq<u8>,
    /// The `cookie-av`s, in order.
    pub avs: Seq<ServerAv>,
}

/// The `cookie-av`s of the pieces from `i` on.
pub open spec fn av_list(pieces: Seq<Seq<u8>>, i: nat) -> Option<Seq<ServerAv>>
    decreases pieces.len() - i
{
    if i >= pieces.len() {
        Some(seq![])
    } else {
        match cookie_av(piece_body(pieces[i as int], i + 1 == pieces.len())) {
            None => None,
            Some(av) => match av_list(pieces, i + 1) {
                None => None,
                Some(rest) => Some(seq![av] + rest),
            },
        }
    }
}

/// `set-cookie-string = BWS cookie-pair *( BWS ";" OWS cookie-av )`:
/// what the string denotes, or `None` if it does not match.
pub open spec fn set_cookie_string(s: Seq<u8>) -> Option<ServerCookie> {
    let pieces = split_semicolons(s);
    match cookie_pair(piece_body(pieces[0], pieces.len() == 1)) {
        None => None,
        Some((name, value)) => match av_list(pieces, 1) {
            None => None,
            Some(avs) => Some(ServerCookie { name, value, avs }),
        },
    }
}

// ---------------------------------------------------------------------
// The statement (proof section: from here on `spec.rs` is used).
// ---------------------------------------------------------------------

/// The fields a `sane-cookie-date` string is built from.
pub open spec fn date_fields_of(v: Seq<u8>) -> crate::date::independent::HttpDateFields {
    choose|f: crate::date::independent::HttpDateFields|
        crate::date::independent::fields_allowed(f) && #[trigger] crate::date::independent::imf_fixdate(f) == v
}

/// What the user agent's algorithm makes of a `cookie-av` the grammar
/// produced (§5.6.1 to §5.6.7), written for the values the grammar allows:
/// `None` is "ignore the cookie-av". An `Expires` whose fields denote no
/// date is ignored (§5.6.1 step 2); one that does is limited to `now` plus
/// the cookie-age-limit (steps 3 and 4). A `Max-Age` starts with a non-zero
/// digit, so its delta-seconds is positive (§5.6.2 step 7). A `Domain` has
/// no leading "." and is lower-cased (§5.6.3). A `Path` that does not start
/// with "/" is replaced by the default-path (§5.6.4). An `extension-av` is
/// an unrecognized attribute (§5.6 step 7).
pub open spec fn denote_av(av: ServerAv, uri_path: Seq<u8>, now: int) -> Option<Attribute> {
    match av {
        ServerAv::Expires(v) => {
            let f = date_fields_of(v);
            if crate::date::independent::denotes_cookie_date(f.year, f.month, f.day, f.hour, f.minute, f.second) {
                let instant = crate::date::spec::seconds_since_1601(crate::date::independent::date_of(f.year, f));
                let limit = now + cookie_age_limit();
                Some(Attribute::Expires(if instant > limit { limit } else { instant }))
            } else {
                None
            }
        },
        ServerAv::MaxAge(v) => {
            let delta = number_of(v) as int;
            Some(Attribute::MaxAge(now + (if delta < cookie_age_limit() { delta } else { cookie_age_limit() })))
        },
        ServerAv::Domain(v) => Some(Attribute::Domain(crate::ascii::ascii_lowercase(v))),
        ServerAv::Path(v) => Some(
            Attribute::Path(if v.len() > 0 && v[0] == 0x2F { v } else { crate::matching::spec::default_path(uri_path) }),
        ),
        ServerAv::Secure => Some(Attribute::Secure),
        ServerAv::HttpOnly => Some(Attribute::HttpOnly),
        ServerAv::SameSite(x) => Some(
            Attribute::SameSite(match x {
                ServerSameSite::Strict => SameSite::Strict,
                ServerSameSite::Lax => SameSite::Lax,
                ServerSameSite::None => SameSite::None,
            }),
        ),
        ServerAv::Extension(_) => None,
    }
}

/// The attributes the user agent keeps from the `cookie-av`s `avs`, in
/// order.
pub open spec fn denote_avs(avs: Seq<ServerAv>, uri_path: Seq<u8>, now: int) -> Seq<Attribute>
    decreases avs.len()
{
    if avs.len() == 0 {
        seq![]
    } else {
        let rest = denote_avs(avs.drop_last(), uri_path, now);
        match denote_av(avs[avs.len() - 1], uri_path, now) {
            Some(a) => rest.push(a),
            None => rest,
        }
    }
}

/// The name of an `extension-av` as §5.6 step 4 and 5 find it: the octets
/// before the first "=" (all of them if there is none) without leading or
/// trailing white space.
pub open spec fn extension_name(b: Seq<u8>) -> Seq<u8> {
    crate::ascii::remove_leading_and_trailing_wsp(b.take(crate::ascii::find_octet(b, 0x3D, 0) as int))
}

/// `n` is the name of one of the seven attributes the algorithm
/// recognizes, in any case.
pub open spec fn is_recognized_name(n: Seq<u8>) -> bool {
    is_ci(n, name_expires()) || is_ci(n, name_max_age()) || is_ci(n, name_domain()) || is_ci(n, name_path())
        || is_ci(n, name_secure()) || is_ci(n, name_httponly()) || is_ci(n, name_samesite())
}

/// The class of `cookie-av` the equivalence covers (see
/// [`set_cookie_agrees`]).
pub open spec fn av_in_class(av: ServerAv) -> bool {
    match av {
        // The year is four digits from 100 on (a smaller one is a two-digit
        // year to the user agent, §5.1.1 steps 3 and 4).
        ServerAv::Expires(v) => forall|f: crate::date::independent::HttpDateFields|
            crate::date::independent::fields_allowed(f) && #[trigger] crate::date::independent::imf_fixdate(f) == v
                ==> f.year >= 100,
        // §5.6 step 6: an attribute-value over 1024 octets is ignored.
        ServerAv::MaxAge(v) => v.len() <= 1024,
        ServerAv::Domain(v) => v.len() <= 1024,
        // Also: no white space at the end, which the user agent removes
        // (the grammar leaves it in the last `path-value`).
        ServerAv::Path(v) => v.len() <= 1024 && (v.len() == 0 || !g_ows(v[v.len() - 1])),
        ServerAv::Secure | ServerAv::HttpOnly | ServerAv::SameSite(_) => true,
        // The grammar also allows an `extension-av` the user agent reads as
        // one of the seven (`Max-Age=0`, `Secure=x`, `Expires=garbage`,
        // `Domain=.a.b`): those are outside the class.
        ServerAv::Extension(b) => !is_recognized_name(extension_name(b)),
    }
}

/// The class of `set-cookie-string` the equivalence covers: the name and
/// value total at most 4096 octets (§5.6 step 5) and every `cookie-av` is
/// in [`av_in_class`].
pub open spec fn in_class(c: ServerCookie) -> bool {
    c.name.len() + c.value.len() <= 4096 && forall|i: int| 0 <= i < c.avs.len() ==> av_in_class(#[trigger] c.avs[i])
}

/// Statement of `lemma_set_cookie_agrees`: on every string the grammar
/// matches whose parse is in the class, the user agent's parse (§5.6, for a
/// request to a URL with path `uri_path` at time `now`) has the same name
/// and value, and the attributes the grammar's `cookie-av`s denote.
pub open spec fn set_cookie_agrees(s: Seq<u8>, uri_path: Seq<u8>, now: int) -> bool {
    (set_cookie_string(s) matches Some(c) && in_class(c)) ==> parse_a_set_cookie_string(s, uri_path, now)
        == Some(
        SetCookie {
            name: set_cookie_string(s).unwrap().name,
            value: set_cookie_string(s).unwrap().value,
            attributes: denote_avs(set_cookie_string(s).unwrap().avs, uri_path, now),
        },
    )
}

// ---------------------------------------------------------------------
// Proofs, part 1: generic facts about the helpers.
// ---------------------------------------------------------------------

/// Every octet of `x` is `SP` or `HTAB`.
pub open spec fn all_ws(x: Seq<u8>) -> bool {
    forall|i: int| 0 <= i < x.len() ==> g_ows(#[trigger] x[i])
}

/// No octet of `x` is "=".
pub open spec fn no_equals(x: Seq<u8>) -> bool {
    forall|i: int| 0 <= i < x.len() ==> (#[trigger] x[i]) != 0x3D
}

/// `x` neither starts nor ends with white space.
pub open spec fn trimmed(x: Seq<u8>) -> bool {
    x.len() == 0 || (!g_ows(x[0]) && !g_ows(x[x.len() - 1]))
}

/// A search from `k` finds what a search from 0 in the rest finds.
proof fn lemma_find_shift(s: Seq<u8>, c: u8, k: nat, j: nat)
    requires
        k <= s.len(),
    ensures
        crate::ascii::find_octet(s, c, k + j) == k + crate::ascii::find_octet(s.skip(k as int), c, j),
    decreases s.len() - k - j,
{
    let t = s.skip(k as int);
    if k + j < s.len() && s[(k + j) as int] != c {
        assert(t[j as int] == s[(k + j) as int]);
        lemma_find_shift(s, c, k, j + 1);
    } else if k + j < s.len() {
        assert(t[j as int] == s[(k + j) as int]);
    }
}

/// The pieces `split_loop` collects: the ones already `done`, then the
/// split of the rest with `cur` put in front of its first piece.
proof fn lemma_split_loop(t: Seq<u8>, cur: Seq<u8>, done: Seq<Seq<u8>>)
    ensures
        split_semicolons(t).len() >= 1,
        split_loop(t, cur, done) =~= done + seq![cur + split_semicolons(t)[0]] + split_semicolons(t).skip(1),
    decreases t.len(),
{
    if t.len() == 0 {
        assert(split_semicolons(t) =~= seq![Seq::<u8>::empty()]);
    } else if t[0] == 0x3B {
        lemma_split_loop(t.skip(1), seq![], done.push(cur));
        lemma_split_loop(t.skip(1), seq![], seq![seq![]]);
        lemma_split_loop(t.skip(1), seq![], seq![]);
        let p = split_semicolons(t.skip(1));
        assert(split_semicolons(t) =~= seq![Seq::<u8>::empty()] + p);
        assert(seq![Seq::<u8>::empty() + p[0]] + p.skip(1) =~= p);
    } else {
        lemma_split_loop(t.skip(1), cur.push(t[0]), done);
        lemma_split_loop(t.skip(1), seq![t[0]], seq![]);
        lemma_split_loop(t.skip(1), seq![], seq![]);
        let p = split_semicolons(t.skip(1));
        assert(split_semicolons(t) =~= seq![seq![t[0]] + p[0]] + p.skip(1));
        assert(cur + (seq![t[0]] + p[0]) =~= cur.push(t[0]) + p[0]);
    }
}

/// The first piece is what comes before the first ";", and the others are
/// the split of what comes after it.
proof fn lemma_split_head(t: Seq<u8>)
    ensures
        split_semicolons(t).len() >= 1,
        crate::ascii::find_octet(t, 0x3B, 0) == t.len() ==> split_semicolons(t) =~= seq![t],
        crate::ascii::find_octet(t, 0x3B, 0) < t.len() ==> (t[crate::ascii::find_octet(t, 0x3B, 0) as int] == 0x3B
            && split_semicolons(t) =~= seq![t.take(crate::ascii::find_octet(t, 0x3B, 0) as int)]
            + split_semicolons(t.skip(crate::ascii::find_octet(t, 0x3B, 0) as int + 1))),
    decreases t.len(),
{
    lemma_split_loop(t, seq![], seq![]);
    if t.len() == 0 {
        assert(t =~= Seq::<u8>::empty());
        assert(split_loop(t, seq![], seq![]) =~= seq![Seq::<u8>::empty()]);
        assert(split_semicolons(t) =~= seq![t]);
    } else if t[0] == 0x3B {
        lemma_split_loop(t.skip(1), seq![], seq![seq![]]);
        lemma_split_loop(t.skip(1), seq![], seq![]);
        let p = split_semicolons(t.skip(1));
        assert(split_semicolons(t) =~= seq![Seq::<u8>::empty()] + p);
        assert(t.take(0) =~= Seq::<u8>::empty());
    } else {
        lemma_split_head(t.skip(1));
        super::termination::lemma_find_octet_bounds(t.skip(1), 0x3B, 0);
        lemma_find_shift(t, 0x3B, 1, 0);
        lemma_split_loop(t.skip(1), seq![t[0]], seq![]);
        lemma_split_loop(t.skip(1), seq![], seq![]);
        let p = split_semicolons(t.skip(1));
        let j1 = crate::ascii::find_octet(t.skip(1), 0x3B, 0);
        assert(split_semicolons(t) =~= seq![seq![t[0]] + p[0]] + p.skip(1));
        if j1 == t.skip(1).len() {
            assert(p =~= seq![t.skip(1)]);
            assert(seq![t[0]] + t.skip(1) =~= t);
            assert(p.skip(1) =~= Seq::<Seq<u8>>::empty());
            assert(split_semicolons(t) =~= seq![t]);
        } else {
            assert(p =~= seq![t.skip(1).take(j1 as int)] + split_semicolons(t.skip(1).skip(j1 as int + 1)));
            assert(seq![t[0]] + t.skip(1).take(j1 as int) =~= t.take(j1 as int + 1));
            assert(t.skip(1).skip(j1 as int + 1) =~= t.skip(j1 as int + 2));
            assert(split_semicolons(t) =~= seq![t.take(j1 as int + 1)] + split_semicolons(t.skip(j1 as int + 2)));
        }
    }
}

/// A run of white space has nothing left after the leading white space is
/// removed.
proof fn lemma_lead_all_ws(ws: Seq<u8>)
    requires
        all_ws(ws),
    ensures
        crate::ascii::remove_leading_wsp(ws).len() == 0,
    decreases ws.len(),
{
    if ws.len() > 0 {
        assert(all_ws(ws.skip(1))) by {
            assert forall|i: int| 0 <= i < ws.skip(1).len() implies g_ows(#[trigger] ws.skip(1)[i]) by {
                assert(ws.skip(1)[i] == ws[i + 1]);
            }
        }
        lemma_lead_all_ws(ws.skip(1));
    }
}

/// White space in front is removed.
proof fn lemma_lead_ws(ws: Seq<u8>, x: Seq<u8>)
    requires
        all_ws(ws),
    ensures
        crate::ascii::remove_leading_wsp(ws + x) == crate::ascii::remove_leading_wsp(x),
    decreases ws.len(),
{
    if ws.len() == 0 {
        assert(ws + x =~= x);
    } else {
        assert(all_ws(ws.skip(1))) by {
            assert forall|i: int| 0 <= i < ws.skip(1).len() implies g_ows(#[trigger] ws.skip(1)[i]) by {
                assert(ws.skip(1)[i] == ws[i + 1]);
            }
        }
        assert((ws + x)[0] == ws[0]);
        assert((ws + x).skip(1) =~= ws.skip(1) + x);
        lemma_lead_ws(ws.skip(1), x);
    }
}

/// White space at the end is removed.
proof fn lemma_trail_ws(x: Seq<u8>, ws: Seq<u8>)
    requires
        all_ws(ws),
    ensures
        crate::ascii::remove_trailing_wsp(x + ws) == crate::ascii::remove_trailing_wsp(x),
    decreases ws.len(),
{
    if ws.len() == 0 {
        assert(x + ws =~= x);
    } else {
        assert(all_ws(ws.drop_last())) by {
            assert forall|i: int| 0 <= i < ws.drop_last().len() implies g_ows(#[trigger] ws.drop_last()[i]) by {
                assert(ws.drop_last()[i] == ws[i]);
            }
        }
        assert((x + ws)[(x + ws).len() - 1] == ws[ws.len() - 1]);
        assert((x + ws).drop_last() =~= x + ws.drop_last());
        lemma_trail_ws(x, ws.drop_last());
    }
}

/// White space after `x`: what is left of the front-stripped `x + ws`.
proof fn lemma_lead_then(x: Seq<u8>, ws: Seq<u8>)
    requires
        all_ws(ws),
    ensures
        crate::ascii::remove_leading_wsp(x).len() > 0 ==> crate::ascii::remove_leading_wsp(x + ws)
            == crate::ascii::remove_leading_wsp(x) + ws,
        crate::ascii::remove_leading_wsp(x).len() == 0 ==> crate::ascii::remove_leading_wsp(x + ws).len() == 0,
    decreases x.len(),
{
    if x.len() == 0 {
        assert(x + ws =~= ws);
        lemma_lead_all_ws(ws);
    } else if crate::ascii::is_wsp(x[0]) {
        assert((x + ws).skip(1) =~= x.skip(1) + ws);
        assert((x + ws)[0] == x[0]);
        lemma_lead_then(x.skip(1), ws);
    } else {
        assert((x + ws)[0] == x[0]);
    }
}

/// White space around `x` does not change what stripping leaves.
proof fn lemma_strip_pad(ws1: Seq<u8>, x: Seq<u8>, ws2: Seq<u8>)
    requires
        all_ws(ws1),
        all_ws(ws2),
    ensures
        crate::ascii::remove_leading_and_trailing_wsp(ws1 + x + ws2) == crate::ascii::remove_leading_and_trailing_wsp(x),
{
    assert(ws1 + x + ws2 =~= ws1 + (x + ws2));
    lemma_lead_ws(ws1, x + ws2);
    lemma_lead_then(x, ws2);
    let a = crate::ascii::remove_leading_wsp(x);
    if a.len() > 0 {
        lemma_trail_ws(a, ws2);
    } else {
        assert(crate::ascii::remove_leading_wsp(x + ws2) =~= Seq::<u8>::empty());
        assert(a =~= Seq::<u8>::empty());
    }
}

/// A string with no white space at either end is not changed by stripping.
proof fn lemma_strip_trimmed(v: Seq<u8>)
    requires
        trimmed(v),
    ensures
        crate::ascii::remove_leading_and_trailing_wsp(v) == v,
{
}

/// Before the first "=" (when none of the octets in front is one).
proof fn lemma_find_equals_skip(s: Seq<u8>, i: nat, k: nat)
    requires
        i <= k <= s.len(),
        forall|j: int| i <= j < k ==> (#[trigger] s[j]) != 0x3D,
    ensures
        crate::ascii::find_octet(s, 0x3D, i) == crate::ascii::find_octet(s, 0x3D, k),
    decreases k - i,
{
    if i < k {
        lemma_find_equals_skip(s, i + 1, k);
    }
}

/// The first "=" of `a + x` when `a` has none.
proof fn lemma_find_equals_prefix(a: Seq<u8>, x: Seq<u8>)
    requires
        no_equals(a),
    ensures
        crate::ascii::find_octet(a + x, 0x3D, 0) == a.len() + crate::ascii::find_octet(x, 0x3D, 0),
{
    assert forall|j: int| 0 <= j < a.len() implies (#[trigger] (a + x)[j]) != 0x3D by {
        assert((a + x)[j] == a[j]);
    }
    lemma_find_equals_skip(a + x, 0, a.len());
    lemma_find_shift(a + x, 0x3D, a.len(), 0);
    assert((a + x).skip(a.len() as int) =~= x);
}

/// `skip_bws` removes a run of white space and leaves a string that does
/// not start with any.
proof fn lemma_skip_bws(x: Seq<u8>)
    ensures
        skip_bws(x).len() <= x.len(),
        x =~= x.take((x.len() - skip_bws(x).len()) as int) + skip_bws(x),
        all_ws(x.take((x.len() - skip_bws(x).len()) as int)),
        skip_bws(x).len() == 0 || !g_ows(skip_bws(x)[0]),
    decreases x.len(),
{
    if x.len() > 0 && g_ows(x[0]) {
        lemma_skip_bws(x.skip(1));
        let r = skip_bws(x);
        let n = (x.len() - r.len()) as int;
        let w = x.skip(1).take((x.skip(1).len() - r.len()) as int);
        assert(x.take(n) =~= seq![x[0]] + w);
        assert(x.skip(1) =~= w + r);
        assert(x =~= seq![x[0]] + x.skip(1));
        assert(x =~= x.take(n) + r);
        assert forall|i: int| 0 <= i < x.take(n).len() implies g_ows(#[trigger] x.take(n)[i]) by {
            if i > 0 {
                assert(x.take(n)[i] == w[i - 1]);
            }
        }
    } else {
        assert(x.take(0) =~= Seq::<u8>::empty());
        assert(x =~= x.take(0) + x);
    }
}

/// `trim_bws_end` removes a run of white space and leaves a string that does
/// not end with any.
proof fn lemma_trim_bws_end(x: Seq<u8>)
    ensures
        trim_bws_end(x).len() <= x.len(),
        x =~= trim_bws_end(x) + x.skip(trim_bws_end(x).len() as int),
        all_ws(x.skip(trim_bws_end(x).len() as int)),
        trim_bws_end(x).len() == 0 || !g_ows(trim_bws_end(x)[trim_bws_end(x).len() - 1]),
    decreases x.len(),
{
    if x.len() > 0 && g_ows(x[x.len() - 1]) {
        lemma_trim_bws_end(x.drop_last());
        let r = trim_bws_end(x);
        assert(x.skip(r.len() as int) =~= x.drop_last().skip(r.len() as int) + seq![x[x.len() - 1]]);
        assert(x.drop_last() =~= r + x.drop_last().skip(r.len() as int));
        assert(x =~= x.drop_last() + seq![x[x.len() - 1]]);
        assert(x =~= r + x.skip(r.len() as int));
        assert forall|i: int| 0 <= i < x.skip(r.len() as int).len() implies g_ows(#[trigger] x.skip(r.len() as int)[i]) by {
            if i < x.drop_last().skip(r.len() as int).len() {
                assert(x.skip(r.len() as int)[i] == x.drop_last().skip(r.len() as int)[i]);
            }
        }
    } else {
        assert(x.skip(x.len() as int) =~= Seq::<u8>::empty());
        assert(x =~= x + x.skip(x.len() as int));
    }
}

// ---------------------------------------------------------------------
// Proofs, part 2: one piece between semicolons.
// ---------------------------------------------------------------------

/// What §5.6 steps 3 to 7 of the loop make of one cookie-av string: the
/// attribute, or `None` (ignored).
pub open spec fn spec_piece(piece: Seq<u8>, uri_path: Seq<u8>, now: int) -> Option<Attribute> {
    let equals = crate::ascii::find_octet(piece, 0x3D, 0);
    let (attribute_name, attribute_value) = if equals < piece.len() {
        (piece.take(equals as int), piece.skip(equals as int + 1))
    } else {
        (piece, seq![])
    };
    let attribute_name = crate::ascii::remove_leading_and_trailing_wsp(attribute_name);
    let attribute_value = crate::ascii::remove_leading_and_trailing_wsp(attribute_value);
    if attribute_value.len() > 1024 { None } else { process_attribute(attribute_name, attribute_value, uri_path, now) }
}

/// The white space `piece_body` removes before and after.
pub open spec fn body_head(piece: Seq<u8>, last: bool) -> Seq<u8> {
    let t = if last { piece } else { trim_bws_end(piece) };
    t.take((t.len() - skip_bws(t).len()) as int)
}

/// The white space `piece_body` removes after.
pub open spec fn body_tail(piece: Seq<u8>, last: bool) -> Seq<u8> {
    if last { seq![] } else { piece.skip(trim_bws_end(piece).len() as int) }
}

/// A piece is its body with white space around it, and none at the end of
/// the body unless the piece is the last.
proof fn lemma_piece_body(r: Seq<u8>, last: bool)
    ensures
        r =~= body_head(r, last) + piece_body(r, last) + body_tail(r, last),
        all_ws(body_head(r, last)),
        all_ws(body_tail(r, last)),
        piece_body(r, last).len() == 0 || !g_ows(piece_body(r, last)[0]),
        !last ==> (piece_body(r, last).len() == 0 || !g_ows(piece_body(r, last)[piece_body(r, last).len() - 1])),
{
    let t = if last { r } else { trim_bws_end(r) };
    lemma_trim_bws_end(r);
    lemma_skip_bws(t);
    let b = skip_bws(t);
    if last {
        assert(r.skip(r.len() as int) =~= Seq::<u8>::empty());
        assert(r =~= t);
    } else {
        assert(t =~= b || t.len() >= b.len());
    }
    // t = head + b; r = t + tail.
    assert(t =~= body_head(r, last) + b);
    assert(r =~= t + body_tail(r, last));
    assert(b.len() > 0 ==> b[b.len() - 1] == t[t.len() - 1]) by {
        if b.len() > 0 {
            assert(t =~= body_head(r, last) + b);
        }
    }
}

/// `av_value` finds a name, white space, "=", white space and the value.
proof fn lemma_av_value(b: Seq<u8>, name: Seq<u8>)
    requires
        av_value(b, name) is Some,
    ensures
        ({
            let v = av_value(b, name).unwrap();
            let after = skip_bws(b.skip(name.len() as int));
            let w1 = b.skip(name.len() as int).take((b.skip(name.len() as int).len() - after.len()) as int);
            let rest = after.skip(1);
            let w2 = rest.take((rest.len() - v.len()) as int);
            is_ci(b.take(name.len() as int), name) && b =~= b.take(name.len() as int) + (w1 + (seq![0x3Du8] + (w2
                + v))) && all_ws(w1) && all_ws(w2) && (v.len() == 0 || !g_ows(v[0]))
        }),
{
    let n = name.len() as int;
    let after = skip_bws(b.skip(n));
    lemma_skip_bws(b.skip(n));
    let v = av_value(b, name).unwrap();
    assert(v == skip_bws(after.skip(1)));
    lemma_skip_bws(after.skip(1));
    let w1 = b.skip(n).take((b.skip(n).len() - after.len()) as int);
    let rest = after.skip(1);
    let w2 = rest.take((rest.len() - v.len()) as int);
    assert(after =~= seq![0x3Du8] + rest);
    assert(rest =~= w2 + v);
    assert(b.skip(n) =~= w1 + after);
    assert(b =~= b.take(n) + b.skip(n));
}

/// A piece with a name, "=" and a value, and white space around: the
/// attribute-name and attribute-value §5.6 steps 4 and 5 find.
proof fn lemma_spec_piece_value(
    ws1: Seq<u8>,
    name: Seq<u8>,
    w1: Seq<u8>,
    w2: Seq<u8>,
    v: Seq<u8>,
    ws2: Seq<u8>,
    uri_path: Seq<u8>,
    now: int,
)
    requires
        all_ws(ws1),
        all_ws(w1),
        all_ws(w2),
        all_ws(ws2),
        no_equals(name),
        trimmed(name),
        trimmed(v),
    ensures
        spec_piece(ws1 + (name + (w1 + (seq![0x3Du8] + (w2 + v)))) + ws2, uri_path, now) == if v.len() > 1024 {
            None
        } else {
            process_attribute(name, v, uri_path, now)
        },
{
    let a = ws1 + name + w1;
    let rest = w2 + v + ws2;
    let r = ws1 + (name + (w1 + (seq![0x3Du8] + (w2 + v)))) + ws2;
    assert(no_equals(a)) by {
        assert forall|i: int| 0 <= i < a.len() implies (#[trigger] a[i]) != 0x3D by {
            if i < ws1.len() {
                assert(ws1[i] == a[i]);
                assert(g_ows(ws1[i]));
            } else if i < ws1.len() + name.len() {
                assert(name[i - ws1.len()] == a[i]);
            } else {
                assert(w1[i - ws1.len() - name.len()] == a[i]);
                assert(g_ows(a[i]));
            }
        }
    }
    assert(r =~= a + (seq![0x3Du8] + rest));
    lemma_find_equals_prefix(a, seq![0x3Du8] + rest);
    assert((seq![0x3Du8] + rest)[0] == 0x3D);
    assert(crate::ascii::find_octet(seq![0x3Du8] + rest, 0x3D, 0) == 0);
    let e = a.len();
    assert(r.take(e as int) =~= a);
    assert(r.skip(e as int + 1) =~= rest);
    assert(w1 + (seq![0x3Du8] + (w2 + v)) =~= w1 + seq![0x3Du8] + (w2 + v));
    lemma_strip_pad(ws1, name + w1, seq![]);
    assert(a =~= ws1 + (name + w1) + Seq::<u8>::empty());
    lemma_strip_pad(Seq::<u8>::empty(), name, w1);
    assert(name + w1 =~= Seq::<u8>::empty() + name + w1);
    lemma_strip_trimmed(name);
    lemma_strip_pad(w2, v, ws2);
    assert(rest =~= w2 + v + ws2);
    lemma_strip_pad(Seq::<u8>::empty(), v, Seq::<u8>::empty());
    lemma_strip_trimmed(v);
}

/// A piece with no "=": the attribute-name is the whole piece, stripped.
proof fn lemma_spec_piece_bare(ws1: Seq<u8>, b: Seq<u8>, ws2: Seq<u8>, uri_path: Seq<u8>, now: int)
    requires
        all_ws(ws1),
        all_ws(ws2),
        no_equals(b),
    ensures
        spec_piece(ws1 + b + ws2, uri_path, now) == process_attribute(
            crate::ascii::remove_leading_and_trailing_wsp(b),
            seq![],
            uri_path,
            now,
        ),
{
    let r = ws1 + b + ws2;
    assert(no_equals(r)) by {
        assert forall|i: int| 0 <= i < r.len() implies (#[trigger] r[i]) != 0x3D by {
            if i < ws1.len() {
                assert(g_ows(ws1[i]));
            } else if i < ws1.len() + b.len() {
                assert(b[i - ws1.len()] == r[i]);
            } else {
                assert(g_ows(ws2[i - ws1.len() - b.len()]));
            }
        }
    }
    lemma_find_equals_prefix(r, seq![]);
    assert(r + Seq::<u8>::empty() =~= r);
    lemma_strip_pad(ws1, b, ws2);
    assert(crate::ascii::remove_leading_and_trailing_wsp(seq![]) =~= Seq::<u8>::empty());
}

// ---------------------------------------------------------------------
// Proofs, part 3: attribute names and what the algorithm does with them.
// ---------------------------------------------------------------------

/// `is_ci(n, low)` is the spec's case-insensitive match against the
/// mixed-case literal whose lower case is `low`.
proof fn lemma_ci_literal(n: Seq<u8>, lit: Seq<u8>, low: Seq<u8>)
    requires
        crate::ascii::ascii_lowercase(lit) =~= low,
    ensures
        crate::ascii::case_insensitive_match(n, lit) == is_ci(n, low),
{
    let l = crate::ascii::ascii_lowercase(n);
    assert(l.len() == n.len());
    assert forall|i: int| 0 <= i < n.len() implies l[i] == lower(n[i]) by {}
    if is_ci(n, low) {
        assert(l =~= low);
    }
    if l == crate::ascii::ascii_lowercase(lit) {
        assert(is_ci(n, low));
    }
}

/// Two names a string is both in any case are equal.
proof fn lemma_ci_unique(n: Seq<u8>, a: Seq<u8>, b: Seq<u8>)
    requires
        is_ci(n, a),
        is_ci(n, b),
    ensures
        a =~= b,
{
    assert forall|i: int| 0 <= i < a.len() implies a[i] == b[i] by {
        assert(lower(n[i]) == a[i]);
        assert(lower(n[i]) == b[i]);
    }
}

/// The seven names are different.
proof fn lemma_names_differ()
    ensures
        name_expires() != name_max_age(),
        name_expires() != name_domain(),
        name_expires() != name_path(),
        name_expires() != name_secure(),
        name_expires() != name_httponly(),
        name_expires() != name_samesite(),
        name_max_age() != name_domain(),
        name_max_age() != name_path(),
        name_max_age() != name_secure(),
        name_max_age() != name_httponly(),
        name_max_age() != name_samesite(),
        name_domain() != name_path(),
        name_domain() != name_secure(),
        name_domain() != name_httponly(),
        name_domain() != name_samesite(),
        name_path() != name_secure(),
        name_path() != name_httponly(),
        name_path() != name_samesite(),
        name_secure() != name_httponly(),
        name_secure() != name_samesite(),
        name_httponly() != name_samesite(),
{
    assert(name_expires()[0] != name_max_age()[0]);
    assert(name_expires()[0] != name_domain()[0]);
    assert(name_expires()[0] != name_secure()[0]);
    assert(name_max_age()[0] != name_domain()[0]);
    assert(name_max_age()[0] != name_secure()[0]);
    assert(name_domain()[0] != name_secure()[0]);
    assert(name_httponly()[0] != name_samesite()[0]);
}

/// What the spec's `process_attribute` does with a name in any case:
/// the same as the one subsection for it, or nothing for a name it does
/// not recognize.
proof fn lemma_process_attribute(n: Seq<u8>, v: Seq<u8>, uri_path: Seq<u8>, now: int)
    ensures
        is_ci(n, name_expires()) ==> process_attribute(n, v, uri_path, now) == process_expires(v, now),
        is_ci(n, name_max_age()) ==> process_attribute(n, v, uri_path, now) == process_max_age(v, now),
        is_ci(n, name_domain()) ==> process_attribute(n, v, uri_path, now) == process_domain(v),
        is_ci(n, name_path()) ==> process_attribute(n, v, uri_path, now) == process_path(v, uri_path),
        is_ci(n, name_secure()) ==> process_attribute(n, v, uri_path, now) == Some(Attribute::Secure),
        is_ci(n, name_httponly()) ==> process_attribute(n, v, uri_path, now) == Some(Attribute::HttpOnly),
        is_ci(n, name_samesite()) ==> process_attribute(n, v, uri_path, now) == process_same_site(v),
        !is_recognized_name(n) ==> process_attribute(n, v, uri_path, now) is None,
{
    lemma_names_differ();
    lemma_ci_literal(n, lit_expires(), name_expires());
    lemma_ci_literal(n, lit_max_age(), name_max_age());
    lemma_ci_literal(n, lit_domain(), name_domain());
    lemma_ci_literal(n, lit_path(), name_path());
    lemma_ci_literal(n, lit_secure(), name_secure());
    lemma_ci_literal(n, lit_http_only(), name_httponly());
    lemma_ci_literal(n, lit_same_site(), name_samesite());
    if is_ci(n, name_expires()) {
        lemma_ci_unique_all(n, name_expires());
    }
    if is_ci(n, name_max_age()) {
        lemma_ci_unique_all(n, name_max_age());
    }
    if is_ci(n, name_domain()) {
        lemma_ci_unique_all(n, name_domain());
    }
    if is_ci(n, name_path()) {
        lemma_ci_unique_all(n, name_path());
    }
    if is_ci(n, name_secure()) {
        lemma_ci_unique_all(n, name_secure());
    }
    if is_ci(n, name_httponly()) {
        lemma_ci_unique_all(n, name_httponly());
    }
    if is_ci(n, name_samesite()) {
        lemma_ci_unique_all(n, name_samesite());
    }
}

/// A string that is a name in any case is none of the other six.
proof fn lemma_ci_unique_all(n: Seq<u8>, a: Seq<u8>)
    requires
        is_ci(n, a),
    ensures
        is_ci(n, name_expires()) ==> a =~= name_expires(),
        is_ci(n, name_max_age()) ==> a =~= name_max_age(),
        is_ci(n, name_domain()) ==> a =~= name_domain(),
        is_ci(n, name_path()) ==> a =~= name_path(),
        is_ci(n, name_secure()) ==> a =~= name_secure(),
        is_ci(n, name_httponly()) ==> a =~= name_httponly(),
        is_ci(n, name_samesite()) ==> a =~= name_samesite(),
{
    if is_ci(n, name_expires()) { lemma_ci_unique(n, a, name_expires()); }
    if is_ci(n, name_max_age()) { lemma_ci_unique(n, a, name_max_age()); }
    if is_ci(n, name_domain()) { lemma_ci_unique(n, a, name_domain()); }
    if is_ci(n, name_path()) { lemma_ci_unique(n, a, name_path()); }
    if is_ci(n, name_secure()) { lemma_ci_unique(n, a, name_secure()); }
    if is_ci(n, name_httponly()) { lemma_ci_unique(n, a, name_httponly()); }
    if is_ci(n, name_samesite()) { lemma_ci_unique(n, a, name_samesite()); }
}

/// §5.6.1 on an `Expires` the grammar produced is `denote_av`.
proof fn lemma_expires(v: Seq<u8>, uri_path: Seq<u8>, now: int)
    requires
        is_sane_cookie_date(v),
        av_in_class(ServerAv::Expires(v)),
    ensures
        process_expires(v, now) == denote_av(ServerAv::Expires(v), uri_path, now),
{
    assert(exists|f: crate::date::independent::HttpDateFields|
        crate::date::independent::fields_allowed(f) && #[trigger] crate::date::independent::imf_fixdate(f) == v);
    let f = date_fields_of(v);
    assert(crate::date::independent::fields_allowed(f) && crate::date::independent::imf_fixdate(f) == v);
    assert(f.year >= 100);
    crate::date::independent::lemma_imf_fixdate_agrees(f);
}

/// The digits of a number are the same number in the two transcriptions.
proof fn lemma_number_of(v: Seq<u8>)
    ensures
        number_of(v) == crate::ascii::digits_value(v),
    decreases v.len(),
{
    if v.len() > 0 {
        lemma_number_of(v.drop_last());
    }
}

/// A number with a first digit that is not 0 is at least 1.
proof fn lemma_positive(v: Seq<u8>)
    requires
        v.len() >= 1,
        0x31 <= v[0] <= 0x39,
        all_of(v, |c: u8| g_digit(c)),
    ensures
        crate::ascii::digits_value(v) >= 1,
    decreases v.len(),
{
    if v.len() > 1 {
        let t = v.drop_last();
        assert(t[0] == v[0]);
        assert forall|i: int| 0 <= i < t.len() implies g_digit(#[trigger] t[i]) by {
            assert(t[i] == v[i]);
        }
        lemma_positive(t);
    }
}

/// Digits are digits from any index.
proof fn lemma_all_digits_from(v: Seq<u8>, i: nat)
    requires
        all_of(v, |c: u8| g_digit(c)),
    ensures
        all_digits_from(v, i),
    decreases v.len() - i,
{
    if i < v.len() {
        assert(g_digit(v[i as int]));
        lemma_all_digits_from(v, i + 1);
    }
}

/// §5.6.2 on a `Max-Age` the grammar produced is `denote_av`.
proof fn lemma_max_age(v: Seq<u8>, uri_path: Seq<u8>, now: int)
    requires
        is_max_age_value(v),
    ensures
        process_max_age(v, now) == denote_av(ServerAv::MaxAge(v), uri_path, now),
{
    lemma_all_digits_from(v, 1);
    assert(g_digit(v[0]));
    lemma_number_of(v);
    lemma_positive(v);
}

/// §5.6.3 on a `Domain` the grammar produced is `denote_av`.
proof fn lemma_domain(v: Seq<u8>, uri_path: Seq<u8>, now: int)
    requires
        is_subdomain(v),
    ensures
        process_domain(v) == denote_av(ServerAv::Domain(v), uri_path, now),
{
}

/// §5.6.7 on a `SameSite` the grammar produced is `denote_av`.
proof fn lemma_same_site(v: Seq<u8>, x: ServerSameSite, uri_path: Seq<u8>, now: int)
    requires
        samesite_value(v) == Some(x),
    ensures
        process_same_site(v) == denote_av(ServerAv::SameSite(x), uri_path, now),
{
    let strict = seq![0x73u8, 0x74, 0x72, 0x69, 0x63, 0x74];
    let lax = seq![0x6Cu8, 0x61, 0x78];
    let none = seq![0x6Eu8, 0x6F, 0x6E, 0x65];
    assert(crate::ascii::ascii_lowercase(lit_strict()) =~= strict);
    assert(crate::ascii::ascii_lowercase(lit_lax()) =~= lax);
    assert(crate::ascii::ascii_lowercase(lit_none()) =~= none);
    lemma_ci_literal(v, lit_strict(), strict);
    lemma_ci_literal(v, lit_lax(), lax);
    lemma_ci_literal(v, lit_none(), none);
}

/// An IMF-fixdate is 29 octets, starts with a letter and ends with "T".
proof fn lemma_imf_shape(f: crate::date::independent::HttpDateFields)
    requires
        crate::date::independent::fields_allowed(f),
    ensures
        crate::date::independent::imf_fixdate(f).len() == 29,
        !g_ows(crate::date::independent::imf_fixdate(f)[0]),
        !g_ows(crate::date::independent::imf_fixdate(f)[28]),
{
    use crate::date::independent::*;
    let dn = day_name(f.day_name);
    let dd = two_digits(f.day);
    let mon = month_name(f.month);
    let yr = four_digits(f.year);
    let tod = time_of_day(f);
    let g = gmt();
    let sp = seq![0x20u8];
    let cs = seq![0x2Cu8, 0x20];
    assert(dn.len() == 3);
    assert(mon.len() == 3);
    assert(tod.len() == 8);
    let r9 = sp + g;
    let r8 = tod + r9;
    let r7 = sp + r8;
    let r6 = yr + r7;
    let r5 = sp + r6;
    let r4 = mon + r5;
    let r3 = sp + r4;
    let r2 = dd + r3;
    let r1 = cs + r2;
    assert(imf_fixdate(f) == dn + r1);
    assert(imf_fixdate(f)[0] == dn[0]);
    assert(imf_fixdate(f)[28] == 0x54u8);
}

/// The first "=" of `b + tail` is `b`'s, if `b` has one.
proof fn lemma_find_equals_extend(b: Seq<u8>, tail: Seq<u8>, from: nat)
    requires
        crate::ascii::find_octet(b, 0x3D, from) < b.len(),
    ensures
        crate::ascii::find_octet(b + tail, 0x3D, from) == crate::ascii::find_octet(b, 0x3D, from),
    decreases b.len() - from,
{
    if from < b.len() && b[from as int] != 0x3D {
        assert((b + tail)[from as int] == b[from as int]);
        lemma_find_equals_extend(b, tail, from + 1);
    } else {
        assert((b + tail)[from as int] == b[from as int]);
    }
}

/// An octet that is in a name in any case is not "=" and not white space.
proof fn lemma_ci_octets(n: Seq<u8>, name: Seq<u8>)
    requires
        is_ci(n, name),
        forall|i: int| 0 <= i < name.len() ==> (#[trigger] name[i] != 0x3D && !g_ows(name[i])),
    ensures
        no_equals(n),
        trimmed(n),
{
    assert forall|i: int| 0 <= i < n.len() implies (#[trigger] n[i]) != 0x3D by {
        assert(lower(n[i]) == name[i]);
    }
    if n.len() > 0 {
        assert(lower(n[0]) == name[0]);
        assert(lower(n[n.len() - 1]) == name[n.len() - 1]);
    }
}

/// None of the names has "=" or white space in it.
proof fn lemma_name_octets()
    ensures
        forall|i: int| 0 <= i < name_expires().len() ==> (#[trigger] name_expires()[i] != 0x3D && !g_ows(name_expires()[i])),
        forall|i: int| 0 <= i < name_max_age().len() ==> (#[trigger] name_max_age()[i] != 0x3D && !g_ows(name_max_age()[i])),
        forall|i: int| 0 <= i < name_domain().len() ==> (#[trigger] name_domain()[i] != 0x3D && !g_ows(name_domain()[i])),
        forall|i: int| 0 <= i < name_path().len() ==> (#[trigger] name_path()[i] != 0x3D && !g_ows(name_path()[i])),
        forall|i: int| 0 <= i < name_secure().len() ==> (#[trigger] name_secure()[i] != 0x3D && !g_ows(name_secure()[i])),
        forall|i: int| 0 <= i < name_httponly().len() ==> (#[trigger] name_httponly()[i] != 0x3D && !g_ows(name_httponly()[i])),
        forall|i: int| 0 <= i < name_samesite().len() ==> (#[trigger] name_samesite()[i] != 0x3D && !g_ows(name_samesite()[i])),
{
}

/// The three `samesite-value`s have no white space in them.
proof fn lemma_same_site_octets(v: Seq<u8>, x: ServerSameSite)
    requires
        samesite_value(v) == Some(x),
    ensures
        trimmed(v),
        v.len() <= 6,
{
    let strict = seq![0x73u8, 0x74, 0x72, 0x69, 0x63, 0x74];
    let lax = seq![0x6Cu8, 0x61, 0x78];
    let none = seq![0x6Eu8, 0x6F, 0x6E, 0x65];
    if is_ci(v, strict) {
        assert(lower(v[0]) == strict[0]);
        assert(lower(v[5]) == strict[5]);
    } else if is_ci(v, lax) {
        assert(lower(v[0]) == lax[0]);
        assert(lower(v[2]) == lax[2]);
    } else {
        assert(lower(v[0]) == none[0]);
        assert(lower(v[3]) == none[3]);
    }
}

/// A subdomain has a letter or digit at either end.
proof fn lemma_subdomain_trimmed(v: Seq<u8>)
    requires
        is_subdomain(v),
    ensures
        trimmed(v),
        no_equals(v),
{
    assert forall|i: int| 0 <= i < v.len() implies (#[trigger] v[i]) != 0x3D by {
        assert(is_let_dig(v[i]) || v[i] == 0x2D || v[i] == 0x2E);
    }
}

/// An "=" at index `i` is found at `i` or sooner.
proof fn lemma_find_equals_at(b: Seq<u8>, from: nat, i: nat)
    requires
        from <= i < b.len(),
        b[i as int] == 0x3D,
    ensures
        crate::ascii::find_octet(b, 0x3D, from) <= i,
    decreases i - from,
{
    if from < i && b[from as int] != 0x3D {
        lemma_find_equals_at(b, from + 1, i);
    }
}

/// The attribute-value §5.6 step 5 finds in a piece.
pub open spec fn spec_value_of(piece: Seq<u8>) -> Seq<u8> {
    let equals = crate::ascii::find_octet(piece, 0x3D, 0);
    crate::ascii::remove_leading_and_trailing_wsp(
        if equals < piece.len() { piece.skip(equals as int + 1) } else { seq![] },
    )
}

/// A piece whose body is a name, "=" and a value, with the name in any
/// case: the attribute-name and attribute-value the loop finds.
proof fn lemma_named_piece(r: Seq<u8>, last: bool, name: Seq<u8>, uri_path: Seq<u8>, now: int)
    requires
        av_value(piece_body(r, last), name) is Some,
        trimmed(av_value(piece_body(r, last), name).unwrap()),
        forall|i: int| 0 <= i < name.len() ==> (#[trigger] name[i] != 0x3D && !g_ows(name[i])),
    ensures
        is_ci(piece_body(r, last).take(name.len() as int), name),
        spec_piece(r, uri_path, now) == if av_value(piece_body(r, last), name).unwrap().len() > 1024 {
            None
        } else {
            process_attribute(
                piece_body(r, last).take(name.len() as int),
                av_value(piece_body(r, last), name).unwrap(),
                uri_path,
                now,
            )
        },
{
    let b = piece_body(r, last);
    let head = body_head(r, last);
    let tail = body_tail(r, last);
    lemma_piece_body(r, last);
    let v = av_value(b, name).unwrap();
    lemma_av_value(b, name);
    let n = b.take(name.len() as int);
    let after = skip_bws(b.skip(name.len() as int));
    let w1 = b.skip(name.len() as int).take((b.skip(name.len() as int).len() - after.len()) as int);
    let rest = after.skip(1);
    let w2 = rest.take((rest.len() - v.len()) as int);
    lemma_ci_octets(n, name);
    assert(r == head + (n + (w1 + (seq![0x3Du8] + (w2 + v)))) + tail);
    lemma_spec_piece_value(head, n, w1, w2, v, tail, uri_path, now);
}

/// An `extension-av` piece, whose name is not one of the seven.
proof fn lemma_extension_piece(r: Seq<u8>, last: bool, uri_path: Seq<u8>, now: int)
    requires
        piece_body(r, last).len() >= 1,
        !is_recognized_name(extension_name(piece_body(r, last))),
    ensures
        spec_piece(r, uri_path, now) is None,
{
    let b = piece_body(r, last);
    let head = body_head(r, last);
    let tail = body_tail(r, last);
    lemma_piece_body(r, last);
    let j = crate::ascii::find_octet(b, 0x3D, 0);
    super::termination::lemma_find_octet_bounds(b, 0x3D, 0);
    assert(r == head + b + tail);
    assert(no_equals(head)) by {
        assert forall|i: int| 0 <= i < head.len() implies (#[trigger] head[i]) != 0x3D by {
            assert(g_ows(head[i]));
        }
    }
    if j < b.len() {
        lemma_find_equals_extend(b, tail, 0);
        assert(head + b + tail =~= head + (b + tail));
        lemma_find_equals_prefix(head, b + tail);
        let e = head.len() + j;
        assert(r.take(e as int) =~= head + b.take(j as int));
        lemma_strip_pad(head, b.take(j as int), seq![]);
        assert(head + b.take(j as int) =~= head + b.take(j as int) + Seq::<u8>::empty());
        assert(extension_name(b) == crate::ascii::remove_leading_and_trailing_wsp(b.take(j as int)));
    } else {
        assert(no_equals(b)) by {
            assert forall|i: int| 0 <= i < b.len() implies (#[trigger] b[i]) != 0x3D by {
                if b[i] == 0x3D {
                    lemma_find_equals_at(b, 0, i as nat);
                }
            }
        }
        lemma_spec_piece_bare(head, b, tail, uri_path, now);
        assert(b.take(j as int) =~= b);
    }
    lemma_process_attribute(extension_name(b), spec_value_of(r), uri_path, now);
}

/// One piece between semicolons, in the class: the user agent's reading
/// of it is what the grammar's `cookie-av` denotes.
proof fn lemma_piece(r: Seq<u8>, last: bool, av: ServerAv, uri_path: Seq<u8>, now: int)
    requires
        cookie_av(piece_body(r, last)) == Some(av),
        av_in_class(av),
    ensures
        spec_piece(r, uri_path, now) == denote_av(av, uri_path, now),
{
    let b = piece_body(r, last);
    let head = body_head(r, last);
    let tail = body_tail(r, last);
    lemma_piece_body(r, last);
    lemma_name_octets();
    if is_ci(b, name_secure()) {
        lemma_ci_octets(b, name_secure());
        lemma_spec_piece_bare(head, b, tail, uri_path, now);
        lemma_strip_trimmed(b);
        lemma_process_attribute(b, seq![], uri_path, now);
        assert(r == head + b + tail);
    } else if is_ci(b, name_httponly()) {
        lemma_ci_octets(b, name_httponly());
        lemma_spec_piece_bare(head, b, tail, uri_path, now);
        lemma_strip_trimmed(b);
        lemma_process_attribute(b, seq![], uri_path, now);
        assert(r == head + b + tail);
    } else if av_value(b, name_expires()) is Some && is_sane_cookie_date(av_value(b, name_expires()).unwrap()) {
        let v = av_value(b, name_expires()).unwrap();
        assert(exists|f: crate::date::independent::HttpDateFields|
            crate::date::independent::fields_allowed(f) && #[trigger] crate::date::independent::imf_fixdate(f) == v);
        let f = date_fields_of(v);
        lemma_imf_shape(f);
        lemma_named_piece(r, last, name_expires(), uri_path, now);
        let n = b.take(name_expires().len() as int);
        lemma_process_attribute(n, v, uri_path, now);
        lemma_expires(v, uri_path, now);
    } else if av_value(b, name_max_age()) is Some && is_max_age_value(av_value(b, name_max_age()).unwrap()) {
        let v = av_value(b, name_max_age()).unwrap();
        assert(trimmed(v)) by {
            assert(g_digit(v[0]));
            assert(g_digit(v[v.len() - 1]));
        }
        lemma_named_piece(r, last, name_max_age(), uri_path, now);
        let n = b.take(name_max_age().len() as int);
        lemma_process_attribute(n, v, uri_path, now);
        lemma_max_age(v, uri_path, now);
    } else if av_value(b, name_domain()) is Some && is_subdomain(av_value(b, name_domain()).unwrap()) {
        let v = av_value(b, name_domain()).unwrap();
        lemma_subdomain_trimmed(v);
        lemma_named_piece(r, last, name_domain(), uri_path, now);
        let n = b.take(name_domain().len() as int);
        lemma_process_attribute(n, v, uri_path, now);
        lemma_domain(v, uri_path, now);
    } else if av_value(b, name_path()) is Some && all_of(av_value(b, name_path()).unwrap(), |c: u8| g_av_octet(c)) {
        let v = av_value(b, name_path()).unwrap();
        lemma_av_value(b, name_path());
        assert(trimmed(v));
        lemma_named_piece(r, last, name_path(), uri_path, now);
        let n = b.take(name_path().len() as int);
        lemma_process_attribute(n, v, uri_path, now);
    } else if av_value(b, name_samesite()) is Some && samesite_value(av_value(b, name_samesite()).unwrap()) is Some {
        let v = av_value(b, name_samesite()).unwrap();
        let x = samesite_value(v).unwrap();
        lemma_same_site_octets(v, x);
        lemma_named_piece(r, last, name_samesite(), uri_path, now);
        let n = b.take(name_samesite().len() as int);
        lemma_process_attribute(n, v, uri_path, now);
        lemma_same_site(v, x, uri_path, now);
    } else {
        // An extension-av, which is not one of the seven (class).
        assert(av == ServerAv::Extension(b));
        lemma_extension_piece(r, last, uri_path, now);
    }
}

// ---------------------------------------------------------------------
// Proofs, part 4: the loop over the attributes.
// ---------------------------------------------------------------------

/// The attributes §5.6's loop keeps from the pieces `ps`, in order.
pub open spec fn spec_attrs(ps: Seq<Seq<u8>>, uri_path: Seq<u8>, now: int) -> Seq<Attribute>
    decreases ps.len(),
{
    if ps.len() == 0 {
        seq![]
    } else {
        match spec_piece(ps[0], uri_path, now) {
            Some(a) => seq![a] + spec_attrs(ps.skip(1), uri_path, now),
            None => spec_attrs(ps.skip(1), uri_path, now),
        }
    }
}

/// §5.6's loop (steps 1 to 8) is `spec_attrs` of the pieces after the first
/// ";" at `pos`.
proof fn lemma_parse_attributes(s: Seq<u8>, pos: nat, uri_path: Seq<u8>, now: int, list: Seq<Attribute>)
    requires
        pos <= s.len(),
        pos == s.len() || s[pos as int] == 0x3B,
    ensures
        parse_attributes(s, pos, uri_path, now, list) == list + (if pos >= s.len() {
            seq![]
        } else {
            spec_attrs(split_semicolons(s.skip(pos as int + 1)), uri_path, now)
        }),
    decreases s.len() - pos,
{
    if pos < s.len() {
        let t = s.skip(pos as int + 1);
        super::termination::lemma_find_octet_bounds(s, 0x3B, pos + 1);
        lemma_find_shift(s, 0x3B, pos + 1, 0);
        let j = crate::ascii::find_octet(t, 0x3B, 0);
        let end = crate::ascii::find_octet(s, 0x3B, pos + 1);
        assert(end == pos + 1 + j);
        super::termination::lemma_find_octet_bounds(t, 0x3B, 0);
        lemma_split_head(t);
        assert(s.subrange(pos as int + 1, end as int) =~= t.take(j as int));
        let piece = t.take(j as int);
        let ps = split_semicolons(t);
        let after = match spec_piece(piece, uri_path, now) {
            Some(a) => list.push(a),
            None => list,
        };
        // The step 6 check is part of `spec_piece`.
        assert(parse_attributes(s, pos, uri_path, now, list) == parse_attributes(s, end, uri_path, now, after));
        if j == t.len() {
            assert(end == s.len());
            assert(ps =~= seq![t]);
            assert(t.take(j as int) =~= t);
            assert(ps.skip(1) =~= Seq::<Seq<u8>>::empty());
        } else {
            assert(s[end as int] == t[j as int]);
            assert(ps =~= seq![piece] + split_semicolons(t.skip(j as int + 1)));
            assert(t.skip(j as int + 1) =~= s.skip(end as int + 1));
            assert(ps.skip(1) =~= split_semicolons(s.skip(end as int + 1)));
            lemma_parse_attributes(s, end, uri_path, now, after);
        }
        assert(ps[0] == piece);
        match spec_piece(piece, uri_path, now) {
            Some(a) => {
                assert(list.push(a) =~= list + seq![a]);
                assert(spec_attrs(ps, uri_path, now) =~= seq![a] + spec_attrs(ps.skip(1), uri_path, now));
                assert(list + seq![a] + spec_attrs(ps.skip(1), uri_path, now) =~= list + (seq![a]
                    + spec_attrs(ps.skip(1), uri_path, now)));
            },
            None => {
                assert(spec_attrs(ps, uri_path, now) =~= spec_attrs(ps.skip(1), uri_path, now));
            },
        }
    }
}

/// The attributes an optional denotation contributes.
pub open spec fn opt_seq(o: Option<Attribute>) -> Seq<Attribute> {
    match o {
        Some(a) => seq![a],
        None => seq![],
    }
}

/// `denote_avs` appends the last attribute's denotation.
proof fn lemma_denote_avs_last(avs: Seq<ServerAv>, uri_path: Seq<u8>, now: int)
    requires
        avs.len() > 0,
    ensures
        denote_avs(avs, uri_path, now) =~= denote_avs(avs.drop_last(), uri_path, now) + opt_seq(
            denote_av(avs[avs.len() - 1], uri_path, now),
        ),
{
    match denote_av(avs[avs.len() - 1], uri_path, now) {
        Some(a) => {
            assert(denote_avs(avs.drop_last(), uri_path, now).push(a) =~= denote_avs(avs.drop_last(), uri_path, now) + seq![a]);
        },
        None => {
            assert(denote_avs(avs.drop_last(), uri_path, now) + Seq::<Attribute>::empty() =~= denote_avs(avs.drop_last(), uri_path, now));
        },
    }
}

/// `denote_avs` puts the first attribute's denotation first.
proof fn lemma_denote_avs_cons(av: ServerAv, rest: Seq<ServerAv>, uri_path: Seq<u8>, now: int)
    ensures
        denote_avs(seq![av] + rest, uri_path, now) =~= opt_seq(denote_av(av, uri_path, now)) + denote_avs(
            rest,
            uri_path,
            now,
        ),
    decreases rest.len(),
{
    let all = seq![av] + rest;
    let first = opt_seq(denote_av(av, uri_path, now));
    if rest.len() == 0 {
        assert(all.drop_last() =~= Seq::<ServerAv>::empty());
        assert(all =~= seq![av]);
        lemma_denote_avs_last(all, uri_path, now);
        assert(denote_avs(rest, uri_path, now) =~= Seq::<Attribute>::empty());
        assert(first + Seq::<Attribute>::empty() =~= first);
        assert(Seq::<Attribute>::empty() + first =~= first);
    } else {
        assert(all.drop_last() =~= seq![av] + rest.drop_last());
        assert(all[all.len() - 1] == rest[rest.len() - 1]);
        lemma_denote_avs_cons(av, rest.drop_last(), uri_path, now);
        lemma_denote_avs_last(all, uri_path, now);
        lemma_denote_avs_last(rest, uri_path, now);
        let d = denote_avs(rest.drop_last(), uri_path, now);
        let o = opt_seq(denote_av(rest[rest.len() - 1], uri_path, now));
        assert((first + d) + o =~= first + (d + o));
    }
}

/// The attributes the grammar's `cookie-av`s denote are the ones the loop
/// keeps from the pieces they were read from.
proof fn lemma_av_list(ps: Seq<Seq<u8>>, i: nat, avs: Seq<ServerAv>, uri_path: Seq<u8>, now: int)
    requires
        i <= ps.len(),
        av_list(ps, i) == Some(avs),
        forall|k: int| 0 <= k < avs.len() ==> av_in_class(#[trigger] avs[k]),
    ensures
        spec_attrs(ps.skip(i as int), uri_path, now) == denote_avs(avs, uri_path, now),
    decreases ps.len() - i,
{
    if i < ps.len() {
        let rest = av_list(ps, i + 1).unwrap();
        let av = cookie_av(piece_body(ps[i as int], i + 1 == ps.len())).unwrap();
        assert(avs =~= seq![av] + rest);
        assert(av_in_class(avs[0]));
        assert forall|k: int| 0 <= k < rest.len() implies av_in_class(#[trigger] rest[k]) by {
            assert(rest[k] == avs[k + 1]);
        }
        lemma_av_list(ps, i + 1, rest, uri_path, now);
        lemma_piece(ps[i as int], i + 1 == ps.len(), av, uri_path, now);
        lemma_denote_avs_cons(av, rest, uri_path, now);
        let t = ps.skip(i as int);
        assert(t[0] == ps[i as int]);
        assert(t.skip(1) =~= ps.skip(i as int + 1));
        assert(spec_attrs(t, uri_path, now) =~= opt_seq(spec_piece(ps[i as int], uri_path, now)) + spec_attrs(
            t.skip(1),
            uri_path,
            now,
        ));
        assert(Seq::<Attribute>::empty() + spec_attrs(t.skip(1), uri_path, now) =~= spec_attrs(t.skip(1), uri_path, now));
    } else {
        assert(avs =~= Seq::<ServerAv>::empty());
        assert(ps.skip(i as int) =~= Seq::<Seq<u8>>::empty());
    }
}

// ---------------------------------------------------------------------
// Proofs, part 5: the name-value pair, and no control characters.
// ---------------------------------------------------------------------

/// The octets of a `set-cookie-string` are all printable or HTAB, so none
/// is a CTL character excluding HTAB (§5.6 step 1).
pub open spec fn g_ok(c: u8) -> bool {
    c == 0x09 || (0x20 <= c <= 0x7E)
}

/// The run of `tchar`s `token_len` counts.
proof fn lemma_token_len(b: Seq<u8>)
    ensures
        token_len(b) <= b.len(),
        forall|i: int| 0 <= i < token_len(b) ==> g_tchar(#[trigger] b[i]),
    decreases b.len(),
{
    if b.len() > 0 && g_tchar(b[0]) {
        lemma_token_len(b.skip(1));
        assert forall|i: int| 0 <= i < token_len(b) implies g_tchar(#[trigger] b[i]) by {
            if i > 0 {
                assert(b.skip(1)[i - 1] == b[i]);
            }
        }
    }
}

/// A `cookie-pair` is a name, white space, "=", white space and a value.
proof fn lemma_cookie_pair(b: Seq<u8>)
    requires
        cookie_pair(b) is Some,
    ensures
        ({
            let (name, value) = cookie_pair(b).unwrap();
            let n = token_len(b);
            let after = skip_bws(b.skip(n as int));
            let w1 = b.skip(n as int).take((b.skip(n as int).len() - after.len()) as int);
            let rest = after.skip(1);
            let w2 = rest.take((rest.len() - value.len()) as int);
            name.len() >= 1 && all_of(name, |c: u8| g_tchar(c)) && b =~= name + (w1 + (seq![0x3Du8] + (w2 + value)))
                && all_ws(w1) && all_ws(w2) && is_cookie_value(value)
        }),
{
    let (name, value) = cookie_pair(b).unwrap();
    let n = token_len(b);
    lemma_token_len(b);
    let after = skip_bws(b.skip(n as int));
    lemma_skip_bws(b.skip(n as int));
    lemma_skip_bws(after.skip(1));
    let w1 = b.skip(n as int).take((b.skip(n as int).len() - after.len()) as int);
    let rest = after.skip(1);
    let w2 = rest.take((rest.len() - value.len()) as int);
    assert(after =~= seq![0x3Du8] + rest);
    assert(rest =~= w2 + value);
    assert(b.skip(n as int) =~= w1 + after);
    assert(b =~= b.take(n as int) + b.skip(n as int));
    assert forall|i: int| 0 <= i < name.len() implies g_tchar(#[trigger] name[i]) by {
        assert(name[i] == b[i]);
    }
}

/// The name and value §5.6 steps 3 and 4 find in a `cookie-pair` with white
/// space around it.
proof fn lemma_pair_split(
    ws1: Seq<u8>,
    name: Seq<u8>,
    w1: Seq<u8>,
    w2: Seq<u8>,
    value: Seq<u8>,
    ws2: Seq<u8>,
)
    requires
        all_ws(ws1),
        all_ws(w1),
        all_ws(w2),
        all_ws(ws2),
        no_equals(name),
        trimmed(name),
        trimmed(value),
    ensures
        ({
            let r = ws1 + (name + (w1 + (seq![0x3Du8] + (w2 + value)))) + ws2;
            let e = crate::ascii::find_octet(r, 0x3D, 0);
            e < r.len() && crate::ascii::remove_leading_and_trailing_wsp(r.take(e as int)) == name
                && crate::ascii::remove_leading_and_trailing_wsp(r.skip(e as int + 1)) == value
        }),
{
    let a = ws1 + name + w1;
    let rest = w2 + value + ws2;
    let r = ws1 + (name + (w1 + (seq![0x3Du8] + (w2 + value)))) + ws2;
    assert(no_equals(a)) by {
        assert forall|i: int| 0 <= i < a.len() implies (#[trigger] a[i]) != 0x3D by {
            if i < ws1.len() {
                assert(ws1[i] == a[i]);
                assert(g_ows(ws1[i]));
            } else if i < ws1.len() + name.len() {
                assert(name[i - ws1.len()] == a[i]);
            } else {
                assert(w1[i - ws1.len() - name.len()] == a[i]);
                assert(g_ows(a[i]));
            }
        }
    }
    assert(r =~= a + (seq![0x3Du8] + rest));
    lemma_find_equals_prefix(a, seq![0x3Du8] + rest);
    assert((seq![0x3Du8] + rest)[0] == 0x3D);
    assert(crate::ascii::find_octet(seq![0x3Du8] + rest, 0x3D, 0) == 0);
    let e = a.len();
    assert(r.take(e as int) =~= a);
    assert(r.skip(e as int + 1) =~= rest);
    assert(a =~= ws1 + (name + w1) + Seq::<u8>::empty());
    lemma_strip_pad(ws1, name + w1, seq![]);
    assert(name + w1 =~= Seq::<u8>::empty() + name + w1);
    lemma_strip_pad(Seq::<u8>::empty(), name, w1);
    lemma_strip_trimmed(name);
    lemma_strip_pad(w2, value, ws2);
    lemma_strip_pad(Seq::<u8>::empty(), value, Seq::<u8>::empty());
    lemma_strip_trimmed(value);
}

/// `all_of` over a concatenation.
proof fn lemma_ok_concat(a: Seq<u8>, b: Seq<u8>)
    requires
        all_of(a, |c: u8| g_ok(c)),
        all_of(b, |c: u8| g_ok(c)),
    ensures
        all_of(a + b, |c: u8| g_ok(c)),
{
    assert forall|i: int| 0 <= i < (a + b).len() implies g_ok(#[trigger] (a + b)[i]) by {
        if i < a.len() {
            assert((a + b)[i] == a[i]);
        } else {
            assert((a + b)[i] == b[i - a.len()]);
        }
    }
}

/// A string in any case of a printable one is printable.
proof fn lemma_ci_ok(n: Seq<u8>, name: Seq<u8>)
    requires
        is_ci(n, name),
        all_of(name, |c: u8| g_ok(c)),
    ensures
        all_of(n, |c: u8| g_ok(c)),
{
    assert forall|i: int| 0 <= i < n.len() implies g_ok(#[trigger] n[i]) by {
        assert(lower(n[i]) == name[i]);
        assert(g_ok(name[i]));
    }
}

/// The seven names and the three `samesite-value`s are printable.
proof fn lemma_names_ok()
    ensures
        all_of(name_expires(), |c: u8| g_ok(c)),
        all_of(name_max_age(), |c: u8| g_ok(c)),
        all_of(name_domain(), |c: u8| g_ok(c)),
        all_of(name_path(), |c: u8| g_ok(c)),
        all_of(name_secure(), |c: u8| g_ok(c)),
        all_of(name_httponly(), |c: u8| g_ok(c)),
        all_of(name_samesite(), |c: u8| g_ok(c)),
        all_of(seq![0x73u8, 0x74, 0x72, 0x69, 0x63, 0x74], |c: u8| g_ok(c)),
        all_of(seq![0x6Cu8, 0x61, 0x78], |c: u8| g_ok(c)),
        all_of(seq![0x6Eu8, 0x6F, 0x6E, 0x65], |c: u8| g_ok(c)),
{
}

/// Everything an IMF-fixdate is made of is printable.
proof fn lemma_imf_ok(f: crate::date::independent::HttpDateFields)
    requires
        crate::date::independent::fields_allowed(f),
    ensures
        all_of(crate::date::independent::imf_fixdate(f), |c: u8| g_ok(c)),
{
    use crate::date::independent::*;
    let dn = day_name(f.day_name);
    let dd = two_digits(f.day);
    let mon = month_name(f.month);
    let yr = four_digits(f.year);
    let tod = time_of_day(f);
    let g = gmt();
    let sp = seq![0x20u8];
    let cs = seq![0x2Cu8, 0x20];
    let colon = seq![0x3Au8];
    let (h, m, sec) = (two_digits(f.hour), two_digits(f.minute), two_digits(f.second));
    assert(all_of(dn, |c: u8| g_ok(c)));
    assert(all_of(mon, |c: u8| g_ok(c)));
    assert(all_of(g, |c: u8| g_ok(c)));
    assert(all_of(sp, |c: u8| g_ok(c)));
    assert(all_of(cs, |c: u8| g_ok(c)));
    assert(all_of(colon, |c: u8| g_ok(c)));
    assert(all_of(dd, |c: u8| g_ok(c))) by {
        assert forall|k: int| 0 <= k < dd.len() implies g_ok(#[trigger] dd[k]) by {}
    }
    assert(all_of(h, |c: u8| g_ok(c))) by {
        assert forall|k: int| 0 <= k < h.len() implies g_ok(#[trigger] h[k]) by {}
    }
    assert(all_of(m, |c: u8| g_ok(c))) by {
        assert forall|k: int| 0 <= k < m.len() implies g_ok(#[trigger] m[k]) by {}
    }
    assert(all_of(sec, |c: u8| g_ok(c))) by {
        assert forall|k: int| 0 <= k < sec.len() implies g_ok(#[trigger] sec[k]) by {}
    }
    assert(all_of(yr, |c: u8| g_ok(c))) by {
        assert forall|k: int| 0 <= k < yr.len() implies g_ok(#[trigger] yr[k]) by {}
    }
    lemma_ok_concat(colon, sec);
    lemma_ok_concat(m, colon + sec);
    lemma_ok_concat(colon, m + (colon + sec));
    lemma_ok_concat(h, colon + (m + (colon + sec)));
    assert(all_of(tod, |c: u8| g_ok(c)));
    lemma_ok_concat(sp, g);
    lemma_ok_concat(tod, sp + g);
    lemma_ok_concat(sp, tod + (sp + g));
    lemma_ok_concat(yr, sp + (tod + (sp + g)));
    lemma_ok_concat(sp, yr + (sp + (tod + (sp + g))));
    lemma_ok_concat(mon, sp + (yr + (sp + (tod + (sp + g)))));
    lemma_ok_concat(sp, mon + (sp + (yr + (sp + (tod + (sp + g))))));
    lemma_ok_concat(dd, sp + (mon + (sp + (yr + (sp + (tod + (sp + g)))))));
    lemma_ok_concat(cs, dd + (sp + (mon + (sp + (yr + (sp + (tod + (sp + g))))))));
    lemma_ok_concat(dn, cs + (dd + (sp + (mon + (sp + (yr + (sp + (tod + (sp + g)))))))));
}

/// A piece with white space around its body is printable if the body is.
proof fn lemma_piece_ok(r: Seq<u8>, last: bool)
    requires
        all_of(piece_body(r, last), |c: u8| g_ok(c)),
    ensures
        all_of(r, |c: u8| g_ok(c)),
{
    lemma_piece_body(r, last);
    let head = body_head(r, last);
    let tail = body_tail(r, last);
    assert(all_of(head, |c: u8| g_ok(c))) by {
        assert forall|i: int| 0 <= i < head.len() implies g_ok(#[trigger] head[i]) by {
            assert(g_ows(head[i]));
        }
    }
    assert(all_of(tail, |c: u8| g_ok(c))) by {
        assert forall|i: int| 0 <= i < tail.len() implies g_ok(#[trigger] tail[i]) by {
            assert(g_ows(tail[i]));
        }
    }
    lemma_ok_concat(head, piece_body(r, last));
    lemma_ok_concat(head + piece_body(r, last), tail);
}

/// A `cookie-pair` is printable.
proof fn lemma_cookie_pair_ok(b: Seq<u8>)
    requires
        cookie_pair(b) is Some,
    ensures
        all_of(b, |c: u8| g_ok(c)),
{
    lemma_cookie_pair(b);
    let (name, value) = cookie_pair(b).unwrap();
    let n = token_len(b);
    let after = skip_bws(b.skip(n as int));
    let w1 = b.skip(n as int).take((b.skip(n as int).len() - after.len()) as int);
    let rest = after.skip(1);
    let w2 = rest.take((rest.len() - value.len()) as int);
    assert(all_of(name, |c: u8| g_ok(c))) by {
        assert forall|i: int| 0 <= i < name.len() implies g_ok(#[trigger] name[i]) by {
            assert(g_tchar(name[i]));
        }
    }
    assert(all_of(w1, |c: u8| g_ok(c))) by {
        assert forall|i: int| 0 <= i < w1.len() implies g_ok(#[trigger] w1[i]) by {
            assert(g_ows(w1[i]));
        }
    }
    assert(all_of(w2, |c: u8| g_ok(c))) by {
        assert forall|i: int| 0 <= i < w2.len() implies g_ok(#[trigger] w2[i]) by {
            assert(g_ows(w2[i]));
        }
    }
    assert(all_of(value, |c: u8| g_ok(c))) by {
        assert forall|i: int| 0 <= i < value.len() implies g_ok(#[trigger] value[i]) by {
            if all_of(value, |c: u8| g_cookie_octet(c)) {
                assert(g_cookie_octet(value[i]));
            } else {
                if i == 0 || i == value.len() - 1 {
                    assert(g_dquote(value[i]));
                } else {
                    assert(value.subrange(1, value.len() - 1)[i - 1] == value[i]);
                    assert(g_cookie_octet(value.subrange(1, value.len() - 1)[i - 1]));
                }
            }
        }
    }
    let eq = seq![0x3Du8];
    assert(all_of(eq, |c: u8| g_ok(c)));
    lemma_ok_concat(w2, value);
    lemma_ok_concat(eq, w2 + value);
    lemma_ok_concat(w1, eq + (w2 + value));
    lemma_ok_concat(name, w1 + (eq + (w2 + value)));
}

// ---------------------------------------------------------------------
// Proofs, part 6: no control characters, and the theorem.
// ---------------------------------------------------------------------

/// A named `cookie-av` is printable when its value is.
proof fn lemma_named_ok(b: Seq<u8>, name: Seq<u8>)
    requires
        av_value(b, name) is Some,
        all_of(av_value(b, name).unwrap(), |c: u8| g_ok(c)),
        all_of(name, |c: u8| g_ok(c)),
    ensures
        all_of(b, |c: u8| g_ok(c)),
{
    lemma_av_value(b, name);
    let v = av_value(b, name).unwrap();
    let n = b.take(name.len() as int);
    let after = skip_bws(b.skip(name.len() as int));
    let w1 = b.skip(name.len() as int).take((b.skip(name.len() as int).len() - after.len()) as int);
    let rest = after.skip(1);
    let w2 = rest.take((rest.len() - v.len()) as int);
    lemma_ci_ok(n, name);
    assert(all_of(w1, |c: u8| g_ok(c))) by {
        assert forall|i: int| 0 <= i < w1.len() implies g_ok(#[trigger] w1[i]) by {
            assert(g_ows(w1[i]));
        }
    }
    assert(all_of(w2, |c: u8| g_ok(c))) by {
        assert forall|i: int| 0 <= i < w2.len() implies g_ok(#[trigger] w2[i]) by {
            assert(g_ows(w2[i]));
        }
    }
    let eq = seq![0x3Du8];
    assert(all_of(eq, |c: u8| g_ok(c)));
    lemma_ok_concat(w2, v);
    lemma_ok_concat(eq, w2 + v);
    lemma_ok_concat(w1, eq + (w2 + v));
    lemma_ok_concat(n, w1 + (eq + (w2 + v)));
}

/// A `cookie-av` is printable.
proof fn lemma_av_ok(b: Seq<u8>)
    requires
        cookie_av(b) is Some,
    ensures
        all_of(b, |c: u8| g_ok(c)),
{
    lemma_names_ok();
    if is_ci(b, name_secure()) {
        lemma_ci_ok(b, name_secure());
    } else if is_ci(b, name_httponly()) {
        lemma_ci_ok(b, name_httponly());
    } else if av_value(b, name_expires()) is Some && is_sane_cookie_date(av_value(b, name_expires()).unwrap()) {
        let v = av_value(b, name_expires()).unwrap();
        assert(exists|f: crate::date::independent::HttpDateFields|
            crate::date::independent::fields_allowed(f) && #[trigger] crate::date::independent::imf_fixdate(f) == v);
        lemma_imf_ok(date_fields_of(v));
        lemma_named_ok(b, name_expires());
    } else if av_value(b, name_max_age()) is Some && is_max_age_value(av_value(b, name_max_age()).unwrap()) {
        let v = av_value(b, name_max_age()).unwrap();
        assert(all_of(v, |c: u8| g_ok(c))) by {
            assert forall|i: int| 0 <= i < v.len() implies g_ok(#[trigger] v[i]) by {
                assert(g_digit(v[i]));
            }
        }
        lemma_named_ok(b, name_max_age());
    } else if av_value(b, name_domain()) is Some && is_subdomain(av_value(b, name_domain()).unwrap()) {
        let v = av_value(b, name_domain()).unwrap();
        assert(all_of(v, |c: u8| g_ok(c))) by {
            assert forall|i: int| 0 <= i < v.len() implies g_ok(#[trigger] v[i]) by {
                assert(is_let_dig(v[i]) || v[i] == 0x2D || v[i] == 0x2E);
            }
        }
        lemma_named_ok(b, name_domain());
    } else if av_value(b, name_path()) is Some && all_of(av_value(b, name_path()).unwrap(), |c: u8| g_av_octet(c)) {
        let v = av_value(b, name_path()).unwrap();
        assert(all_of(v, |c: u8| g_ok(c))) by {
            assert forall|i: int| 0 <= i < v.len() implies g_ok(#[trigger] v[i]) by {
                assert(g_av_octet(v[i]));
            }
        }
        lemma_named_ok(b, name_path());
    } else if av_value(b, name_samesite()) is Some && samesite_value(av_value(b, name_samesite()).unwrap()) is Some {
        let v = av_value(b, name_samesite()).unwrap();
        if is_ci(v, seq![0x73u8, 0x74, 0x72, 0x69, 0x63, 0x74]) {
            lemma_ci_ok(v, seq![0x73u8, 0x74, 0x72, 0x69, 0x63, 0x74]);
        } else if is_ci(v, seq![0x6Cu8, 0x61, 0x78]) {
            lemma_ci_ok(v, seq![0x6Cu8, 0x61, 0x78]);
        } else {
            lemma_ci_ok(v, seq![0x6Eu8, 0x6F, 0x6E, 0x65]);
        }
        lemma_named_ok(b, name_samesite());
    } else {
        assert forall|i: int| 0 <= i < b.len() implies g_ok(#[trigger] b[i]) by {
            assert(g_av_octet(b[i]));
        }
    }
}

/// Every piece after the first is printable, if the attributes parse.
proof fn lemma_av_list_ok(ps: Seq<Seq<u8>>, i: nat)
    requires
        i <= ps.len(),
        av_list(ps, i) is Some,
    ensures
        forall|k: int| i <= k < ps.len() ==> all_of(#[trigger] ps[k], |c: u8| g_ok(c)),
    decreases ps.len() - i,
{
    if i < ps.len() {
        let b = piece_body(ps[i as int], i + 1 == ps.len());
        lemma_av_ok(b);
        lemma_piece_ok(ps[i as int], i + 1 == ps.len());
        lemma_av_list_ok(ps, i + 1);
    }
}

/// A string whose pieces between semicolons are printable is printable.
proof fn lemma_split_ok(s: Seq<u8>)
    requires
        forall|k: int| 0 <= k < split_semicolons(s).len() ==> all_of(#[trigger] split_semicolons(s)[k], |c: u8| g_ok(c)),
    ensures
        all_of(s, |c: u8| g_ok(c)),
    decreases s.len(),
{
    lemma_split_head(s);
    super::termination::lemma_find_octet_bounds(s, 0x3B, 0);
    let j = crate::ascii::find_octet(s, 0x3B, 0);
    if j < s.len() {
        let t = s.skip(j as int + 1);
        let ps = split_semicolons(s);
        assert(ps =~= seq![s.take(j as int)] + split_semicolons(t));
        assert forall|k: int| 0 <= k < split_semicolons(t).len() implies all_of(
            #[trigger] split_semicolons(t)[k],
            |c: u8| g_ok(c),
        ) by {
            assert(ps[k + 1] == split_semicolons(t)[k]);
        }
        lemma_split_ok(t);
        assert(all_of(s.take(j as int), |c: u8| g_ok(c))) by {
            assert(ps[0] == s.take(j as int));
        }
        let semi = seq![0x3Bu8];
        assert(all_of(semi, |c: u8| g_ok(c)));
        lemma_ok_concat(s.take(j as int), semi);
        lemma_ok_concat(s.take(j as int) + semi, t);
        assert(s =~= s.take(j as int) + semi + t);
    } else {
        assert(split_semicolons(s) =~= seq![s]);
        assert(split_semicolons(s)[0] == s);
    }
}

/// No octet of a printable string is a CTL character excluding HTAB.
proof fn lemma_no_ctl(s: Seq<u8>, i: nat)
    requires
        all_of(s, |c: u8| g_ok(c)),
    ensures
        !contains_ctl_from(s, i),
    decreases s.len() - i,
{
    if i < s.len() {
        assert(g_ok(s[i as int]));
        lemma_no_ctl(s, i + 1);
    }
}

/// The theorem. On every string the grammar matches whose parse is in the
/// class, the user agent's parse has the same name and value, and the
/// attributes the grammar's `cookie-av`s denote.
pub proof fn lemma_set_cookie_agrees(s: Seq<u8>, uri_path: Seq<u8>, now: int)
    ensures
        set_cookie_agrees(s, uri_path, now),
{
    if set_cookie_string(s) is Some && in_class(set_cookie_string(s).unwrap()) {
        let c = set_cookie_string(s).unwrap();
        let pieces = split_semicolons(s);
        lemma_split_head(s);
        let last0 = pieces.len() == 1;
        let b0 = piece_body(pieces[0], last0);
        assert(cookie_pair(b0) == Some((c.name, c.value)));
        assert(av_list(pieces, 1) == Some(c.avs));
        // Step 1: no CTL characters.
        lemma_cookie_pair_ok(b0);
        lemma_piece_ok(pieces[0], last0);
        lemma_av_list_ok(pieces, 1);
        assert forall|k: int| 0 <= k < split_semicolons(s).len() implies all_of(
            #[trigger] split_semicolons(s)[k],
            |cc: u8| g_ok(cc),
        ) by {
            if k == 0 {
                assert(split_semicolons(s)[0] == pieces[0]);
            }
        }
        lemma_split_ok(s);
        lemma_no_ctl(s, 0);
        assert(!contains_ctl_excluding_htab(s));
        // Steps 2 to 4: the name and the value.
        let j = crate::ascii::find_octet(s, 0x3B, 0);
        super::termination::lemma_find_octet_bounds(s, 0x3B, 0);
        if j == s.len() {
            assert(pieces =~= seq![s]);
            assert(s.subrange(0, j as int) =~= s);
        } else {
            assert(pieces =~= seq![s.take(j as int)] + split_semicolons(s.skip(j as int + 1)));
            assert(s.subrange(0, j as int) =~= s.take(j as int));
        }
        assert(s.subrange(0, j as int) == pieces[0]);
        lemma_cookie_pair(b0);
        lemma_piece_body(pieces[0], last0);
        let (name, value) = (c.name, c.value);
        let n = token_len(b0);
        let after = skip_bws(b0.skip(n as int));
        let w1 = b0.skip(n as int).take((b0.skip(n as int).len() - after.len()) as int);
        let rest = after.skip(1);
        let w2 = rest.take((rest.len() - value.len()) as int);
        let head0 = body_head(pieces[0], last0);
        let tail0 = body_tail(pieces[0], last0);
        assert(no_equals(name)) by {
            assert forall|i: int| 0 <= i < name.len() implies (#[trigger] name[i]) != 0x3D by {
                assert(g_tchar(name[i]));
            }
        }
        assert(trimmed(name)) by {
            assert(g_tchar(name[0]));
            assert(g_tchar(name[name.len() - 1]));
        }
        assert(trimmed(value)) by {
            if value.len() > 0 {
                if all_of(value, |cc: u8| g_cookie_octet(cc)) {
                    assert(g_cookie_octet(value[0]));
                    assert(g_cookie_octet(value[value.len() - 1]));
                } else {
                    assert(g_dquote(value[0]));
                    assert(g_dquote(value[value.len() - 1]));
                }
            }
        }
        assert(pieces[0] == head0 + (name + (w1 + (seq![0x3Du8] + (w2 + value)))) + tail0);
        lemma_pair_split(head0, name, w1, w2, value, tail0);
        // Steps 5 and 6.
        assert(name.len() + value.len() <= 4096);
        // The attributes.
        lemma_parse_attributes(s, j, uri_path, now, seq![]);
        lemma_av_list(pieces, 1, c.avs, uri_path, now);
        if j == s.len() {
            assert(pieces.skip(1) =~= Seq::<Seq<u8>>::empty());
            assert(c.avs =~= Seq::<ServerAv>::empty());
        } else {
            assert(pieces.skip(1) =~= split_semicolons(s.skip(j as int + 1)));
        }
        assert(Seq::<Attribute>::empty() + denote_avs(c.avs, uri_path, now) =~= denote_avs(c.avs, uri_path, now));
    }
}

/// The grammar accepts at least `a=b`: the statement is not vacuous.
pub proof fn lemma_example_pair()
    ensures
        set_cookie_string(seq![0x61u8, 0x3D, 0x62]) == Some(
            ServerCookie { name: seq![0x61u8], value: seq![0x62u8], avs: seq![] },
        ),
{
    let s = seq![0x61u8, 0x3D, 0x62];
    reveal_with_fuel(split_loop, 5);
    reveal_with_fuel(skip_bws, 3);
    reveal_with_fuel(trim_bws_end, 3);
    reveal_with_fuel(token_len, 3);
    reveal_with_fuel(crate::ascii::find_octet, 5);
    lemma_split_head(s);
    assert(crate::ascii::find_octet(s, 0x3B, 0) == 3);
    assert(split_semicolons(s) =~= seq![s]);
    assert(token_len(s) == 1);
    assert(s.skip(1) =~= seq![0x3Du8, 0x62u8]);
    assert(skip_bws(s.skip(1)) =~= s.skip(1));
    assert(skip_bws(s.skip(1).skip(1)) =~= seq![0x62u8]);
    assert(is_cookie_value(seq![0x62u8])) by {
        assert(all_of(seq![0x62u8], |c: u8| g_cookie_octet(c)));
    }
    assert(skip_bws(s) =~= s);
    assert(piece_body(s, true) =~= s);
    assert(s.take(1) =~= seq![0x61u8]);
    assert(cookie_pair(s) == Some((seq![0x61u8], seq![0x62u8])));
    assert(av_list(split_semicolons(s), 1) == Some(Seq::<ServerAv>::empty()));
}

} // verus!
