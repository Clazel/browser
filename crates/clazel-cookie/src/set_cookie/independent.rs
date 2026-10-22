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
//! string denotes. The statement of what the two parsers agree on is at the
//! end of this file.
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

} // verus!
