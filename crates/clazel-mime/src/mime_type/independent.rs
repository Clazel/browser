//! An independent transcription of MIME type parsing, from a different
//! standard than [`super::spec`]: the HTTP `media-type` grammar
//! (docs/VERIFICATION.md, "Trust without reviewers", item 2). The
//! transcription section uses nothing from `spec.rs`; only the proof
//! section below it does.
//!
//! Source: RFC 9110 "HTTP Semantics" (June 2022; an RFC never changes after
//! publication), <https://www.rfc-editor.org/rfc/rfc9110>: §8.3.1 Media
//! Type (`media-type`, `type`, `subtype`, and "The type and subtype tokens
//! are case-insensitive"), §5.6.2 Tokens (`token`, `tchar`), §5.6.3
//! Whitespace (`OWS`), §5.6.4 Quoted Strings (`quoted-string`, `qdtext`,
//! `quoted-pair`, and "Recipients that process the value of a
//! quoted-string MUST handle a quoted-pair as if it were replaced by the
//! octet following the backslash"), §5.6.6 Parameters (`parameters`,
//! `parameter`, "Parameter names are case-insensitive", "The quoted and
//! unquoted values are equivalent"), §5.5 (`obs-text`). Core rules
//! (`ALPHA`, `DIGIT`, `DQUOTE`, `HTAB`, `SP`, `VCHAR`) from RFC 5234
//! Appendix B.1. The MIME Sniffing Standard §4.3 defines "valid MIME type
//! string" as a string matching this `media-type` production.
//!
//! [`media_type`] returns `None` for a string that does not match
//! `media-type`, and otherwise the value it denotes. What the two parsers
//! agree on is stated and proven at the end of this file:
//! [`lemma_equals_parse_a_mime_type`] proves `parse_a_mime_type` gives the
//! same record on **every string that matches `media-type` and has no
//! parameter name twice (compared case-insensitively)**, and
//! [`lemma_serialize_is_media_type`] proves every serialization of a parsed
//! record matches `media-type` and denotes that record. Outside that class
//! they differ by design: the WHATWG parser also accepts strings RFC 9110
//! rejects (leading or trailing whitespace, CR and LF, a parameter with no
//! "=", text after a quoted string, code points above U+00FF, ...), and
//! keeps only the first of repeated parameters, where the grammar keeps
//! them all.
//!
//! Modelling choices:
//! - A string is a `Seq<u32>` of code points; RFC 9110's octets are the
//!   code points U+0000 to U+00FF. A code point above U+00FF matches no
//!   rule, so a string holding one never matches.
//! - The grammar is read by a parser that decides each choice with the
//!   next code point, which is exact here: a `token` is the longest run of
//!   `tchar`s (no rule after a token can start with a `tchar`); `OWS` is
//!   the longest run of SP and HTAB (the rule after it is ";", the end, or
//!   a `parameter`, which starts with a `tchar`); `parameter-value` is a
//!   `quoted-string` exactly when it starts with DQUOTE (`tchar` excludes
//!   it); and inside a `quoted-string`, `qdtext` excludes DQUOTE and "\",
//!   so each code point decides between `qdtext`, `quoted-pair` and the
//!   closing DQUOTE.
//! - `[ parameter ]` is present exactly when the code point after `OWS` is
//!   a `tchar`: a `parameter` starts with one, and otherwise the
//!   repetition can only continue with `OWS ";"`, or end.
//! - "case-insensitive" is represented by mapping ALPHA to its lowercase
//!   letter (RFC 5234 §2.3: %x41-5A and %x61-7A are the same letters), so
//!   equal-ignoring-case values are equal. Type, subtype and parameter
//!   names are mapped; parameter values are kept as written, since §5.6.6
//!   leaves their case-sensitivity to each parameter.
//! - The value of a `quoted-string` is its content with each
//!   `quoted-pair` replaced by its second octet (§5.6.4). Per §5.6.6 a
//!   token value and a quoted value with the same content are equal.
//! - Parameters are kept in order, repeats included: §5.6.6 says nothing
//!   about repeated names.

// Only the proof section below uses `spec.rs`.
#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// RFC 5234 B.1: `ALPHA = %x41-5A / %x61-7A ; A-Z / a-z`.
pub open spec fn is_alpha(c: u32) -> bool {
    (0x41 <= c <= 0x5A) || (0x61 <= c <= 0x7A)
}

/// RFC 5234 B.1: `DIGIT = %x30-39 ; 0-9`.
pub open spec fn is_digit(c: u32) -> bool {
    0x30 <= c <= 0x39
}

/// RFC 5234 B.1: `VCHAR = %x21-7E ; visible (printing) characters`.
pub open spec fn is_vchar(c: u32) -> bool {
    0x21 <= c <= 0x7E
}

/// RFC 5234 B.1: `HTAB = %x09` and `SP = %x20`. RFC 9110 §5.6.3:
/// `OWS = *( SP / HTAB )`; this is one such code point.
pub open spec fn is_sp_or_htab(c: u32) -> bool {
    c == 0x20 || c == 0x09
}

/// RFC 9110 §5.5: `obs-text = %x80-FF`.
pub open spec fn is_obs_text(c: u32) -> bool {
    0x80 <= c <= 0xFF
}

/// RFC 9110 §5.6.2: `tchar = "!" / "#" / "$" / "%" / "&" / "'" / "*" /
/// "+" / "-" / "." / "^" / "_" / "`" / "|" / "~" / DIGIT / ALPHA`.
pub open spec fn is_tchar(c: u32) -> bool {
    match c {
        // "!" "#" "$" "%" "&" "'" "*" "+" "-" "." "^" "_" "`" "|" "~"
        0x21 | 0x23 | 0x24 | 0x25 | 0x26 | 0x27 | 0x2A | 0x2B | 0x2D | 0x2E | 0x5E | 0x5F | 0x60 | 0x7C | 0x7E => true,
        _ => is_digit(c) || is_alpha(c),
    }
}

/// RFC 9110 §5.6.4: `qdtext = HTAB / SP / %x21 / %x23-5B / %x5D-7E / obs-text`.
pub open spec fn is_qdtext(c: u32) -> bool {
    c == 0x09 || c == 0x20 || c == 0x21 || (0x23 <= c <= 0x5B) || (0x5D <= c <= 0x7E) || is_obs_text(c)
}

/// RFC 9110 §5.6.4: the octet after "\" in
/// `quoted-pair = "\" ( HTAB / SP / VCHAR / obs-text )`.
pub open spec fn is_quoted_pair_octet(c: u32) -> bool {
    c == 0x09 || c == 0x20 || is_vchar(c) || is_obs_text(c)
}

/// Where the longest run of `tchar`s starting at `i` ends.
pub open spec fn tchars_end(s: Seq<u32>, i: nat) -> nat
    decreases s.len() - i
{
    if i < s.len() && is_tchar(s[i as int]) {
        tchars_end(s, i + 1)
    } else {
        i
    }
}

/// `OWS` (§5.6.3) at `i`: where the longest run of SP and HTAB ends.
pub open spec fn ows_end(s: Seq<u32>, i: nat) -> nat
    decreases s.len() - i
{
    if i < s.len() && is_sp_or_htab(s[i as int]) {
        ows_end(s, i + 1)
    } else {
        i
    }
}

/// `token = 1*tchar` (§5.6.2) at `i`: the token and the position after it.
pub open spec fn token(s: Seq<u32>, i: nat) -> Option<(Seq<u32>, nat)> {
    let end = tchars_end(s, i);
    if end > i {
        Some((s.subrange(i as int, end as int), end))
    } else {
        None
    }
}

/// `*( qdtext / quoted-pair ) DQUOTE` at `i`, the rest of a
/// `quoted-string` after its opening DQUOTE, with `value` read so far.
/// Returns the value and the position after the closing DQUOTE.
pub open spec fn quoted_string_rest(s: Seq<u32>, i: nat, value: Seq<u32>) -> Option<(Seq<u32>, nat)>
    decreases s.len() - i
{
    if i >= s.len() {
        // No closing DQUOTE.
        None
    } else if s[i as int] == 0x22 {
        // The closing DQUOTE.
        Some((value, i + 1))
    } else if s[i as int] == 0x5C {
        // quoted-pair: "replaced by the octet following the backslash".
        if i + 1 < s.len() && is_quoted_pair_octet(s[i as int + 1]) {
            quoted_string_rest(s, i + 2, value.push(s[i as int + 1]))
        } else {
            None
        }
    } else if is_qdtext(s[i as int]) {
        quoted_string_rest(s, i + 1, value.push(s[i as int]))
    } else {
        None
    }
}

/// `quoted-string = DQUOTE *( qdtext / quoted-pair ) DQUOTE` (§5.6.4) at
/// `i`: its value, and the position after it.
pub open spec fn quoted_string(s: Seq<u32>, i: nat) -> Option<(Seq<u32>, nat)> {
    if i < s.len() && s[i as int] == 0x22 {
        quoted_string_rest(s, i + 1, seq![])
    } else {
        None
    }
}

/// `parameter-value = ( token / quoted-string )` (§5.6.6) at `i`.
pub open spec fn parameter_value(s: Seq<u32>, i: nat) -> Option<(Seq<u32>, nat)> {
    if i < s.len() && s[i as int] == 0x22 {
        quoted_string(s, i)
    } else {
        token(s, i)
    }
}

/// Case-insensitive text, as one canonical form: each ALPHA in %x41-5A
/// mapped to its lowercase letter (see the modelling choices).
pub open spec fn fold_case(s: Seq<u32>) -> Seq<u32> {
    s.map_values(|c: u32| if 0x41 <= c <= 0x5A { (c + 0x20) as u32 } else { c })
}

/// A media type's value: type, subtype and parameters (name, value), with
/// the case-insensitive parts folded.
pub struct MediaType {
    /// type
    pub type_: Seq<u32>,
    /// subtype
    pub subtype: Seq<u32>,
    /// parameters, in order
    pub parameters: Seq<(Seq<u32>, Seq<u32>)>,
}

/// `parameters = *( OWS ";" OWS [ parameter ] )` (§5.6.6) from `i` to the
/// end of the input, with the parameters read so far in `acc`.
pub open spec fn parameters(s: Seq<u32>, i: nat, acc: Seq<(Seq<u32>, Seq<u32>)>) -> Option<Seq<(Seq<u32>, Seq<u32>)>>
    decreases s.len() - i via parameters_decreases
{
    if i >= s.len() {
        // No more repetitions, and nothing left over.
        Some(acc)
    } else {
        // OWS ";"
        let j = ows_end(s, i);
        if j < s.len() && s[j as int] == 0x3B {
            // OWS
            let k = ows_end(s, j + 1);
            if k < s.len() && is_tchar(s[k as int]) {
                // parameter = parameter-name "=" parameter-value
                match token(s, k) {
                    Some((name, n)) => if n < s.len() && s[n as int] == 0x3D {
                        match parameter_value(s, n + 1) {
                            Some((value, e)) => parameters(s, e, acc.push((fold_case(name), value))),
                            None => None,
                        }
                    } else {
                        None
                    },
                    None => None,
                }
            } else {
                // [ parameter ] absent.
                parameters(s, k, acc)
            }
        } else {
            // Neither the end nor another repetition.
            None
        }
    }
}

/// `media-type = type "/" subtype parameters` (§8.3.1), `type = token`,
/// `subtype = token`, over all of `s`. `None`: `s` does not match.
pub open spec fn media_type(s: Seq<u32>) -> Option<MediaType> {
    match token(s, 0) {
        Some((type_, p)) => if p < s.len() && s[p as int] == 0x2F {
            match token(s, p + 1) {
                Some((subtype, q)) => match parameters(s, q, seq![]) {
                    Some(ps) => Some(MediaType { type_: fold_case(type_), subtype: fold_case(subtype), parameters: ps }),
                    None => None,
                },
                None => None,
            }
        } else {
            None
        },
        None => None,
    }
}

/// Termination of [`parameters`]: every repetition moves forward.
#[via_fn]
proof fn parameters_decreases(s: Seq<u32>, i: nat, acc: Seq<(Seq<u32>, Seq<u32>)>) {
    if i < s.len() {
        lemma_ows_end(s, i);
        let j = ows_end(s, i);
        lemma_ows_end(s, j + 1);
        let k = ows_end(s, j + 1);
        lemma_tchars_end(s, k);
        let n = tchars_end(s, k);
        lemma_quoted_string_rest_position(s, n + 2, seq![]);
        lemma_tchars_end(s, n + 1);
    }
}

/// Where a run of `tchar`s ends.
pub proof fn lemma_tchars_end(s: Seq<u32>, i: nat)
    ensures
        tchars_end(s, i) >= i,
        i <= s.len() ==> tchars_end(s, i) <= s.len(),
        forall|k: int| i <= k < tchars_end(s, i) ==> is_tchar(#[trigger] s[k]),
        tchars_end(s, i) < s.len() ==> !is_tchar(s[tchars_end(s, i) as int]),
    decreases s.len() - i
{
    if i < s.len() && is_tchar(s[i as int]) {
        lemma_tchars_end(s, i + 1);
    }
}

/// Where `OWS` ends.
pub proof fn lemma_ows_end(s: Seq<u32>, i: nat)
    ensures
        ows_end(s, i) >= i,
        i <= s.len() ==> ows_end(s, i) <= s.len(),
        forall|k: int| i <= k < ows_end(s, i) ==> is_sp_or_htab(#[trigger] s[k]),
        ows_end(s, i) < s.len() ==> !is_sp_or_htab(s[ows_end(s, i) as int]),
    decreases s.len() - i
{
    if i < s.len() && is_sp_or_htab(s[i as int]) {
        lemma_ows_end(s, i + 1);
    }
}

/// A quoted string ends after where it starts, within the input.
pub proof fn lemma_quoted_string_rest_position(s: Seq<u32>, i: nat, value: Seq<u32>)
    ensures
        quoted_string_rest(s, i, value) matches Some((_, e)) ==> i < e <= s.len(),
    decreases s.len() - i
{
    if i < s.len() && s[i as int] != 0x22 {
        if s[i as int] == 0x5C {
            if i + 1 < s.len() && is_quoted_pair_octet(s[i as int + 1]) {
                lemma_quoted_string_rest_position(s, i + 2, value.push(s[i as int + 1]));
            }
        } else if is_qdtext(s[i as int]) {
            lemma_quoted_string_rest_position(s, i + 1, value.push(s[i as int]));
        }
    }
}

// ===========================================================================
// Proof: what this transcription and `spec.rs` agree on. Everything below
// is proof machinery; the transcription ends above.
// ===========================================================================


/// RFC 9110 §8.3.1's own examples: the first three are equal; the fourth
/// differs only in the charset value's case, which RFC 2046 makes
/// insignificant for charset but which this grammar keeps (see the
/// modelling choices). Then three strings that are not media types, and
/// one whose repeated parameter is kept.
pub proof fn lemma_rfc_examples() {
    // text/html;charset=utf-8
    assert(media_type(seq![0x74u32, 0x65u32, 0x78u32, 0x74u32, 0x2Fu32, 0x68u32, 0x74u32, 0x6Du32, 0x6Cu32, 0x3Bu32, 0x63u32, 0x68u32, 0x61u32, 0x72u32, 0x73u32, 0x65u32, 0x74u32, 0x3Du32, 0x75u32, 0x74u32, 0x66u32, 0x2Du32, 0x38u32]) is Some
        && media_type(seq![0x74u32, 0x65u32, 0x78u32, 0x74u32, 0x2Fu32, 0x68u32, 0x74u32, 0x6Du32, 0x6Cu32, 0x3Bu32, 0x63u32, 0x68u32, 0x61u32, 0x72u32, 0x73u32, 0x65u32, 0x74u32, 0x3Du32, 0x75u32, 0x74u32, 0x66u32, 0x2Du32, 0x38u32])->Some_0.type_ =~= seq![0x74u32, 0x65u32, 0x78u32, 0x74u32]
        && media_type(seq![0x74u32, 0x65u32, 0x78u32, 0x74u32, 0x2Fu32, 0x68u32, 0x74u32, 0x6Du32, 0x6Cu32, 0x3Bu32, 0x63u32, 0x68u32, 0x61u32, 0x72u32, 0x73u32, 0x65u32, 0x74u32, 0x3Du32, 0x75u32, 0x74u32, 0x66u32, 0x2Du32, 0x38u32])->Some_0.subtype =~= seq![0x68u32, 0x74u32, 0x6Du32, 0x6Cu32]
        && media_type(seq![0x74u32, 0x65u32, 0x78u32, 0x74u32, 0x2Fu32, 0x68u32, 0x74u32, 0x6Du32, 0x6Cu32, 0x3Bu32, 0x63u32, 0x68u32, 0x61u32, 0x72u32, 0x73u32, 0x65u32, 0x74u32, 0x3Du32, 0x75u32, 0x74u32, 0x66u32, 0x2Du32, 0x38u32])->Some_0.parameters.len() == 1
        && media_type(seq![0x74u32, 0x65u32, 0x78u32, 0x74u32, 0x2Fu32, 0x68u32, 0x74u32, 0x6Du32, 0x6Cu32, 0x3Bu32, 0x63u32, 0x68u32, 0x61u32, 0x72u32, 0x73u32, 0x65u32, 0x74u32, 0x3Du32, 0x75u32, 0x74u32, 0x66u32, 0x2Du32, 0x38u32])->Some_0.parameters[0].0 =~= seq![0x63u32, 0x68u32, 0x61u32, 0x72u32, 0x73u32, 0x65u32, 0x74u32]
        && media_type(seq![0x74u32, 0x65u32, 0x78u32, 0x74u32, 0x2Fu32, 0x68u32, 0x74u32, 0x6Du32, 0x6Cu32, 0x3Bu32, 0x63u32, 0x68u32, 0x61u32, 0x72u32, 0x73u32, 0x65u32, 0x74u32, 0x3Du32, 0x75u32, 0x74u32, 0x66u32, 0x2Du32, 0x38u32])->Some_0.parameters[0].1 =~= seq![0x75u32, 0x74u32, 0x66u32, 0x2Du32, 0x38u32]) by (compute_only);
    // Text/HTML;Charset="utf-8"
    assert(media_type(seq![0x54u32, 0x65u32, 0x78u32, 0x74u32, 0x2Fu32, 0x48u32, 0x54u32, 0x4Du32, 0x4Cu32, 0x3Bu32, 0x43u32, 0x68u32, 0x61u32, 0x72u32, 0x73u32, 0x65u32, 0x74u32, 0x3Du32, 0x22u32, 0x75u32, 0x74u32, 0x66u32, 0x2Du32, 0x38u32, 0x22u32]) is Some
        && media_type(seq![0x54u32, 0x65u32, 0x78u32, 0x74u32, 0x2Fu32, 0x48u32, 0x54u32, 0x4Du32, 0x4Cu32, 0x3Bu32, 0x43u32, 0x68u32, 0x61u32, 0x72u32, 0x73u32, 0x65u32, 0x74u32, 0x3Du32, 0x22u32, 0x75u32, 0x74u32, 0x66u32, 0x2Du32, 0x38u32, 0x22u32])->Some_0.type_ =~= seq![0x74u32, 0x65u32, 0x78u32, 0x74u32]
        && media_type(seq![0x54u32, 0x65u32, 0x78u32, 0x74u32, 0x2Fu32, 0x48u32, 0x54u32, 0x4Du32, 0x4Cu32, 0x3Bu32, 0x43u32, 0x68u32, 0x61u32, 0x72u32, 0x73u32, 0x65u32, 0x74u32, 0x3Du32, 0x22u32, 0x75u32, 0x74u32, 0x66u32, 0x2Du32, 0x38u32, 0x22u32])->Some_0.subtype =~= seq![0x68u32, 0x74u32, 0x6Du32, 0x6Cu32]
        && media_type(seq![0x54u32, 0x65u32, 0x78u32, 0x74u32, 0x2Fu32, 0x48u32, 0x54u32, 0x4Du32, 0x4Cu32, 0x3Bu32, 0x43u32, 0x68u32, 0x61u32, 0x72u32, 0x73u32, 0x65u32, 0x74u32, 0x3Du32, 0x22u32, 0x75u32, 0x74u32, 0x66u32, 0x2Du32, 0x38u32, 0x22u32])->Some_0.parameters.len() == 1
        && media_type(seq![0x54u32, 0x65u32, 0x78u32, 0x74u32, 0x2Fu32, 0x48u32, 0x54u32, 0x4Du32, 0x4Cu32, 0x3Bu32, 0x43u32, 0x68u32, 0x61u32, 0x72u32, 0x73u32, 0x65u32, 0x74u32, 0x3Du32, 0x22u32, 0x75u32, 0x74u32, 0x66u32, 0x2Du32, 0x38u32, 0x22u32])->Some_0.parameters[0].0 =~= seq![0x63u32, 0x68u32, 0x61u32, 0x72u32, 0x73u32, 0x65u32, 0x74u32]
        && media_type(seq![0x54u32, 0x65u32, 0x78u32, 0x74u32, 0x2Fu32, 0x48u32, 0x54u32, 0x4Du32, 0x4Cu32, 0x3Bu32, 0x43u32, 0x68u32, 0x61u32, 0x72u32, 0x73u32, 0x65u32, 0x74u32, 0x3Du32, 0x22u32, 0x75u32, 0x74u32, 0x66u32, 0x2Du32, 0x38u32, 0x22u32])->Some_0.parameters[0].1 =~= seq![0x75u32, 0x74u32, 0x66u32, 0x2Du32, 0x38u32]) by (compute_only);
    // text/html; charset="utf-8"
    assert(media_type(seq![0x74u32, 0x65u32, 0x78u32, 0x74u32, 0x2Fu32, 0x68u32, 0x74u32, 0x6Du32, 0x6Cu32, 0x3Bu32, 0x20u32, 0x63u32, 0x68u32, 0x61u32, 0x72u32, 0x73u32, 0x65u32, 0x74u32, 0x3Du32, 0x22u32, 0x75u32, 0x74u32, 0x66u32, 0x2Du32, 0x38u32, 0x22u32]) is Some
        && media_type(seq![0x74u32, 0x65u32, 0x78u32, 0x74u32, 0x2Fu32, 0x68u32, 0x74u32, 0x6Du32, 0x6Cu32, 0x3Bu32, 0x20u32, 0x63u32, 0x68u32, 0x61u32, 0x72u32, 0x73u32, 0x65u32, 0x74u32, 0x3Du32, 0x22u32, 0x75u32, 0x74u32, 0x66u32, 0x2Du32, 0x38u32, 0x22u32])->Some_0.type_ =~= seq![0x74u32, 0x65u32, 0x78u32, 0x74u32]
        && media_type(seq![0x74u32, 0x65u32, 0x78u32, 0x74u32, 0x2Fu32, 0x68u32, 0x74u32, 0x6Du32, 0x6Cu32, 0x3Bu32, 0x20u32, 0x63u32, 0x68u32, 0x61u32, 0x72u32, 0x73u32, 0x65u32, 0x74u32, 0x3Du32, 0x22u32, 0x75u32, 0x74u32, 0x66u32, 0x2Du32, 0x38u32, 0x22u32])->Some_0.subtype =~= seq![0x68u32, 0x74u32, 0x6Du32, 0x6Cu32]
        && media_type(seq![0x74u32, 0x65u32, 0x78u32, 0x74u32, 0x2Fu32, 0x68u32, 0x74u32, 0x6Du32, 0x6Cu32, 0x3Bu32, 0x20u32, 0x63u32, 0x68u32, 0x61u32, 0x72u32, 0x73u32, 0x65u32, 0x74u32, 0x3Du32, 0x22u32, 0x75u32, 0x74u32, 0x66u32, 0x2Du32, 0x38u32, 0x22u32])->Some_0.parameters.len() == 1
        && media_type(seq![0x74u32, 0x65u32, 0x78u32, 0x74u32, 0x2Fu32, 0x68u32, 0x74u32, 0x6Du32, 0x6Cu32, 0x3Bu32, 0x20u32, 0x63u32, 0x68u32, 0x61u32, 0x72u32, 0x73u32, 0x65u32, 0x74u32, 0x3Du32, 0x22u32, 0x75u32, 0x74u32, 0x66u32, 0x2Du32, 0x38u32, 0x22u32])->Some_0.parameters[0].0 =~= seq![0x63u32, 0x68u32, 0x61u32, 0x72u32, 0x73u32, 0x65u32, 0x74u32]
        && media_type(seq![0x74u32, 0x65u32, 0x78u32, 0x74u32, 0x2Fu32, 0x68u32, 0x74u32, 0x6Du32, 0x6Cu32, 0x3Bu32, 0x20u32, 0x63u32, 0x68u32, 0x61u32, 0x72u32, 0x73u32, 0x65u32, 0x74u32, 0x3Du32, 0x22u32, 0x75u32, 0x74u32, 0x66u32, 0x2Du32, 0x38u32, 0x22u32])->Some_0.parameters[0].1 =~= seq![0x75u32, 0x74u32, 0x66u32, 0x2Du32, 0x38u32]) by (compute_only);
    // text/html;charset=UTF-8: the value keeps its case.
    assert(media_type(seq![0x74u32, 0x65u32, 0x78u32, 0x74u32, 0x2Fu32, 0x68u32, 0x74u32, 0x6Du32, 0x6Cu32, 0x3Bu32, 0x63u32, 0x68u32, 0x61u32, 0x72u32, 0x73u32, 0x65u32, 0x74u32, 0x3Du32, 0x55u32, 0x54u32, 0x46u32, 0x2Du32, 0x38u32])->Some_0.parameters[0].1 =~= seq![0x55u32, 0x54u32, 0x46u32, 0x2Du32, 0x38u32]) by (compute_only);
    // "text/html " (trailing space), "t/h;c" (no "="), "t/h;a=\"b"
    // (unterminated quoted string), "t/h;a=b;a=c" (repeats kept).
    assert(media_type(seq![0x74u32, 0x65u32, 0x78u32, 0x74u32, 0x2Fu32, 0x68u32, 0x74u32, 0x6Du32, 0x6Cu32, 0x20u32]) is None && media_type(seq![0x74u32, 0x2Fu32, 0x68u32, 0x3Bu32, 0x63u32]) is None
        && media_type(seq![0x74u32, 0x2Fu32, 0x68u32, 0x3Bu32, 0x61u32, 0x3Du32, 0x22u32, 0x62u32]) is None
        && media_type(seq![0x74u32, 0x2Fu32, 0x68u32, 0x3Bu32, 0x61u32, 0x3Du32, 0x62u32, 0x3Bu32, 0x61u32, 0x3Du32, 0x63u32])->Some_0.parameters.len() == 2) by (compute_only);
}

/// The record a media type's value corresponds to.
pub open spec fn to_record(m: MediaType) -> MimeTypeRecord {
    MimeTypeRecord { type_: m.type_, subtype: m.subtype, parameters: m.parameters }
}

/// No parameter name appears twice. (Names are already case-folded, so
/// this compares them case-insensitively.)
pub open spec fn distinct_names(ps: Seq<(Seq<u32>, Seq<u32>)>) -> bool {
    forall|i: int, j: int| 0 <= i < j < ps.len() ==> (#[trigger] ps[i]).0 != (#[trigger] ps[j]).0
}

/// `tchar` is exactly the MIME Sniffing Standard's HTTP token code point
/// (as that standard's note says).
proof fn lemma_tchar(c: u32)
    ensures
        is_tchar(c) == is_http_token_code_point(c),
        is_tchar(c) ==> !is_http_whitespace(c) && c != 0x22 && c != 0x2F && c != 0x3B && c != 0x3D && c != 0x5C,
        is_tchar(c) ==> is_http_quoted_string_token_code_point(c),
        is_sp_or_htab(c) ==> is_http_whitespace(c) && c != 0x3B && c != 0x3D,
        is_qdtext(c) || is_quoted_pair_octet(c) ==> is_http_quoted_string_token_code_point(c),
        is_qdtext(c) ==> meets(Condition::NotQuotationMarkOrReverseSolidus, c),
{
}

/// Case folding is ASCII lowercase.
proof fn lemma_fold_case(s: Seq<u32>)
    ensures
        fold_case(s) == ascii_lowercase(s),
{
    assert(fold_case(s) =~= ascii_lowercase(s));
}

/// A run of `tchar`s is a run of HTTP token code points.
proof fn lemma_token_solely(s: Seq<u32>)
    requires
        forall|k: int| 0 <= k < s.len() ==> is_tchar(#[trigger] s[k]),
    ensures
        solely_http_token_code_points(s),
        solely_http_token_code_points(ascii_lowercase(s)),
        ascii_lowercase(s).len() == s.len(),
{
    assert forall|k: int| 0 <= k < s.len() implies is_http_token_code_point(#[trigger] s[k]) by {
        lemma_tchar(s[k]);
    }
    super::lemmas::lemma_solely_token(s);
    super::lemmas::lemma_ascii_lowercase(s);
}

/// The parameters read so far are a prefix of the result.
proof fn lemma_parameters_prefix(s: Seq<u32>, i: nat, acc: Seq<(Seq<u32>, Seq<u32>)>)
    ensures
        parameters(s, i, acc) matches Some(all) ==> acc.len() <= all.len() && all.subrange(0, acc.len() as int) == acc,
    decreases s.len() - i
{
    if i < s.len() {
        lemma_ows_end(s, i);
        let j = ows_end(s, i);
        if j < s.len() && s[j as int] == 0x3B {
            lemma_ows_end(s, j + 1);
            let k = ows_end(s, j + 1);
            if k < s.len() && is_tchar(s[k as int]) {
                lemma_tchars_end(s, k);
                let n = tchars_end(s, k);
                if n < s.len() && s[n as int] == 0x3D {
                    lemma_quoted_string_rest_position(s, n + 2, seq![]);
                    lemma_tchars_end(s, n + 1);
                    if let Some((value, e)) = parameter_value(s, n + 1) {
                        let name = s.subrange(k as int, n as int);
                        let acc2 = acc.push((fold_case(name), value));
                        lemma_parameters_prefix(s, e, acc2);
                        if let Some(all) = parameters(s, e, acc2) {
                            assert(all.subrange(0, acc.len() as int) =~= acc2.subrange(0, acc.len() as int));
                            assert(acc2.subrange(0, acc.len() as int) =~= acc);
                        }
                    }
                }
            } else {
                lemma_parameters_prefix(s, k, acc);
            }
        }
    } else {
        assert(acc.subrange(0, acc.len() as int) =~= acc);
    }
}

/// The value of a quoted string holds only HTTP quoted-string token code
/// points, and the string ends with a DQUOTE.
proof fn lemma_quoted_string_rest_value(s: Seq<u32>, i: nat, value: Seq<u32>)
    requires
        solely_http_quoted_string_token_code_points(value),
    ensures
        quoted_string_rest(s, i, value) matches Some((v, e)) ==> solely_http_quoted_string_token_code_points(v)
            && i < e <= s.len() && s[e - 1] == 0x22,
    decreases s.len() - i
{
    super::lemmas::lemma_solely_quoted_string_token(value);
    if i < s.len() && s[i as int] != 0x22 {
        let c = if s[i as int] == 0x5C { s[i as int + 1] } else { s[i as int] };
        let next = if s[i as int] == 0x5C { i + 2 } else { i + 1 };
        if (s[i as int] == 0x5C && i + 1 < s.len() && is_quoted_pair_octet(s[i as int + 1]))
            || (s[i as int] != 0x5C && is_qdtext(s[i as int]))
        {
            lemma_tchar(c);
            let v2 = value.push(c);
            assert forall|k: int| 0 <= k < v2.len() implies is_http_quoted_string_token_code_point(#[trigger] v2[k]) by {
                if k < value.len() {
                    assert(v2[k] == value[k]);
                }
            }
            super::lemmas::lemma_solely_quoted_string_token(v2);
            lemma_quoted_string_rest_value(s, next, v2);
        }
    }
}

/// On a quoted string that matches §5.6.4, Fetch's "collect an HTTP quoted
/// string" loop reads the same value and stops at the same place.
proof fn lemma_quoted_string_loop_agrees(s: Seq<u32>, l: nat, i: nat, value: Seq<u32>)
    requires
        l <= s.len(),
        forall|k: int| l <= k < s.len() ==> is_http_whitespace(#[trigger] s[k]),
        quoted_string_rest(s, i, value) is Some,
    ensures
        ({
            let (v, e) = quoted_string_rest(s, i, value)->Some_0;
            &&& e <= l
            &&& quoted_string_loop(s.subrange(0, l as int), i, value) == (v, e)
        }),
    decreases s.len() - i
{
    let t = s.subrange(0, l as int);
    let c = s[i as int];
    // Every code point the grammar reads is not whitespace except SP and
    // HTAB inside the quotes, which come before the closing DQUOTE, so all
    // of it lies before `l`.
    lemma_quoted_string_rest_value(s, i, seq![]);
    let nq = Condition::NotQuotationMarkOrReverseSolidus;
    if c == 0x22 {
        assert(i < l);
        assert(t[i as int] == 0x22);
        super::lemmas::lemma_collect_exact(nq, t, i, i);
        assert(t.subrange(i as int, i as int) =~= seq![]);
        assert(value + seq![] =~= value);
    } else if c == 0x5C {
        let d = s[i as int + 1];
        lemma_quoted_string_loop_agrees(s, l, i + 2, value.push(d));
        lemma_quoted_string_rest_position(s, i + 2, value.push(d));
        assert(i + 1 < l);
        assert(t[i as int] == 0x5C && t[i as int + 1] == d);
        super::lemmas::lemma_collect_exact(nq, t, i, i);
        assert(t.subrange(i as int, i as int) =~= seq![]);
        assert(value + seq![] =~= value);
    } else {
        lemma_tchar(c);
        lemma_quoted_string_loop_agrees(s, l, i + 1, value.push(c));
        lemma_quoted_string_rest_position(s, i + 1, value.push(c));
        assert(i < l);
        assert(t[i as int] == c);
        super::lemmas::lemma_quoted_string_loop_step(t, i, value);
    }
}

/// Where the WHATWG parser stands when the grammar is at `i` between
/// parameters: on the next ";", or at the end of the trimmed input.
pub open spec fn whatwg_position(s: Seq<u32>, l: nat, i: nat) -> nat {
    if i >= s.len() {
        l
    } else {
        ows_end(s, i)
    }
}

/// From `i`, where `parameters` succeeds, collecting code points that are
/// not ";" in the trimmed input `t` stops at [`whatwg_position`], and
/// everything between is SP or HTAB.
proof fn lemma_to_next_semicolon(s: Seq<u32>, l: nat, i: nat, acc: Seq<(Seq<u32>, Seq<u32>)>)
    requires
        l <= s.len(),
        forall|k: int| l <= k < s.len() ==> is_http_whitespace(#[trigger] s[k]),
        i <= l,
        i == s.len() ==> l == s.len(),
        parameters(s, i, acc) is Some,
    ensures
        whatwg_position(s, l, i) <= l,
        i <= whatwg_position(s, l, i),
        forall|k: int| i <= k < whatwg_position(s, l, i) ==> is_sp_or_htab(#[trigger] s[k]),
        whatwg_position(s, l, i) < l ==> s[whatwg_position(s, l, i) as int] == 0x3B,
        whatwg_position(s, l, i) == l ==> i == s.len(),
        collect(Condition::NotSemicolon, s.subrange(0, l as int), i)
            == (s.subrange(i as int, whatwg_position(s, l, i) as int), whatwg_position(s, l, i)),
{
    let t = s.subrange(0, l as int);
    let p = whatwg_position(s, l, i);
    if i < s.len() {
        lemma_ows_end(s, i);
        assert(s[p as int] == 0x3B);
        lemma_tchar(s[p as int]);
        assert(p < l);
    }
    assert forall|k: int| i <= k < p implies meets(Condition::NotSemicolon, #[trigger] t[k]) by {
        assert(t[k] == s[k]);
        lemma_tchar(s[k]);
    }
    super::lemmas::lemma_collect_exact(Condition::NotSemicolon, t, i, p);
    assert(t.subrange(i as int, p as int) =~= s.subrange(i as int, p as int));
}

/// The step 11 loop agrees with `parameters` from `i` on.
proof fn lemma_loop(
    s: Seq<u32>,
    l: nat,
    i: nat,
    acc: Seq<(Seq<u32>, Seq<u32>)>,
    all: Seq<(Seq<u32>, Seq<u32>)>,
    m: MimeTypeRecord,
)
    requires
        l <= s.len(),
        forall|k: int| l <= k < s.len() ==> is_http_whitespace(#[trigger] s[k]),
        i <= l,
        i == s.len() ==> l == s.len(),
        parameters(s, i, acc) == Some(all),
        distinct_names(all),
        m.parameters == acc,
    ensures
        parse_parameters(s.subrange(0, l as int), whatwg_position(s, l, i), m) == (MimeTypeRecord { parameters: all, ..m }),
    decreases s.len() - i
{
    let t = s.subrange(0, l as int);
    if i >= s.len() {
        assert(all == acc);
        return;
    }
    lemma_ows_end(s, i);
    let j = ows_end(s, i);
    assert(s[j as int] == 0x3B);
    lemma_tchar(s[j as int]);
    assert(j < l);
    assert(t[j as int] == 0x3B);
    lemma_ows_end(s, j + 1);
    let k = ows_end(s, j + 1);
    let ws = Condition::HttpWhitespace;
    let nse = Condition::NotSemicolonOrEqualsSign;
    if k >= s.len() {
        // ";" then only OWS: an empty parameter, and the end.
        assert(k == s.len());
        assert(parameters(s, k, acc) == Some(acc));
        assert(all == acc);
        assert forall|q: int| j + 1 <= q < l implies meets(ws, #[trigger] t[q]) by {
            assert(t[q] == s[q]);
            lemma_tchar(s[q]);
        }
        super::lemmas::lemma_collect_exact(ws, t, j + 1, l);
        super::lemmas::lemma_collect_exact(nse, t, l, l);
        return;
    }
    // From here on, k < s.len(), and s[k] is not SP or HTAB.
    assert(!is_sp_or_htab(s[k as int]));
    if !is_tchar(s[k as int]) {
        // [ parameter ] absent: the next repetition starts at k with ";".
        lemma_ows_end(s, k);
        assert(ows_end(s, k) == k);
        assert(s[k as int] == 0x3B);
        lemma_tchar(s[k as int]);
        assert(k < l);
        assert forall|q: int| j + 1 <= q < k implies meets(ws, #[trigger] t[q]) by {
            assert(t[q] == s[q]);
            lemma_tchar(s[q]);
        }
        assert(t[k as int] == 0x3B);
        super::lemmas::lemma_collect_exact(ws, t, j + 1, k);
        super::lemmas::lemma_collect_exact(nse, t, k, k);
        lemma_loop(s, l, k, acc, all, m);
        return;
    }
    // A parameter: name "=" value.
    lemma_tchar(s[k as int]);
    assert(k < l);
    lemma_tchars_end(s, k);
    let n = tchars_end(s, k);
    let name = s.subrange(k as int, n as int);
    assert(n < s.len() && s[n as int] == 0x3D);
    lemma_tchar(s[n as int]);
    assert(n < l);
    assert forall|q: int| j + 1 <= q < k implies meets(ws, #[trigger] t[q]) by {
        assert(t[q] == s[q]);
        lemma_tchar(s[q]);
    }
    assert(t[k as int] == s[k as int]);
    super::lemmas::lemma_collect_exact(ws, t, j + 1, k);
    assert forall|q: int| k <= q < n implies meets(nse, #[trigger] t[q]) by {
        assert(t[q] == s[q]);
        lemma_tchar(s[q]);
    }
    assert(t[n as int] == 0x3D);
    super::lemmas::lemma_collect_exact(nse, t, k, n);
    assert(t.subrange(k as int, n as int) =~= name);
    assert forall|q: int| 0 <= q < name.len() implies is_tchar(#[trigger] name[q]) by {
        assert(name[q] == s[k + q]);
    }
    lemma_token_solely(name);
    lemma_fold_case(name);
    let lname = fold_case(name);
    let (value, e) = parameter_value(s, n + 1)->Some_0;
    let acc2 = acc.push((lname, value));
    assert(parameters(s, e, acc2) == Some(all));
    // The name is new.
    lemma_parameters_prefix(s, e, acc2);
    assert(all[acc.len() as int] == acc2[acc.len() as int]);
    super::lemmas::lemma_map_exists(acc, lname);
    assert forall|q: int| 0 <= q < acc.len() implies (#[trigger] acc[q]).0 != lname by {
        assert(all[q] == acc2[q]);
        assert(acc2[q] == acc[q]);
    }
    super::lemmas::lemma_map_set_new(acc, lname, value);
    let m2 = MimeTypeRecord { parameters: acc2, ..m };
    if s[n as int + 1] == 0x22 {
        // A quoted-string value.
        lemma_quoted_string_rest_value(s, n + 2, seq![]);
        assert(n + 1 < l) by {
            lemma_tchar(s[n as int + 1]);
        }
        assert(t[n as int + 1] == 0x22);
        lemma_quoted_string_loop_agrees(s, l, n + 2, seq![]);
        lemma_parameters_prefix(s, e, acc2);
        lemma_to_next_semicolon(s, l, e, acc2);
        assert(set_parameter_if_valid(m, lname, value) == m2);
        lemma_loop(s, l, e, acc2, all, m2);
    } else {
        // A token value.
        lemma_tchars_end(s, n + 1);
        assert(n + 1 < e);
        lemma_tchar(s[n as int + 1]);
        assert(n + 1 < l);
        assert(t[n as int + 1] == s[n as int + 1]);
        assert(value == s.subrange(n as int + 1, e as int));
        // The value's last code point is a tchar, so e <= l.
        lemma_tchar(s[e - 1]);
        assert(e <= l);
        lemma_to_next_semicolon(s, l, e, acc2);
        let p = whatwg_position(s, l, e);
        assert forall|q: int| n + 1 <= q < e implies meets(Condition::NotSemicolon, #[trigger] t[q]) by {
            assert(t[q] == s[q]);
            lemma_tchar(s[q]);
        }
        super::lemmas::lemma_collect_exact(Condition::NotSemicolon, t, n + 1, p);
        // What it collects is the value, then SP and HTAB, which step
        // 11.9.2 removes.
        let raw = t.subrange(n as int + 1, p as int);
        let rest = s.subrange(e as int, p as int);
        assert(raw =~= value + rest);
        assert forall|q: int| 0 <= q < rest.len() implies is_http_whitespace(#[trigger] rest[q]) by {
            assert(rest[q] == s[e + q]);
            lemma_tchar(s[e + q]);
        }
        super::lemmas::lemma_remove_trailing_ws_suffix(value, rest);
        assert(value.last() == s[e - 1]);
        super::lemmas::lemma_trim_nothing(value);
        assert forall|q: int| 0 <= q < value.len() implies is_http_quoted_string_token_code_point(#[trigger] value[q]) by {
            assert(value[q] == s[n + 1 + q]);
            lemma_tchar(s[n + 1 + q]);
        }
        super::lemmas::lemma_solely_quoted_string_token(value);
        assert(set_parameter_if_valid(m, lname, value) == m2);
        lemma_loop(s, l, e, acc2, all, m2);
    }
}

/// **The two transcriptions agree on every string that matches RFC 9110's
/// `media-type` and has no parameter name twice** (case-insensitively):
/// parse a MIME type returns the same type, subtype and parameters.
pub proof fn lemma_equals_parse_a_mime_type(s: Seq<u32>)
    requires
        media_type(s) is Some,
        distinct_names(media_type(s)->Some_0.parameters),
    ensures
        parse_a_mime_type(s) == Some(to_record(media_type(s)->Some_0)),
{
    let mt = media_type(s)->Some_0;
    lemma_tchars_end(s, 0);
    let p = tchars_end(s, 0);
    let type_ = s.subrange(0, p as int);
    lemma_tchars_end(s, p + 1);
    let q = tchars_end(s, p + 1);
    let subtype = s.subrange(p as int + 1, q as int);
    // Step 1: s starts with a tchar; only trailing whitespace goes.
    lemma_tchar(s[0]);
    super::lemmas::lemma_remove_trailing_shape(s);
    let l = super::lemmas::content_end(s);
    let t = s.subrange(0, l as int);
    assert(remove_leading_http_whitespace(s) == s);
    assert(remove_leading_and_trailing_http_whitespace(s) == t);
    lemma_tchar(s[q - 1]);
    assert(q <= l);
    // Step 3: the type, up to "/".
    lemma_tchar(s[p as int]);
    assert(p < l);
    assert forall|k: int| 0 <= k < p implies meets(Condition::NotSolidus, #[trigger] t[k]) by {
        assert(t[k] == s[k]);
        lemma_tchar(s[k]);
    }
    assert(t[p as int] == 0x2F);
    super::lemmas::lemma_collect_exact(Condition::NotSolidus, t, 0, p);
    assert(t.subrange(0, p as int) =~= type_);
    assert forall|k: int| 0 <= k < type_.len() implies is_tchar(#[trigger] type_[k]) by {
        assert(type_[k] == s[k]);
    }
    lemma_token_solely(type_);
    // Step 7: the subtype, up to ";" or the end; step 8 removes the OWS.
    lemma_to_next_semicolon(s, l, q, seq![]);
    let w = whatwg_position(s, l, q);
    assert forall|k: int| p + 1 <= k < q implies meets(Condition::NotSemicolon, #[trigger] t[k]) by {
        assert(t[k] == s[k]);
        lemma_tchar(s[k]);
    }
    super::lemmas::lemma_collect_exact(Condition::NotSemicolon, t, p + 1, w);
    let raw = t.subrange(p as int + 1, w as int);
    let rest = s.subrange(q as int, w as int);
    assert(raw =~= subtype + rest);
    assert forall|k: int| 0 <= k < rest.len() implies is_http_whitespace(#[trigger] rest[k]) by {
        assert(rest[k] == s[q + k]);
        lemma_tchar(s[q + k]);
    }
    super::lemmas::lemma_remove_trailing_ws_suffix(subtype, rest);
    assert(subtype.last() == s[q - 1]);
    super::lemmas::lemma_trim_nothing(subtype);
    assert forall|k: int| 0 <= k < subtype.len() implies is_tchar(#[trigger] subtype[k]) by {
        assert(subtype[k] == s[p + 1 + k]);
    }
    lemma_token_solely(subtype);
    lemma_fold_case(type_);
    lemma_fold_case(subtype);
    // Step 11.
    let m0 = MimeTypeRecord { type_: fold_case(type_), subtype: fold_case(subtype), parameters: seq![] };
    lemma_loop(s, l, q, seq![], mt.parameters, m0);
}


/// A run of `tchar`s that ends at `q` is where [`tchars_end`] stops.
proof fn lemma_tchars_end_exact(s: Seq<u32>, i: nat, q: nat)
    requires
        i <= q <= s.len(),
        forall|k: int| i <= k < q ==> is_tchar(#[trigger] s[k]),
        q < s.len() ==> !is_tchar(s[q as int]),
    ensures
        tchars_end(s, i) == q,
    decreases q - i
{
    if i < q {
        lemma_tchars_end_exact(s, i + 1, q);
    }
}

/// `OWS` that is empty.
proof fn lemma_ows_end_none(s: Seq<u32>, i: nat)
    requires
        i < s.len() ==> !is_sp_or_htab(s[i as int]),
    ensures
        ows_end(s, i) == i,
{
}

/// The grammar's quoted string over an escaped value reads the value back.
proof fn lemma_quoted_string_rest_escaped(s: Seq<u32>, a: nat, acc: Seq<u32>, v: Seq<u32>)
    requires
        super::lemmas::holds_at(s, a as int, precede_quotes_and_backslashes(v) + seq![0x22u32]),
        solely_http_quoted_string_token_code_points(v),
    ensures
        quoted_string_rest(s, a, acc) == Some((acc + v, a + precede_quotes_and_backslashes(v).len() + 1)),
    decreases v.len()
{
    let esc = precede_quotes_and_backslashes(v);
    super::lemmas::lemma_holds_at_split(s, a as int, esc, seq![0x22u32]);
    super::lemmas::lemma_holds_at(s, a as int, esc);
    super::lemmas::lemma_holds_at(s, a + esc.len() as int, seq![0x22u32]);
    super::lemmas::lemma_solely_quoted_string_token(v);
    if v.len() == 0 {
        assert(seq![0x22u32][0] == 0x22);
        assert(acc + v =~= acc);
    } else {
        let c = v[0];
        let rest = v.drop_first();
        let esc_rest = precede_quotes_and_backslashes(rest);
        assert forall|k: int| 0 <= k < rest.len() implies is_http_quoted_string_token_code_point(#[trigger] rest[k]) by {
            assert(rest[k] == v[k + 1]);
        }
        super::lemmas::lemma_solely_quoted_string_token(rest);
        assert(is_http_quoted_string_token_code_point(v[0]));
        if c == 0x22 || c == 0x5C {
            assert(esc == seq![0x5Cu32, c] + esc_rest);
            assert(esc[0] == 0x5C && esc[1] == c);
            assert(esc + seq![0x22u32] =~= seq![0x5Cu32, c] + (esc_rest + seq![0x22u32]));
            super::lemmas::lemma_holds_at_split(s, a as int, seq![0x5Cu32, c], esc_rest + seq![0x22u32]);
            lemma_quoted_string_rest_escaped(s, a + 2, acc.push(c), rest);
        } else {
            assert(esc == seq![c] + esc_rest);
            assert(esc[0] == c);
            assert(esc + seq![0x22u32] =~= seq![c] + (esc_rest + seq![0x22u32]));
            super::lemmas::lemma_holds_at_split(s, a as int, seq![c], esc_rest + seq![0x22u32]);
            lemma_quoted_string_rest_escaped(s, a + 1, acc.push(c), rest);
        }
        assert(acc.push(c) + rest =~= acc + v);
    }
}

/// The grammar's `parameters` over serialized parameters from entry `i` on
/// reads exactly those parameters.
proof fn lemma_parameters_segments(s: Seq<u32>, ps: OrderedMap, i: nat)
    requires
        super::lemmas::parsed_parameters(ps),
        i <= ps.len(),
        super::lemmas::holds_at(s, s.len() - super::lemmas::segments(ps, i).len(), super::lemmas::segments(ps, i)),
    ensures
        parameters(s, (s.len() - super::lemmas::segments(ps, i).len()) as nat, ps.subrange(0, i as int)) == Some(ps),
    decreases ps.len() - i
{
    let segs = super::lemmas::segments(ps, i);
    let p = (s.len() - segs.len()) as nat;
    super::lemmas::lemma_segments_ends(ps, i);
    if i == ps.len() {
        assert(ps.subrange(0, i as int) =~= ps);
        return;
    }
    let (name, value) = ps[i as int];
    assert(super::lemmas::is_lowercase_token(ps[i as int].0));
    assert(solely_http_quoted_string_token_code_points(ps[i as int].1));
    let sv = serialize_value(value);
    let rest = super::lemmas::segments(ps, i + 1);
    let p_next = (s.len() - rest.len()) as nat;
    super::lemmas::lemma_segments_ends(ps, i + 1);
    super::lemmas::lemma_serialize_value_ends(value);
    super::lemmas::lemma_solely_token(name);
    let e = p + 1 + name.len();
    assert(segs == seq![0x3Bu32] + name + seq![0x3Du32] + sv + rest);
    super::lemmas::lemma_holds_at_split(s, p as int, seq![0x3Bu32] + name + seq![0x3Du32] + sv, rest);
    super::lemmas::lemma_holds_at_split(s, p as int, seq![0x3Bu32] + name + seq![0x3Du32], sv);
    super::lemmas::lemma_holds_at_split(s, p as int, seq![0x3Bu32] + name, seq![0x3Du32]);
    super::lemmas::lemma_holds_at_split(s, p as int, seq![0x3Bu32], name);
    super::lemmas::lemma_holds_at(s, p as int, seq![0x3Bu32]);
    super::lemmas::lemma_holds_at(s, p as int + 1, name);
    super::lemmas::lemma_holds_at(s, e as int, seq![0x3Du32]);
    super::lemmas::lemma_holds_at(s, e as int + 1, sv);
    assert(seq![0x3Bu32][0] == 0x3B && seq![0x3Du32][0] == 0x3D);
    assert(s[p as int] == 0x3B && s[e as int] == 0x3D);
    assert(p_next == e + 1 + sv.len());
    if rest.len() > 0 {
        super::lemmas::lemma_holds_at(s, p_next as int, rest);
        assert(s[p_next as int] == 0x3B);
    }
    // OWS ";" OWS, both OWS empty.
    lemma_ows_end_none(s, p);
    lemma_tchar(name[0]);
    assert(s[p as int + 1] == name[0]);
    lemma_ows_end_none(s, p + 1);
    // parameter-name
    assert forall|k: int| p + 1 <= k < e implies is_tchar(#[trigger] s[k]) by {
        assert(s[k] == name[k - p - 1]);
        lemma_tchar(name[k - p - 1]);
    }
    lemma_tchar(s[e as int]);
    lemma_tchars_end_exact(s, p + 1, e);
    assert(s.subrange(p as int + 1, e as int) =~= name);
    lemma_fold_case(name);
    let acc2 = ps.subrange(0, i as int + 1);
    assert(ps.subrange(0, i as int).push((name, value)) =~= acc2);
    if solely_http_token_code_points(value) && value.len() != 0 {
        // A token value.
        super::lemmas::lemma_solely_token(value);
        assert(sv == value);
        lemma_tchar(value[0]);
        assert(s[e as int + 1] == value[0]);
        assert forall|k: int| e + 1 <= k < p_next implies is_tchar(#[trigger] s[k]) by {
            assert(s[k] == value[k - e - 1]);
            lemma_tchar(value[k - e - 1]);
        }
        if p_next < s.len() {
            lemma_tchar(s[p_next as int]);
        }
        lemma_tchars_end_exact(s, e + 1, p_next);
        assert(s.subrange(e as int + 1, p_next as int) =~= value);
    } else {
        // A quoted value.
        let esc = precede_quotes_and_backslashes(value);
        assert(sv == seq![0x22u32] + (esc + seq![0x22u32]));
        super::lemmas::lemma_holds_at_split(s, e as int + 1, seq![0x22u32], esc + seq![0x22u32]);
        super::lemmas::lemma_holds_at(s, e as int + 1, seq![0x22u32]);
        assert(seq![0x22u32][0] == 0x22);
        assert(s[e as int + 1] == 0x22);
        lemma_quoted_string_rest_escaped(s, e + 2, seq![], value);
        assert(seq![] + value =~= value);
    }
    lemma_parameters_segments(s, ps, i + 1);
}

/// The grammar's `type "/" subtype` on a serialization reads back the
/// type and subtype, and leaves `parameters` at the parameters.
proof fn lemma_media_type_head(s: Seq<u32>, t: Seq<u32>, st: Seq<u32>, segs: Seq<u32>)
    requires
        s == t + seq![0x2Fu32] + st + segs,
        super::lemmas::is_lowercase_token(t),
        super::lemmas::is_lowercase_token(st),
        segs.len() > 0 ==> segs[0] == 0x3B,
    ensures
        media_type(s) == match parameters(s, (t.len() + 1 + st.len()) as nat, seq![]) {
            Some(ps) => Some(MediaType { type_: t, subtype: st, parameters: ps }),
            None => None,
        },
{
    let head = t + seq![0x2Fu32] + st;
    let h = head.len();
    super::lemmas::lemma_solely_token(t);
    super::lemmas::lemma_solely_token(st);
    assert(super::lemmas::holds_at(s, 0, head + segs)) by {
        assert(s.subrange(0, s.len() as int) =~= s);
    }
    super::lemmas::lemma_holds_at_split(s, 0, head, segs);
    super::lemmas::lemma_holds_at_split(s, 0, t + seq![0x2Fu32], st);
    super::lemmas::lemma_holds_at_split(s, 0, t, seq![0x2Fu32]);
    super::lemmas::lemma_holds_at(s, 0, t);
    super::lemmas::lemma_holds_at(s, t.len() as int, seq![0x2Fu32]);
    super::lemmas::lemma_holds_at(s, t.len() as int + 1, st);
    assert(seq![0x2Fu32][0] == 0x2F);
    assert(s[t.len() as int] == 0x2F);
    assert forall|k: int| 0 <= k < t.len() implies is_tchar(#[trigger] s[k]) by {
        assert(s[k] == t[k]);
        lemma_tchar(t[k]);
    }
    lemma_tchar(s[t.len() as int]);
    lemma_tchars_end_exact(s, 0, t.len());
    assert(s.subrange(0, t.len() as int) =~= t);
    assert forall|k: int| t.len() + 1 <= k < h implies is_tchar(#[trigger] s[k]) by {
        assert(s[k] == st[k - t.len() - 1]);
        lemma_tchar(st[k - t.len() - 1]);
    }
    if segs.len() > 0 {
        super::lemmas::lemma_holds_at(s, h as int, segs);
        assert(s[h as int] == 0x3B);
        lemma_tchar(s[h as int]);
    }
    lemma_tchars_end_exact(s, t.len() + 1, h);
    assert(s.subrange(t.len() as int + 1, h as int) =~= st);
    lemma_fold_case(t);
    lemma_fold_case(st);
}

/// **Every serialization of a parsed record is a valid MIME type string**
/// (it matches RFC 9110's `media-type`), and denotes that record.
pub proof fn lemma_serialize_is_media_type(m: MimeTypeRecord)
    requires
        super::lemmas::parsed_form(m),
    ensures
        media_type(serialize_a_mime_type(m)) is Some,
        to_record(media_type(serialize_a_mime_type(m))->Some_0) == m,
{
    let t = m.type_;
    let st = m.subtype;
    let ps = m.parameters;
    let head = t + seq![0x2Fu32] + st;
    let segs = super::lemmas::segments(ps, 0);
    let s = serialize_a_mime_type(m);
    super::lemmas::lemma_serialize_parameters(ps, 0, head);
    assert(s == head + segs);
    super::lemmas::lemma_segments_ends(ps, 0);
    lemma_media_type_head(s, t, st, segs);
    assert(super::lemmas::holds_at(s, s.len() - segs.len(), segs)) by {
        assert(s.subrange(head.len() as int, s.len() as int) =~= segs);
    }
    assert(ps.subrange(0, 0) =~= seq![]);
    lemma_parameters_segments(s, ps, 0);
}

} // verus!
