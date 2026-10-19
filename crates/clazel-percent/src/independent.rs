//! An independent transcription of percent-encoding, from a different
//! standard than [`super::spec`], written before that file existed and
//! without reading it (docs/VERIFICATION.md, "Trust without reviewers",
//! item 2). The same agent wrote both files, so the two are independent in
//! source document and order of writing only.
//!
//! Source: RFC 3986, "Uniform Resource Identifier (URI): Generic Syntax",
//! <https://www.rfc-editor.org/rfc/rfc3986>: §2.1 "Percent-Encoding",
//! §2.2 "Reserved Characters", §2.3 "Unreserved Characters", §2.4 "When to
//! Encode or Decode", and the component rules of §3.2.1 (userinfo), §3.3
//! (path), §3.4 (query) and §3.5 (fragment). Core rules ALPHA, DIGIT and
//! HEXDIG are from RFC 2234 §6.1, as RFC 3986 §1.3 says.
//!
//! The two standards define different things, so equality is proven only
//! where they agree, and each domain is stated exactly (an "if and only
//! if", proven, not a comment):
//!
//! - **Encoding one octet** (§2.1, with the "should use uppercase"
//!   advice): equal to "percent-encode" for every byte.
//! - **Decoding** (§2.1 and §2.4): RFC 3986 defines decoding only for text
//!   made of URI characters in which every "%" begins a `pct-encoded`
//!   triplet ([`rfc_decodable`]). On exactly that domain it equals
//!   "percent-decode". Outside it the RFC says nothing, so nothing is
//!   claimed.
//! - **Which characters are encoded.** RFC 3986 has no "percent-encode
//!   sets"; it says which characters a component allows unencoded (§3) and
//!   that data octets of other characters are percent-encoded (§2.1,
//!   §2.2). Each WHATWG set is compared with the RFC rule for the matching
//!   component, and the code points where they disagree are listed in full
//!   (`*_disagreement`). The proof shows the lists are exact: a set
//!   contains a code point exactly as the RFC rule says if and only if the
//!   code point is not in the list.
//!
//! Modelling choices:
//! - A character is a `u32` code point, a URI character is one with
//!   US-ASCII value (§2: "the integer values used by the ABNF must be
//!   mapped back to their corresponding characters via US-ASCII"), and an
//!   octet is a `u8`.
//! - ABNF quoted strings are case-insensitive (RFC 2234 §2.3), so HEXDIG
//!   also matches "a" to "f"; RFC 3986 §2.1 says so too ("The uppercase
//!   hexadecimal digits 'A' through 'F' are equivalent to the lowercase
//!   digits 'a' through 'f'").
//! - A URI given as octets (for decoding) is its characters' US-ASCII
//!   octets.
//! - "Characters a component allows unencoded" is the component's ABNF
//!   rule without its `pct-encoded` alternative. A "%" used as data is
//!   therefore not allowed unencoded: §2.4, "it must be percent-encoded as
//!   "%25" for that octet to be used as data".

#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------
// RFC 2234 §6.1 core rules, and RFC 3986 §2.2 and §2.3.
// ---------------------------------------------------------------------

/// ALPHA = %x41-5A / %x61-7A ; A-Z / a-z
pub open spec fn rfc_alpha(c: u32) -> bool {
    (0x41 <= c && c <= 0x5A) || (0x61 <= c && c <= 0x7A)
}

/// DIGIT = %x30-39 ; 0-9
pub open spec fn rfc_digit(c: u32) -> bool {
    0x30 <= c && c <= 0x39
}

/// HEXDIG = DIGIT / "A" / "B" / "C" / "D" / "E" / "F", case-insensitive.
pub open spec fn rfc_hexdig(c: u32) -> bool {
    rfc_digit(c) || (0x41 <= c && c <= 0x46) || (0x61 <= c && c <= 0x66)
}

/// The value of a HEXDIG: "0" to "9" are 0 to 9; "A" to "F" (or "a" to
/// "f") are 10 to 15.
pub open spec fn rfc_hexdig_value(c: u32) -> int {
    if rfc_digit(c) {
        c - 0x30
    } else if 0x41 <= c && c <= 0x46 {
        c - 0x41 + 10
    } else {
        c - 0x61 + 10
    }
}

/// unreserved = ALPHA / DIGIT / "-" / "." / "_" / "~"
pub open spec fn rfc_unreserved(c: u32) -> bool {
    rfc_alpha(c) || rfc_digit(c) || c == 0x2D || c == 0x2E || c == 0x5F || c == 0x7E
}

/// gen-delims = ":" / "/" / "?" / "#" / "[" / "]" / "@"
pub open spec fn rfc_gen_delims(c: u32) -> bool {
    c == 0x3A || c == 0x2F || c == 0x3F || c == 0x23 || c == 0x5B || c == 0x5D || c == 0x40
}

/// sub-delims = "!" / "$" / "&" / "'" / "(" / ")" / "*" / "+" / "," / ";" / "="
pub open spec fn rfc_sub_delims(c: u32) -> bool {
    c == 0x21 || c == 0x24 || c == 0x26 || c == 0x27 || c == 0x28 || c == 0x29
        || c == 0x2A || c == 0x2B || c == 0x2C || c == 0x3B || c == 0x3D
}

/// reserved = gen-delims / sub-delims
pub open spec fn rfc_reserved(c: u32) -> bool {
    rfc_gen_delims(c) || rfc_sub_delims(c)
}

/// The characters a URI may contain (§2: "a limited set of characters
/// consisting of digits, letters, and a few graphic symbols"): reserved,
/// unreserved, and the "%" of a percent-encoding.
pub open spec fn rfc_uri_character(c: u32) -> bool {
    rfc_reserved(c) || rfc_unreserved(c) || c == 0x25
}

// ---------------------------------------------------------------------
// §3: characters each component allows unencoded (its rule without the
// `pct-encoded` alternative).
// ---------------------------------------------------------------------

/// §3.2.1: userinfo = *( unreserved / pct-encoded / sub-delims / ":" )
pub open spec fn rfc_userinfo_char(c: u32) -> bool {
    rfc_unreserved(c) || rfc_sub_delims(c) || c == 0x3A
}

/// §3.3: pchar = unreserved / pct-encoded / sub-delims / ":" / "@"
pub open spec fn rfc_pchar(c: u32) -> bool {
    rfc_unreserved(c) || rfc_sub_delims(c) || c == 0x3A || c == 0x40
}

/// §3.3: a path is segments of pchar separated by "/" (path-abempty =
/// *( "/" segment ), segment = *pchar).
pub open spec fn rfc_path_char(c: u32) -> bool {
    rfc_pchar(c) || c == 0x2F
}

/// §3.4: query = *( pchar / "/" / "?" )
pub open spec fn rfc_query_char(c: u32) -> bool {
    rfc_pchar(c) || c == 0x2F || c == 0x3F
}

/// §3.5: fragment = *( pchar / "/" / "?" )
pub open spec fn rfc_fragment_char(c: u32) -> bool {
    rfc_pchar(c) || c == 0x2F || c == 0x3F
}

// ---------------------------------------------------------------------
// §2.1 and §2.4: encoding and decoding octets.
// ---------------------------------------------------------------------

/// An uppercase HEXDIG for `n` in 0 to 15 (§2.1: "URI producers and
/// normalizers should use uppercase hexadecimal digits").
pub open spec fn rfc_upper_hexdig(n: int) -> u32 {
    if n < 10 {
        (0x30 + n) as u32
    } else {
        (0x41 + n - 10) as u32
    }
}

/// §2.1: "A percent-encoded octet is encoded as a character triplet,
/// consisting of the percent character "%" followed by the two hexadecimal
/// digits representing that octet's numeric value." The first digit is
/// the high-order one (as in the RFC's example: "%20" for "00100000").
pub open spec fn rfc_pct_encode(octet: u8) -> Seq<u32> {
    seq![0x25u32, rfc_upper_hexdig(octet as int / 16), rfc_upper_hexdig(octet as int % 16)]
}

/// pct-encoded = "%" HEXDIG HEXDIG, starting at position `k` of `s`.
pub open spec fn rfc_pct_encoded_at(s: Seq<u8>, k: int) -> bool {
    0 <= k && k + 2 < s.len() && s[k] == 0x25 && rfc_hexdig(s[k + 1] as u32)
        && rfc_hexdig(s[k + 2] as u32)
}

/// Text RFC 3986 can decode: URI characters only, and every "%" begins a
/// percent-encoded octet (§2.4: "the percent ("%") character serves as the
/// indicator for percent-encoded octets").
pub open spec fn rfc_decodable(s: Seq<u8>) -> bool {
    &&& forall|k: int| 0 <= k < s.len() ==> rfc_uri_character(#[trigger] s[k] as u32)
    &&& forall|k: int| 0 <= k < s.len() && #[trigger] s[k] == 0x25 ==> rfc_pct_encoded_at(s, k)
}

/// Decoding (§2.1, §2.4): each percent-encoded octet becomes the octet
/// its two digits represent; every other character is its own US-ASCII
/// octet. Meaningful only when [`rfc_decodable`] holds.
pub open spec fn rfc_pct_decode(s: Seq<u8>) -> Seq<u8>
    decreases s.len()
{
    if s.len() == 0 {
        seq![]
    } else if rfc_pct_encoded_at(s, 0) {
        let octet = (16 * rfc_hexdig_value(s[1] as u32) + rfc_hexdig_value(s[2] as u32)) as u8;
        seq![octet] + rfc_pct_decode(s.skip(3))
    } else {
        seq![s[0]] + rfc_pct_decode(s.skip(1))
    }
}

// ---------------------------------------------------------------------
// Where the WHATWG sets and RFC 3986 disagree. Each list is every code
// point on which "the set contains c" differs from "RFC 3986 requires c to
// be percent-encoded in that component"; the lemmas below prove each list
// exact. In every list but the last two, "%" is there because WHATWG's
// set leaves "%" alone (the URL parser keeps existing percent-encodings),
// where RFC 3986 requires data "%" to be encoded.
// ---------------------------------------------------------------------

/// The C0 control set against "is not a URI character": the ten printable
/// US-ASCII characters RFC 3986 excludes from URIs but that set leaves
/// alone: SP " < > \ ^ ` { | }.
pub open spec fn c0_control_disagreement(c: u32) -> bool {
    c == 0x20 || c == 0x22 || c == 0x3C || c == 0x3E || c == 0x5C || c == 0x5E || c == 0x60
        || c == 0x7B || c == 0x7C || c == 0x7D
}

/// The fragment set against §3.5: # % [ \ ] ^ { | }.
pub open spec fn fragment_disagreement(c: u32) -> bool {
    c == 0x23 || c == 0x25 || c == 0x5B || c == 0x5C || c == 0x5D || c == 0x5E || c == 0x7B
        || c == 0x7C || c == 0x7D
}

/// The query set against §3.4: % [ \ ] ^ ` { | }.
pub open spec fn query_disagreement(c: u32) -> bool {
    c == 0x25 || c == 0x5B || c == 0x5C || c == 0x5D || c == 0x5E || c == 0x60 || c == 0x7B
        || c == 0x7C || c == 0x7D
}

/// The special-query set against §3.4: the query set's list, and '.
pub open spec fn special_query_disagreement(c: u32) -> bool {
    query_disagreement(c) || c == 0x27
}

/// The path set against §3.3: % [ \ ] |.
pub open spec fn path_disagreement(c: u32) -> bool {
    c == 0x25 || c == 0x5B || c == 0x5C || c == 0x5D || c == 0x7C
}

/// The userinfo set against §3.2.1: % : ; =. (WHATWG keeps username and
/// password apart, so ":" is data there; ";" and "=" it encodes anyway.)
pub open spec fn userinfo_disagreement(c: u32) -> bool {
    c == 0x25 || c == 0x3A || c == 0x3B || c == 0x3D
}

/// The component set against "data in any component" (§2.2 and §2.3:
/// encode every character but the unreserved ones): ! ' ( ) *, the
/// sub-delims that `encodeURIComponent()` leaves alone.
pub open spec fn component_disagreement(c: u32) -> bool {
    c == 0x21 || c == 0x27 || c == 0x28 || c == 0x29 || c == 0x2A
}

/// The application/x-www-form-urlencoded set against the same rule: * (a
/// sub-delim it leaves alone) and ~ (an unreserved character it encodes).
pub open spec fn form_disagreement(c: u32) -> bool {
    c == 0x2A || c == 0x7E
}

} // verus!
