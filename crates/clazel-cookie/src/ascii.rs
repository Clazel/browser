//! String definitions shared by the cookie specs: ASCII classes, the
//! case-insensitive match, and the whitespace strip, over octet strings.
//!
//! Sources (pinned as in the other specs of this crate):
//! - RFC 6265bis draft 22 §2.3: "Two sequences of octets are said to
//!   case-insensitively match each other if and only if they are equivalent
//!   under the i;ascii-casemap collation defined in [RFC4790]." That
//!   collation compares after mapping every ASCII letter to one case, so
//!   equal lowercase forms are the same relation.
//! - RFC 5234 appendix B.1: DIGIT is %x30-39, ALPHA is %x41-5A / %x61-7A,
//!   WSP is SP / HTAB.
//!
//! A cookie string is a `Seq<u8>`: RFC 6265bis §2.3 says "The term string
//! means a sequence of non-NUL octets", and every algorithm reads octets.

#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// DIGIT (RFC 5234 B.1): %x30-39.
pub open spec fn is_digit(c: u8) -> bool {
    0x30 <= c <= 0x39
}

/// ALPHA (RFC 5234 B.1): %x41-5A / %x61-7A.
pub open spec fn is_alpha(c: u8) -> bool {
    (0x41 <= c <= 0x5A) || (0x61 <= c <= 0x7A)
}

/// WSP (RFC 5234 B.1): SP / HTAB.
pub open spec fn is_wsp(c: u8) -> bool {
    c == 0x20 || c == 0x09
}

/// The ASCII lowercase of one octet: A-Z become a-z, others are unchanged.
pub open spec fn ascii_lowercase_octet(c: u8) -> u8 {
    if 0x41 <= c <= 0x5A { (c + 0x20) as u8 } else { c }
}

/// The ASCII lowercase of a string.
pub open spec fn ascii_lowercase(s: Seq<u8>) -> Seq<u8> {
    s.map_values(|c: u8| ascii_lowercase_octet(c))
}

/// "case-insensitively match" (RFC 6265bis §2.3, i;ascii-casemap).
pub open spec fn case_insensitive_match(a: Seq<u8>, b: Seq<u8>) -> bool {
    ascii_lowercase(a) == ascii_lowercase(b)
}

/// "begins with a case-insensitive match for the string" `prefix`
/// (RFC 6265bis §5.7 steps 20 to 22).
pub open spec fn begins_with_case_insensitive_match(s: Seq<u8>, prefix: Seq<u8>) -> bool {
    s.len() >= prefix.len() && case_insensitive_match(s.subrange(0, prefix.len() as int), prefix)
}

/// Remove any leading WSP characters (RFC 6265bis §5.6 steps 4 and 5).
pub open spec fn remove_leading_wsp(s: Seq<u8>) -> Seq<u8>
    decreases s.len()
{
    if s.len() > 0 && is_wsp(s[0]) { remove_leading_wsp(s.skip(1)) } else { s }
}

/// Remove any trailing WSP characters (RFC 6265bis §5.6 steps 4 and 5).
pub open spec fn remove_trailing_wsp(s: Seq<u8>) -> Seq<u8>
    decreases s.len()
{
    if s.len() > 0 && is_wsp(s[s.len() - 1]) { remove_trailing_wsp(s.drop_last()) } else { s }
}

/// Remove any leading or trailing WSP characters.
pub open spec fn remove_leading_and_trailing_wsp(s: Seq<u8>) -> Seq<u8> {
    remove_trailing_wsp(remove_leading_wsp(s))
}

/// The number a string of ASCII digits denotes, in base 10 ("the numbers
/// denoted by the digits"). Non-digits are not looked at.
pub open spec fn digits_value(s: Seq<u8>) -> nat
    decreases s.len()
{
    if s.len() == 0 { 0 } else { digits_value(s.drop_last()) * 10 + ((s[s.len() - 1] - 0x30) as nat) }
}

/// The index of the first `c` in `s` at or after `from`, or `s.len()` if
/// there is none.
pub open spec fn find_octet(s: Seq<u8>, c: u8, from: nat) -> nat
    decreases s.len() - from
{
    if from >= s.len() { s.len() } else if s[from as int] == c { from } else { find_octet(s, c, from + 1) }
}

} // verus!
