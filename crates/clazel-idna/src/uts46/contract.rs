//! Contracts the executable UTS #46 functions must be proven to meet. Each
//! exec function's `ensures` clause is exactly one of these predicates, so
//! reviewing these (and [`super::spec`]) is enough to know what the
//! implementation guarantees, relative to the tables in [`super::data`].
//!
//! Strings are `u32` code points, as in the rest of the workspace. Flags
//! are [`super::spec::Flags`], which executable code can hold too.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Contract for `nfc(&[u32]) -> Vec<u32>`: Normalization Form C.
pub open spec fn nfc_ensures(input: Seq<u32>, output: Seq<u32>) -> bool {
    output == nfc(input)
}

/// Contract for `to_ascii(&[u32], Flags, bool) -> Option<Vec<u32>>`: UTS #46
/// ToASCII, `None` for a failure value.
pub open spec fn to_ascii_ensures(input: Seq<u32>, flags: Flags, verify_dns_length: bool, output: Option<Seq<u32>>) -> bool {
    output == to_ascii(input, flags, verify_dns_length)
}

/// Contract for `to_unicode(&[u32], Flags) -> (Vec<u32>, bool)`: UTS #46
/// ToUnicode, the string and whether an error was recorded.
pub open spec fn to_unicode_ensures(input: Seq<u32>, flags: Flags, output: Seq<u32>, error: bool) -> bool {
    (output, error) == to_unicode(input, flags)
}

/// Contract for `domain_parser_to_ascii(&[u32], bool) -> Option<Vec<u32>>`
/// (URL §3.3 "domain parser ToASCII").
pub open spec fn domain_parser_to_ascii_ensures(input: Seq<u32>, be_strict: bool, output: Option<Seq<u32>>) -> bool {
    output == domain_parser_to_ascii(input, be_strict)
}

/// Contract for `domain_parser(&[u32], bool) -> Option<Vec<u32>>` (URL §3.3
/// "domain parser"), `None` for failure.
pub open spec fn domain_parser_ensures(input: Seq<u32>, be_strict: bool, output: Option<Seq<u32>>) -> bool {
    output == domain_parser(input, be_strict)
}

/// Contract for `domain_to_unicode(&[u32]) -> Vec<u32>` (URL §3.3 "domain
/// to Unicode").
pub open spec fn domain_to_unicode_ensures(input: Seq<u32>, output: Seq<u32>) -> bool {
    output == domain_to_unicode(input)
}

} // verus!
