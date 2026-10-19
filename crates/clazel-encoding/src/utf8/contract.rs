//! Contracts the executable UTF-8 decoder must be proven to meet. Each
//! exec function's `ensures` clause will be exactly one of these
//! predicates, so reviewing these (and [`super::spec`]) is enough to know
//! what the implementation guarantees.
//!
//! Output is `char`, which Rust guarantees is a scalar value. That this
//! is achievable at all follows from `lemmas::lemma_hooks_scalar`.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The code point values of a sequence of `char`s.
pub open spec fn code_points(s: Seq<char>) -> Seq<u32> {
    s.map_values(|c: char| c as u32)
}

/// Contract for `decode(&[u8]) -> Vec<char>`: equals "UTF-8 decode"
/// (BOM stripped, errors replaced with U+FFFD).
pub open spec fn decode_ensures(input: Seq<u8>, output: Seq<char>) -> bool {
    code_points(output) == utf8_decode(input)
}

/// Contract for `decode_without_bom(&[u8]) -> Vec<char>`.
pub open spec fn decode_without_bom_ensures(input: Seq<u8>, output: Seq<char>) -> bool {
    code_points(output) == utf8_decode_without_bom(input)
}

/// Contract for `decode_without_bom_or_fail(&[u8]) -> Option<Vec<char>>`:
/// `None` exactly when the standard returns failure, and the same output
/// otherwise.
pub open spec fn decode_without_bom_or_fail_ensures(input: Seq<u8>, output: Option<Seq<char>>) -> bool {
    match (output, utf8_decode_without_bom_or_fail(input)) {
        (Some(out), Some(expected)) => code_points(out) == expected,
        (None, None) => true,
        _ => false,
    }
}

} // verus!
