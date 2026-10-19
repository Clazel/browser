//! Contracts the executable UTF-8 decoder and encoder must be proven to
//! meet. Each exec function's `ensures` clause is exactly one of these predicates, so
//! reviewing these (and [`super::spec`]) is enough to know what the
//! implementation guarantees.
//!
//! Output is code points as `u32`, not `char`. vstd has no specification
//! for `char::from_u32` (or any other safe `u32` to `char` conversion), and
//! supplying one would need `assume_specification`, which expands to
//! `unsafe` code (CLAUDE.md rules 1 and 4). Nothing is lost: every output
//! value is a Unicode scalar value (`lemmas::lemma_hooks_scalar`), so a
//! caller's `char::from_u32` never returns `None`.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Contract for `decode(&[u8]) -> Vec<u32>`: equals "UTF-8 decode"
/// (BOM stripped, errors replaced with U+FFFD).
pub open spec fn decode_ensures(input: Seq<u8>, output: Seq<u32>) -> bool {
    output == utf8_decode(input)
}

/// Contract for `decode_without_bom(&[u8]) -> Vec<u32>`.
pub open spec fn decode_without_bom_ensures(input: Seq<u8>, output: Seq<u32>) -> bool {
    output == utf8_decode_without_bom(input)
}

/// Contract for `decode_without_bom_or_fail(&[u8]) -> Option<Vec<u32>>`:
/// `None` exactly when the standard returns failure, and the same output
/// otherwise.
pub open spec fn decode_without_bom_or_fail_ensures(input: Seq<u8>, output: Option<Seq<u32>>) -> bool {
    output == utf8_decode_without_bom_or_fail(input)
}

/// Precondition of `encode(&[u32]) -> Vec<u8>`: the input is "an I/O queue
/// of scalar values" (§6 UTF-8 encode), so §4.1 process an item step 3's
/// assertion ("item is not a surrogate") holds. This is the same type the
/// decoder outputs (`lemmas::lemma_hooks_scalar`).
pub open spec fn encode_requires(input: Seq<u32>) -> bool {
    all_scalar_values(input)
}

/// Contract for `encode(&[u32]) -> Vec<u8>`: equals "UTF-8 encode".
pub open spec fn encode_ensures(input: Seq<u32>, output: Seq<u8>) -> bool {
    output == utf8_encode(input)
}

} // verus!
