//! Contracts the executable decoder and encoder must be proven to meet.
//! Each exec function's `ensures` clause is exactly one of these
//! predicates, so reviewing these (and [`super::spec`]) is enough to know
//! what the implementation guarantees.
//!
//! Strings are `u32` code points, as in `clazel-encoding`'s UTF-8 decoder
//! (whose output this decoder can take directly): vstd has no
//! specification for any safe `u32` to `char` conversion, and supplying one
//! would need `assume_specification`, which expands to `unsafe` code
//! (CLAUDE.md rules 1 and 4). The encoder's output is a string too, so
//! `decode(&encode(bytes))` type-checks; every value in it is ASCII
//! (`lemmas::lemma_encode_ascii`).

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Contract for `decode(&[u32]) -> Option<Vec<u8>>`: `None` exactly when
/// "forgiving-base64 decode" returns failure, and the same bytes otherwise.
pub open spec fn decode_ensures(input: Seq<u32>, output: Option<Seq<u8>>) -> bool {
    output == forgiving_base64_decode(input)
}

/// Contract for `encode(&[u8]) -> Vec<u32>`: equals "forgiving-base64
/// encode". There is no precondition: every byte sequence can be encoded.
pub open spec fn encode_ensures(input: Seq<u8>, output: Seq<u32>) -> bool {
    output == forgiving_base64_encode(input)
}

} // verus!
