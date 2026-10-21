//! Contracts the executable CBOR codec must be proven to meet. Each exec
//! function's `ensures` clause is exactly one of these predicates, so
//! reviewing these (and [`super::spec`]) is enough to know what the
//! implementation guarantees.
//!
//! An item is its token sequence (see the modelling choices in
//! [`super::spec`]): the exec type is `Vec<Token>` where `Token` is the
//! exec twin of the spec's `Token`, and its view is the spec token.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Contract for `decode(&[u8]) -> Option<Vec<Token>>`: `None` exactly when
/// the bytes are not the preferred serialization of one data item of the
/// profile, and the item's tokens otherwise.
pub open spec fn decode_ensures(input: Seq<u8>, output: Option<Seq<Token>>) -> bool {
    output == decode(input)
}

/// Precondition of `encode(&[Token]) -> Vec<u8>`: the tokens are one data
/// item of the profile (text strings valid UTF-8, every array followed by
/// exactly its elements).
pub open spec fn encode_requires(item: Seq<Token>) -> bool {
    is_item(item)
}

/// Contract for `encode(&[Token]) -> Vec<u8>`: the preferred serialization
/// of the item.
pub open spec fn encode_ensures(item: Seq<Token>, output: Seq<u8>) -> bool {
    output == encode(item)
}

} // verus!
