//! Contracts the executable Punycode decoder and encoder must be proven to
//! meet. Each exec function's `ensures` clause is exactly one of these
//! predicates, so reviewing these (and [`super::spec`]) is enough to know
//! what the implementation guarantees.
//!
//! Strings are `u32` code points, as in `clazel-encoding`: vstd has no
//! specification for any safe `u32` to `char` conversion, and supplying one
//! would need `assume_specification`, which expands to `unsafe` code
//! (CLAUDE.md rules 1 and 4). The decoder can produce any value up to
//! `maxint`, including ones that are not scalar values; UTS #46 rejects
//! those in its validity criteria.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Contract for `decode(&[u32]) -> Option<Vec<u32>>`: `None` exactly when
/// RFC 3492 §6.2 fails, and the same code points otherwise.
pub open spec fn decode_ensures(input: Seq<u32>, output: Option<Seq<u32>>) -> bool {
    output == punycode_decode(input)
}

/// Contract for `encode(&[u32]) -> Option<Vec<u32>>`: `None` exactly when
/// RFC 3492 §6.3 fails (on overflow), and the same code points otherwise.
pub open spec fn encode_ensures(input: Seq<u32>, output: Option<Seq<u32>>) -> bool {
    output == punycode_encode(input)
}

} // verus!
