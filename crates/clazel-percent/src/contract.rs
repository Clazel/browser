//! Contracts the executable percent-encoding functions must be proven to
//! meet. Each exec function's `ensures` clause is exactly one of these
//! predicates (and its `requires`, where it has one), so reviewing these
//! and [`super::spec`] is enough to know what the implementation
//! guarantees.
//!
//! Strings are code points as `u32`, as in `clazel-encoding` (see its
//! `utf8/contract.rs` for why not `char`). Inputs that the standard types
//! as scalar value strings are required to hold only scalar values.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Contract for `percent_encode(u8) -> Vec<u32>`: equals "percent-encode".
pub open spec fn percent_encode_ensures(byte: u8, output: Seq<u32>) -> bool {
    output == percent_encode(byte)
}

/// Contract for `percent_decode(&[u8]) -> Vec<u8>`: equals "percent-decode"
/// a byte sequence.
pub open spec fn percent_decode_ensures(input: Seq<u8>, output: Seq<u8>) -> bool {
    output == percent_decode(input)
}

/// Precondition of `percent_decode_string(&[u32]) -> Vec<u8>`: the input
/// is a scalar value string.
pub open spec fn percent_decode_string_requires(input: Seq<u32>) -> bool {
    clazel_encoding::utf8::spec::all_scalar_values(input)
}

/// Contract for `percent_decode_string(&[u32]) -> Vec<u8>`: equals
/// "percent-decode" a scalar value string.
pub open spec fn percent_decode_string_ensures(input: Seq<u32>, output: Seq<u8>) -> bool {
    output == percent_decode_string(input)
}

/// Contract for `PercentEncodeSet::contains(self, u32) -> bool`: membership
/// in the named set.
pub open spec fn contains_ensures(set: PercentEncodeSet, c: u32, result: bool) -> bool {
    result == contains(set, c)
}

/// Precondition of `utf8_percent_encode_code_point(u32, PercentEncodeSet)`:
/// the input is a scalar value.
pub open spec fn utf8_percent_encode_code_point_requires(scalar_value: u32) -> bool {
    clazel_encoding::utf8::spec::is_scalar_value(scalar_value)
}

/// Contract for `utf8_percent_encode_code_point(u32, PercentEncodeSet) ->
/// Vec<u32>`: equals "UTF-8 percent-encode" a scalar value.
pub open spec fn utf8_percent_encode_code_point_ensures(
    scalar_value: u32,
    set: PercentEncodeSet,
    output: Seq<u32>,
) -> bool {
    output == utf8_percent_encode_code_point(scalar_value, set)
}

/// Precondition of `utf8_percent_encode(&[u32], PercentEncodeSet)`: the
/// input is a scalar value string.
pub open spec fn utf8_percent_encode_requires(input: Seq<u32>) -> bool {
    clazel_encoding::utf8::spec::all_scalar_values(input)
}

/// Contract for `utf8_percent_encode(&[u32], PercentEncodeSet) ->
/// Vec<u32>`: equals "UTF-8 percent-encode" a scalar value string.
pub open spec fn utf8_percent_encode_ensures(input: Seq<u32>, set: PercentEncodeSet, output: Seq<u32>) -> bool {
    output == utf8_percent_encode(input, set)
}

} // verus!
