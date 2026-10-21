//! RFC 8949 Appendix A's examples that lie inside the profile, evaluated on
//! the spec, and the profile's rejections. Kept apart from
//! [`super::lemmas`] so that a mutant that breaks one of them does not stop
//! Verus before it checks a kill certificate there.
//!
//! Appendix A lists each example as a decoded value and its hex encoding;
//! the vendored `cbor/test-vectors` file `appendix_a.json` (the same
//! examples) is run through the executable codec in
//! `tests/conformance_appendix_a.rs`.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Appendix A: the item encoded as hex `00`.
pub proof fn lemma_example_uint_0()
    ensures
        decode(seq![0x00u8]) == Some(seq![Token::Uint(0)]),
        encode(seq![Token::Uint(0)]) == seq![0x00u8],
{
    assert(decode(seq![0x00u8]) == Some(seq![Token::Uint(0)])) by (compute_only);
    assert(encode(seq![Token::Uint(0)]) == seq![0x00u8]) by (compute_only);
}

/// Appendix A: the item encoded as hex `01`.
pub proof fn lemma_example_uint_1()
    ensures
        decode(seq![0x01u8]) == Some(seq![Token::Uint(1)]),
        encode(seq![Token::Uint(1)]) == seq![0x01u8],
{
    assert(decode(seq![0x01u8]) == Some(seq![Token::Uint(1)])) by (compute_only);
    assert(encode(seq![Token::Uint(1)]) == seq![0x01u8]) by (compute_only);
}

/// Appendix A: the item encoded as hex `0a`.
pub proof fn lemma_example_uint_10()
    ensures
        decode(seq![0x0au8]) == Some(seq![Token::Uint(10)]),
        encode(seq![Token::Uint(10)]) == seq![0x0au8],
{
    assert(decode(seq![0x0au8]) == Some(seq![Token::Uint(10)])) by (compute_only);
    assert(encode(seq![Token::Uint(10)]) == seq![0x0au8]) by (compute_only);
}

/// Appendix A: the item encoded as hex `17`.
pub proof fn lemma_example_uint_23()
    ensures
        decode(seq![0x17u8]) == Some(seq![Token::Uint(23)]),
        encode(seq![Token::Uint(23)]) == seq![0x17u8],
{
    assert(decode(seq![0x17u8]) == Some(seq![Token::Uint(23)])) by (compute_only);
    assert(encode(seq![Token::Uint(23)]) == seq![0x17u8]) by (compute_only);
}

/// Appendix A: the item encoded as hex `1818`.
pub proof fn lemma_example_uint_24()
    ensures
        decode(seq![0x18u8, 0x18]) == Some(seq![Token::Uint(24)]),
        encode(seq![Token::Uint(24)]) == seq![0x18u8, 0x18],
{
    assert(decode(seq![0x18u8, 0x18]) == Some(seq![Token::Uint(24)])) by (compute_only);
    assert(encode(seq![Token::Uint(24)]) == seq![0x18u8, 0x18]) by (compute_only);
}

/// Appendix A: the item encoded as hex `1819`.
pub proof fn lemma_example_uint_25()
    ensures
        decode(seq![0x18u8, 0x19]) == Some(seq![Token::Uint(25)]),
        encode(seq![Token::Uint(25)]) == seq![0x18u8, 0x19],
{
    assert(decode(seq![0x18u8, 0x19]) == Some(seq![Token::Uint(25)])) by (compute_only);
    assert(encode(seq![Token::Uint(25)]) == seq![0x18u8, 0x19]) by (compute_only);
}

/// Appendix A: the item encoded as hex `1864`.
pub proof fn lemma_example_uint_100()
    ensures
        decode(seq![0x18u8, 0x64]) == Some(seq![Token::Uint(100)]),
        encode(seq![Token::Uint(100)]) == seq![0x18u8, 0x64],
{
    assert(decode(seq![0x18u8, 0x64]) == Some(seq![Token::Uint(100)])) by (compute_only);
    assert(encode(seq![Token::Uint(100)]) == seq![0x18u8, 0x64]) by (compute_only);
}

/// Appendix A: the item encoded as hex `1903e8`.
pub proof fn lemma_example_uint_1000()
    ensures
        decode(seq![0x19u8, 0x03, 0xe8]) == Some(seq![Token::Uint(1000)]),
        encode(seq![Token::Uint(1000)]) == seq![0x19u8, 0x03, 0xe8],
{
    assert(decode(seq![0x19u8, 0x03, 0xe8]) == Some(seq![Token::Uint(1000)])) by (compute_only);
    assert(encode(seq![Token::Uint(1000)]) == seq![0x19u8, 0x03, 0xe8]) by (compute_only);
}

/// Appendix A: the item encoded as hex `1a000f4240`.
pub proof fn lemma_example_uint_1000000()
    ensures
        decode(seq![0x1au8, 0x00, 0x0f, 0x42, 0x40]) == Some(seq![Token::Uint(1000000)]),
        encode(seq![Token::Uint(1000000)]) == seq![0x1au8, 0x00, 0x0f, 0x42, 0x40],
{
    assert(decode(seq![0x1au8, 0x00, 0x0f, 0x42, 0x40]) == Some(seq![Token::Uint(1000000)])) by (compute_only);
    assert(encode(seq![Token::Uint(1000000)]) == seq![0x1au8, 0x00, 0x0f, 0x42, 0x40]) by (compute_only);
}

/// Appendix A: the item encoded as hex `1b000000e8d4a51000`.
pub proof fn lemma_example_uint_10_12()
    ensures
        decode(seq![0x1bu8, 0x00, 0x00, 0x00, 0xe8, 0xd4, 0xa5, 0x10, 0x00]) == Some(seq![Token::Uint(1000000000000)]),
        encode(seq![Token::Uint(1000000000000)]) == seq![0x1bu8, 0x00, 0x00, 0x00, 0xe8, 0xd4, 0xa5, 0x10, 0x00],
{
    assert(decode(seq![0x1bu8, 0x00, 0x00, 0x00, 0xe8, 0xd4, 0xa5, 0x10, 0x00]) == Some(seq![Token::Uint(1000000000000)])) by (compute_only);
    assert(encode(seq![Token::Uint(1000000000000)]) == seq![0x1bu8, 0x00, 0x00, 0x00, 0xe8, 0xd4, 0xa5, 0x10, 0x00]) by (compute_only);
}

/// Appendix A: the item encoded as hex `1bffffffffffffffff`.
pub proof fn lemma_example_uint_max()
    ensures
        decode(seq![0x1bu8, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff]) == Some(seq![Token::Uint(18446744073709551615)]),
        encode(seq![Token::Uint(18446744073709551615)]) == seq![0x1bu8, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff],
{
    assert(decode(seq![0x1bu8, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff]) == Some(seq![Token::Uint(18446744073709551615)])) by (compute_only);
    assert(encode(seq![Token::Uint(18446744073709551615)]) == seq![0x1bu8, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff]) by (compute_only);
}

/// Appendix A: the item encoded as hex `f4`.
pub proof fn lemma_example_false()
    ensures
        decode(seq![0xf4u8]) == Some(seq![Token::Bool(false)]),
        encode(seq![Token::Bool(false)]) == seq![0xf4u8],
{
    assert(decode(seq![0xf4u8]) == Some(seq![Token::Bool(false)])) by (compute_only);
    assert(encode(seq![Token::Bool(false)]) == seq![0xf4u8]) by (compute_only);
}

/// Appendix A: the item encoded as hex `f5`.
pub proof fn lemma_example_true()
    ensures
        decode(seq![0xf5u8]) == Some(seq![Token::Bool(true)]),
        encode(seq![Token::Bool(true)]) == seq![0xf5u8],
{
    assert(decode(seq![0xf5u8]) == Some(seq![Token::Bool(true)])) by (compute_only);
    assert(encode(seq![Token::Bool(true)]) == seq![0xf5u8]) by (compute_only);
}

/// Appendix A: the item encoded as hex `40`.
pub proof fn lemma_example_bytes_empty()
    ensures
        decode(seq![0x40u8]) == Some(seq![Token::Bytes(Seq::<u8>::empty())]),
        encode(seq![Token::Bytes(Seq::<u8>::empty())]) == seq![0x40u8],
{
    assert(decode(seq![0x40u8]) == Some(seq![Token::Bytes(Seq::<u8>::empty())])) by (compute_only);
    assert(encode(seq![Token::Bytes(Seq::<u8>::empty())]) == seq![0x40u8]) by (compute_only);
}

/// Appendix A: the item encoded as hex `4401020304`.
pub proof fn lemma_example_bytes_4()
    ensures
        decode(seq![0x44u8, 0x01, 0x02, 0x03, 0x04]) == Some(seq![Token::Bytes(seq![1u8, 2, 3, 4])]),
        encode(seq![Token::Bytes(seq![1u8, 2, 3, 4])]) == seq![0x44u8, 0x01, 0x02, 0x03, 0x04],
{
    assert(decode(seq![0x44u8, 0x01, 0x02, 0x03, 0x04]) == Some(seq![Token::Bytes(seq![1u8, 2, 3, 4])])) by (compute_only);
    assert(encode(seq![Token::Bytes(seq![1u8, 2, 3, 4])]) == seq![0x44u8, 0x01, 0x02, 0x03, 0x04]) by (compute_only);
}

/// Appendix A: the item encoded as hex `60`.
pub proof fn lemma_example_text_empty()
    ensures
        decode(seq![0x60u8]) == Some(seq![Token::Text(Seq::<u8>::empty())]),
        encode(seq![Token::Text(Seq::<u8>::empty())]) == seq![0x60u8],
{
    assert(decode(seq![0x60u8]) == Some(seq![Token::Text(Seq::<u8>::empty())])) by (compute_only);
    assert(encode(seq![Token::Text(Seq::<u8>::empty())]) == seq![0x60u8]) by (compute_only);
}

/// Appendix A: the item encoded as hex `6161`.
pub proof fn lemma_example_text_a()
    ensures
        decode(seq![0x61u8, 0x61]) == Some(seq![Token::Text(seq![0x61u8])]),
        encode(seq![Token::Text(seq![0x61u8])]) == seq![0x61u8, 0x61],
{
    assert(decode(seq![0x61u8, 0x61]) == Some(seq![Token::Text(seq![0x61u8])])) by (compute_only);
    assert(encode(seq![Token::Text(seq![0x61u8])]) == seq![0x61u8, 0x61]) by (compute_only);
}

/// Appendix A: the item encoded as hex `6449455446`.
pub proof fn lemma_example_text_ietf()
    ensures
        decode(seq![0x64u8, 0x49, 0x45, 0x54, 0x46]) == Some(seq![Token::Text(seq![0x49u8, 0x45, 0x54, 0x46])]),
        encode(seq![Token::Text(seq![0x49u8, 0x45, 0x54, 0x46])]) == seq![0x64u8, 0x49, 0x45, 0x54, 0x46],
{
    assert(decode(seq![0x64u8, 0x49, 0x45, 0x54, 0x46]) == Some(seq![Token::Text(seq![0x49u8, 0x45, 0x54, 0x46])])) by (compute_only);
    assert(encode(seq![Token::Text(seq![0x49u8, 0x45, 0x54, 0x46])]) == seq![0x64u8, 0x49, 0x45, 0x54, 0x46]) by (compute_only);
}

/// Appendix A: the item encoded as hex `62225c`.
pub proof fn lemma_example_text_quote_backslash()
    ensures
        decode(seq![0x62u8, 0x22, 0x5c]) == Some(seq![Token::Text(seq![0x22u8, 0x5C])]),
        encode(seq![Token::Text(seq![0x22u8, 0x5C])]) == seq![0x62u8, 0x22, 0x5c],
{
    assert(decode(seq![0x62u8, 0x22, 0x5c]) == Some(seq![Token::Text(seq![0x22u8, 0x5C])])) by (compute_only);
    assert(encode(seq![Token::Text(seq![0x22u8, 0x5C])]) == seq![0x62u8, 0x22, 0x5c]) by (compute_only);
}

/// Appendix A: the item encoded as hex `62c3bc`.
pub proof fn lemma_example_text_u_umlaut()
    ensures
        decode(seq![0x62u8, 0xc3, 0xbc]) == Some(seq![Token::Text(seq![0xC3u8, 0xBC])]),
        encode(seq![Token::Text(seq![0xC3u8, 0xBC])]) == seq![0x62u8, 0xc3, 0xbc],
{
    assert(decode(seq![0x62u8, 0xc3, 0xbc]) == Some(seq![Token::Text(seq![0xC3u8, 0xBC])])) by (compute_only);
    assert(encode(seq![Token::Text(seq![0xC3u8, 0xBC])]) == seq![0x62u8, 0xc3, 0xbc]) by (compute_only);
}

/// Appendix A: the item encoded as hex `63e6b0b4`.
pub proof fn lemma_example_text_water()
    ensures
        decode(seq![0x63u8, 0xe6, 0xb0, 0xb4]) == Some(seq![Token::Text(seq![0xE6u8, 0xB0, 0xB4])]),
        encode(seq![Token::Text(seq![0xE6u8, 0xB0, 0xB4])]) == seq![0x63u8, 0xe6, 0xb0, 0xb4],
{
    assert(decode(seq![0x63u8, 0xe6, 0xb0, 0xb4]) == Some(seq![Token::Text(seq![0xE6u8, 0xB0, 0xB4])])) by (compute_only);
    assert(encode(seq![Token::Text(seq![0xE6u8, 0xB0, 0xB4])]) == seq![0x63u8, 0xe6, 0xb0, 0xb4]) by (compute_only);
}

/// Appendix A: the item encoded as hex `64f0908591`.
pub proof fn lemma_example_text_u10151()
    ensures
        decode(seq![0x64u8, 0xf0, 0x90, 0x85, 0x91]) == Some(seq![Token::Text(seq![0xF0u8, 0x90, 0x85, 0x91])]),
        encode(seq![Token::Text(seq![0xF0u8, 0x90, 0x85, 0x91])]) == seq![0x64u8, 0xf0, 0x90, 0x85, 0x91],
{
    assert(decode(seq![0x64u8, 0xf0, 0x90, 0x85, 0x91]) == Some(seq![Token::Text(seq![0xF0u8, 0x90, 0x85, 0x91])])) by (compute_only);
    assert(encode(seq![Token::Text(seq![0xF0u8, 0x90, 0x85, 0x91])]) == seq![0x64u8, 0xf0, 0x90, 0x85, 0x91]) by (compute_only);
}

/// Appendix A: the item encoded as hex `80`.
pub proof fn lemma_example_array_empty()
    ensures
        decode(seq![0x80u8]) == Some(seq![Token::Array(0)]),
        encode(seq![Token::Array(0)]) == seq![0x80u8],
{
    assert(decode(seq![0x80u8]) == Some(seq![Token::Array(0)])) by (compute_only);
    assert(encode(seq![Token::Array(0)]) == seq![0x80u8]) by (compute_only);
}

/// Appendix A: the item encoded as hex `83010203`.
pub proof fn lemma_example_array_123()
    ensures
        decode(seq![0x83u8, 0x01, 0x02, 0x03]) == Some(seq![Token::Array(3), Token::Uint(1), Token::Uint(2), Token::Uint(3)]),
        encode(seq![Token::Array(3), Token::Uint(1), Token::Uint(2), Token::Uint(3)]) == seq![0x83u8, 0x01, 0x02, 0x03],
{
    assert(decode(seq![0x83u8, 0x01, 0x02, 0x03]) == Some(seq![Token::Array(3), Token::Uint(1), Token::Uint(2), Token::Uint(3)])) by (compute_only);
    assert(encode(seq![Token::Array(3), Token::Uint(1), Token::Uint(2), Token::Uint(3)]) == seq![0x83u8, 0x01, 0x02, 0x03]) by (compute_only);
}

/// Appendix A: the item encoded as hex `8301820203820405`.
pub proof fn lemma_example_array_nested()
    ensures
        decode(seq![0x83u8, 0x01, 0x82, 0x02, 0x03, 0x82, 0x04, 0x05]) == Some(seq![Token::Array(3), Token::Uint(1), Token::Array(2), Token::Uint(2), Token::Uint(3), Token::Array(2), Token::Uint(4), Token::Uint(5)]),
        encode(seq![Token::Array(3), Token::Uint(1), Token::Array(2), Token::Uint(2), Token::Uint(3), Token::Array(2), Token::Uint(4), Token::Uint(5)]) == seq![0x83u8, 0x01, 0x82, 0x02, 0x03, 0x82, 0x04, 0x05],
{
    assert(decode(seq![0x83u8, 0x01, 0x82, 0x02, 0x03, 0x82, 0x04, 0x05]) == Some(seq![Token::Array(3), Token::Uint(1), Token::Array(2), Token::Uint(2), Token::Uint(3), Token::Array(2), Token::Uint(4), Token::Uint(5)])) by (compute_only);
    assert(encode(seq![Token::Array(3), Token::Uint(1), Token::Array(2), Token::Uint(2), Token::Uint(3), Token::Array(2), Token::Uint(4), Token::Uint(5)]) == seq![0x83u8, 0x01, 0x82, 0x02, 0x03, 0x82, 0x04, 0x05]) by (compute_only);
}

/// Appendix A: the item encoded as hex `98190102030405060708090a0b0c0d0e0f101112131415161718181819`.
pub proof fn lemma_example_array_25()
    ensures
        decode(seq![0x98u8, 0x19, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d, 0x0e, 0x0f, 0x10, 0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17, 0x18, 0x18, 0x18, 0x19]) == Some(seq![Token::Array(25), Token::Uint(1), Token::Uint(2), Token::Uint(3), Token::Uint(4), Token::Uint(5), Token::Uint(6), Token::Uint(7), Token::Uint(8), Token::Uint(9), Token::Uint(10), Token::Uint(11), Token::Uint(12), Token::Uint(13), Token::Uint(14), Token::Uint(15), Token::Uint(16), Token::Uint(17), Token::Uint(18), Token::Uint(19), Token::Uint(20), Token::Uint(21), Token::Uint(22), Token::Uint(23), Token::Uint(24), Token::Uint(25)]),
        encode(seq![Token::Array(25), Token::Uint(1), Token::Uint(2), Token::Uint(3), Token::Uint(4), Token::Uint(5), Token::Uint(6), Token::Uint(7), Token::Uint(8), Token::Uint(9), Token::Uint(10), Token::Uint(11), Token::Uint(12), Token::Uint(13), Token::Uint(14), Token::Uint(15), Token::Uint(16), Token::Uint(17), Token::Uint(18), Token::Uint(19), Token::Uint(20), Token::Uint(21), Token::Uint(22), Token::Uint(23), Token::Uint(24), Token::Uint(25)]) == seq![0x98u8, 0x19, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d, 0x0e, 0x0f, 0x10, 0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17, 0x18, 0x18, 0x18, 0x19],
{
    assert(decode(seq![0x98u8, 0x19, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d, 0x0e, 0x0f, 0x10, 0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17, 0x18, 0x18, 0x18, 0x19]) == Some(seq![Token::Array(25), Token::Uint(1), Token::Uint(2), Token::Uint(3), Token::Uint(4), Token::Uint(5), Token::Uint(6), Token::Uint(7), Token::Uint(8), Token::Uint(9), Token::Uint(10), Token::Uint(11), Token::Uint(12), Token::Uint(13), Token::Uint(14), Token::Uint(15), Token::Uint(16), Token::Uint(17), Token::Uint(18), Token::Uint(19), Token::Uint(20), Token::Uint(21), Token::Uint(22), Token::Uint(23), Token::Uint(24), Token::Uint(25)])) by (compute_only);
    assert(encode(seq![Token::Array(25), Token::Uint(1), Token::Uint(2), Token::Uint(3), Token::Uint(4), Token::Uint(5), Token::Uint(6), Token::Uint(7), Token::Uint(8), Token::Uint(9), Token::Uint(10), Token::Uint(11), Token::Uint(12), Token::Uint(13), Token::Uint(14), Token::Uint(15), Token::Uint(16), Token::Uint(17), Token::Uint(18), Token::Uint(19), Token::Uint(20), Token::Uint(21), Token::Uint(22), Token::Uint(23), Token::Uint(24), Token::Uint(25)]) == seq![0x98u8, 0x19, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d, 0x0e, 0x0f, 0x10, 0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17, 0x18, 0x18, 0x18, 0x19]) by (compute_only);
}

/// Rejected: a 0 written with a one-byte argument (RFC 8949 section 4.2.1).
pub proof fn lemma_reject_non_shortest_24_zero()
    ensures
        decode(seq![0x18u8, 0x00]) is None,
{
    assert(decode(seq![0x18u8, 0x00]) is None) by (compute_only);
}

/// Rejected: 23 written with a one-byte argument.
pub proof fn lemma_reject_non_shortest_24_23()
    ensures
        decode(seq![0x18u8, 0x17]) is None,
{
    assert(decode(seq![0x18u8, 0x17]) is None) by (compute_only);
}

/// Rejected: 255 written with a two-byte argument.
pub proof fn lemma_reject_non_shortest_25_255()
    ensures
        decode(seq![0x19u8, 0x00, 0xff]) is None,
{
    assert(decode(seq![0x19u8, 0x00, 0xff]) is None) by (compute_only);
}

/// Rejected: 65535 written with a four-byte argument.
pub proof fn lemma_reject_non_shortest_26_65535()
    ensures
        decode(seq![0x1au8, 0x00, 0x00, 0xff, 0xff]) is None,
{
    assert(decode(seq![0x1au8, 0x00, 0x00, 0xff, 0xff]) is None) by (compute_only);
}

/// Rejected: 4294967295 written with an eight-byte argument.
pub proof fn lemma_reject_non_shortest_27_max32()
    ensures
        decode(seq![0x1bu8, 0x00, 0x00, 0x00, 0x00, 0xff, 0xff, 0xff, 0xff]) is None,
{
    assert(decode(seq![0x1bu8, 0x00, 0x00, 0x00, 0x00, 0xff, 0xff, 0xff, 0xff]) is None) by (compute_only);
}

/// Rejected: a byte string whose length 0 is not shortest.
pub proof fn lemma_reject_non_shortest_length()
    ensures
        decode(seq![0x58u8, 0x00]) is None,
{
    assert(decode(seq![0x58u8, 0x00]) is None) by (compute_only);
}

/// Rejected: an array whose length 0 is not shortest.
pub proof fn lemma_reject_non_shortest_array()
    ensures
        decode(seq![0x98u8, 0x00]) is None,
{
    assert(decode(seq![0x98u8, 0x00]) is None) by (compute_only);
}

/// Rejected: negative integer -1 (major type 1).
pub proof fn lemma_reject_negative()
    ensures
        decode(seq![0x20u8]) is None,
{
    assert(decode(seq![0x20u8]) is None) by (compute_only);
}

/// Rejected: an empty map (major type 5).
pub proof fn lemma_reject_map()
    ensures
        decode(seq![0xa0u8]) is None,
{
    assert(decode(seq![0xa0u8]) is None) by (compute_only);
}

/// Rejected: tag 0 (major type 6), the head of a date/time string.
pub proof fn lemma_reject_tag()
    ensures
        decode(seq![0xc0u8]) is None,
{
    assert(decode(seq![0xc0u8]) is None) by (compute_only);
}

/// Rejected: a tagged date/time string (major type 6).
pub proof fn lemma_reject_tag_with_text()
    ensures
        decode(seq![0xc0u8, 0x74, 0x32, 0x30, 0x31, 0x33, 0x2d, 0x30, 0x33, 0x2d, 0x32, 0x31, 0x54, 0x32, 0x30, 0x3a, 0x30, 0x34, 0x3a, 0x30, 0x30, 0x5a]) is None,
{
    assert(decode(seq![0xc0u8, 0x74, 0x32, 0x30, 0x31, 0x33, 0x2d, 0x30, 0x33, 0x2d, 0x32, 0x31, 0x54, 0x32, 0x30, 0x3a, 0x30, 0x34, 0x3a, 0x30, 0x30, 0x5a]) is None) by (compute_only);
}

/// Rejected: null.
pub proof fn lemma_reject_null()
    ensures
        decode(seq![0xf6u8]) is None,
{
    assert(decode(seq![0xf6u8]) is None) by (compute_only);
}

/// Rejected: undefined.
pub proof fn lemma_reject_undefined()
    ensures
        decode(seq![0xf7u8]) is None,
{
    assert(decode(seq![0xf7u8]) is None) by (compute_only);
}

/// Rejected: simple(16).
pub proof fn lemma_reject_simple()
    ensures
        decode(seq![0xf0u8]) is None,
{
    assert(decode(seq![0xf0u8]) is None) by (compute_only);
}

/// Rejected: a half-precision float.
pub proof fn lemma_reject_float16()
    ensures
        decode(seq![0xf9u8, 0x00, 0x00]) is None,
{
    assert(decode(seq![0xf9u8, 0x00, 0x00]) is None) by (compute_only);
}

/// Rejected: a double-precision float.
pub proof fn lemma_reject_float64()
    ensures
        decode(seq![0xfbu8, 0x3f, 0xf1, 0x99, 0x99, 0x99, 0x99, 0x99, 0x9a]) is None,
{
    assert(decode(seq![0xfbu8, 0x3f, 0xf1, 0x99, 0x99, 0x99, 0x99, 0x99, 0x9a]) is None) by (compute_only);
}

/// Rejected: break.
pub proof fn lemma_reject_break()
    ensures
        decode(seq![0xffu8]) is None,
{
    assert(decode(seq![0xffu8]) is None) by (compute_only);
}

/// Rejected: an indefinite-length array.
pub proof fn lemma_reject_indefinite_array()
    ensures
        decode(seq![0x9fu8, 0xff]) is None,
{
    assert(decode(seq![0x9fu8, 0xff]) is None) by (compute_only);
}

/// Rejected: an indefinite-length byte string.
pub proof fn lemma_reject_indefinite_bytes()
    ensures
        decode(seq![0x5fu8, 0x42, 0x01, 0x02, 0x43, 0x03, 0x04, 0x05, 0xff]) is None,
{
    assert(decode(seq![0x5fu8, 0x42, 0x01, 0x02, 0x43, 0x03, 0x04, 0x05, 0xff]) is None) by (compute_only);
}

/// Rejected: an indefinite-length text string.
pub proof fn lemma_reject_indefinite_text()
    ensures
        decode(seq![0x7fu8, 0x65, 0x73, 0x74, 0x72, 0x65, 0x61, 0x64, 0x6d, 0x69, 0x6e, 0x67, 0xff]) is None,
{
    assert(decode(seq![0x7fu8, 0x65, 0x73, 0x74, 0x72, 0x65, 0x61, 0x64, 0x6d, 0x69, 0x6e, 0x67, 0xff]) is None) by (compute_only);
}

/// Rejected: additional information 28.
pub proof fn lemma_reject_reserved_28()
    ensures
        decode(seq![0x1cu8]) is None,
{
    assert(decode(seq![0x1cu8]) is None) by (compute_only);
}

/// Rejected: no bytes at all.
pub proof fn lemma_reject_empty()
    ensures
        decode(Seq::<u8>::empty()) is None,
{
    assert(decode(Seq::<u8>::empty()) is None) by (compute_only);
}

/// Rejected: a two-byte argument cut short.
pub proof fn lemma_reject_truncated_argument()
    ensures
        decode(seq![0x19u8, 0x03]) is None,
{
    assert(decode(seq![0x19u8, 0x03]) is None) by (compute_only);
}

/// Rejected: a text string cut short.
pub proof fn lemma_reject_truncated_string()
    ensures
        decode(seq![0x62u8, 0x61]) is None,
{
    assert(decode(seq![0x62u8, 0x61]) is None) by (compute_only);
}

/// Rejected: an array missing elements.
pub proof fn lemma_reject_truncated_array()
    ensures
        decode(seq![0x83u8, 0x01]) is None,
{
    assert(decode(seq![0x83u8, 0x01]) is None) by (compute_only);
}

/// Rejected: a second item after the first.
pub proof fn lemma_reject_trailing()
    ensures
        decode(seq![0x00u8, 0x00]) is None,
{
    assert(decode(seq![0x00u8, 0x00]) is None) by (compute_only);
}

/// Rejected: an array of 2^64-1 elements with none present.
pub proof fn lemma_reject_huge_array()
    ensures
        decode(seq![0x9bu8, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff]) is None,
{
    assert(decode(seq![0x9bu8, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff]) is None) by (compute_only);
}

/// Rejected: a text string with a bad continuation byte.
pub proof fn lemma_reject_invalid_utf8()
    ensures
        decode(seq![0x62u8, 0xc3, 0x28]) is None,
{
    assert(decode(seq![0x62u8, 0xc3, 0x28]) is None) by (compute_only);
}

/// Rejected: a text string with an overlong encoding.
pub proof fn lemma_reject_overlong_utf8()
    ensures
        decode(seq![0x62u8, 0xc0, 0x80]) is None,
{
    assert(decode(seq![0x62u8, 0xc0, 0x80]) is None) by (compute_only);
}

/// Rejected: a text string holding a surrogate.
pub proof fn lemma_reject_surrogate_utf8()
    ensures
        decode(seq![0x63u8, 0xed, 0xa0, 0x80]) is None,
{
    assert(decode(seq![0x63u8, 0xed, 0xa0, 0x80]) is None) by (compute_only);
}

} // verus!
