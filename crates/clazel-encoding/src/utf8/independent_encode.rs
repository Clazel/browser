//! An independent transcription of UTF-8 encoding, from a different
//! standard than [`super::spec`], written without reading that file's
//! encoder (docs/VERIFICATION.md, "Trust without reviewers", item 2). The
//! decoder's independent transcription is [`super::independent`].
//!
//! Source: The Unicode Standard, Version 18.0.0, Chapter 3 "Conformance",
//! <https://www.unicode.org/versions/Unicode18.0.0/core-spec/chapter-3/>:
//! §3.9 D79 (a Unicode encoding form "assigns each Unicode scalar value to
//! a unique code unit sequence"), §3.9.3 D92 "UTF-8 encoding form" with
//! Table 3-6 "UTF-8 Bit Distribution" (`#G27288`) and the Code Points
//! column of Table 3-7 "Well-Formed UTF-8 Byte Sequences" (`#G27506`).
//!
//! [`unicode_encode`] corresponds to "UTF-8 encode" in the Encoding
//! Standard; [`lemma_equals_utf8_encode`] (after the transcription) proves
//! them equal. The transcription itself uses nothing from `spec.rs`; only
//! the proof section does.
//!
//! Modelling choices:
//! - A scalar value is a `u32` (as in `contract.rs`); a byte sequence is
//!   `Seq<u8>`.
//! - Table 3-6 is read as arithmetic: bit field `xxxxxx` of a scalar value
//!   is `c % 64`, the next six bits `c / 64 % 64`, and so on; writing a
//!   field into a byte pattern such as `110yyyyy` is adding it to
//!   `0b1100_0000`. This is exact because each field is narrower than the
//!   pattern's free bits.
//! - The row of Table 3-6 is the one whose Scalar Value pattern has exactly
//!   enough bits: below 2^7 the first row, below 2^11 the second, below
//!   2^16 the third, otherwise the fourth. Table 3-6 alone allows a scalar
//!   value in a longer row with leading zero bits; Table 3-7 (which D92
//!   also cites) rules that out, since its Code Points column puts
//!   U+0000..U+007F in one-byte rows, U+0080..U+07FF in two-byte rows,
//!   U+0800..U+FFFF in three-byte rows and U+10000..U+10FFFF in four-byte
//!   rows. Above U+10FFFF (not a scalar value) the fourth row is used; the
//!   result there means nothing.
//! - D79 maps one scalar value to one code unit sequence; a sequence of
//!   scalar values is encoded as the concatenation of their code unit
//!   sequences, in order ([`unicode_encode`]).

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Table 3-6 "UTF-8 Bit Distribution": the bytes of scalar value `c`.
pub open spec fn table_3_6(c: u32) -> Seq<u8> {
    // The six low bits, `xxxxxx` in every row but the first.
    let x = c % 64;
    if c < 0x80 {
        // 00000000 0xxxxxxx | 0xxxxxxx
        seq![c as u8]
    } else if c < 0x800 {
        // 00000yyy yyxxxxxx | 110yyyyy 10xxxxxx
        let y = c / 64;
        seq![(0b1100_0000 + y) as u8, (0b1000_0000 + x) as u8]
    } else if c < 0x1_0000 {
        // zzzzyyyy yyxxxxxx | 1110zzzz 10yyyyyy 10xxxxxx
        let y = c / 64 % 64;
        let z = c / 4096;
        seq![(0b1110_0000 + z) as u8, (0b1000_0000 + y) as u8, (0b1000_0000 + x) as u8]
    } else {
        // 000uuuuu zzzzyyyy yyxxxxxx | 11110uuu 10uuzzzz 10yyyyyy 10xxxxxx
        let y = c / 64 % 64;
        let z = c / 4096 % 16;
        let u = c / 65536;
        seq![
            (0b1111_0000 + u / 4) as u8,
            (0b1000_0000 + u % 4 * 16 + z) as u8,
            (0b1000_0000 + y) as u8,
            (0b1000_0000 + x) as u8,
        ]
    }
}

/// D79 and D92: the UTF-8 code unit sequence of the scalar values `s`.
pub open spec fn unicode_encode(s: Seq<u32>) -> Seq<u8>
    decreases s.len()
{
    if s.len() == 0 {
        seq![]
    } else {
        table_3_6(s[0]) + unicode_encode(s.drop_first())
    }
}

// ===========================================================================
// Proof: this transcription equals `spec.rs`. Everything below is proof
// machinery; the transcription ends above.
// ===========================================================================

/// D92's example, evaluated: <004D, 0430, 4E8C, 10302> is
/// <4D D0 B0 E4 BA 8C F0 90 8C 82>; and the ends of each row's range.
pub proof fn lemma_unicode_examples() {
    assert(unicode_encode(seq![0x4Du32, 0x430, 0x4E8C, 0x10302])
        =~= seq![0x4Du8, 0xD0, 0xB0, 0xE4, 0xBA, 0x8C, 0xF0, 0x90, 0x8C, 0x82]) by (compute_only);
    assert(unicode_encode(seq![0x7Fu32, 0x80, 0x7FF, 0x800, 0xFFFF, 0x10000, 0x10FFFF])
        =~= seq![0x7Fu8, 0xC2, 0x80, 0xDF, 0xBF, 0xE0, 0xA0, 0x80, 0xEF, 0xBF, 0xBF,
            0xF0, 0x90, 0x80, 0x80, 0xF4, 0x8F, 0xBF, 0xBF]) by (compute_only);
}

/// The fourth row's bit fields are the spec's: `uuu` is bits 18 and up,
/// and `uuzzzz` is bits 12 to 17.
proof fn lemma_fourth_row(c: u32)
    ensures
        c / 65536 / 4 == c / 262144,
        c / 65536 % 4 * 16 + c / 4096 % 16 == c / 4096 % 64,
{
    assert(c / 65536 / 4 == c / 262144) by (bit_vector);
    assert(c / 65536 % 4 * 16 + c / 4096 % 16 == c / 4096 % 64) by (bit_vector);
}

/// One scalar value: UTF-8's encoder's handler returns Table 3-6's bytes.
/// Holds for every `u32`, scalar value or not.
pub proof fn lemma_handler_equals_table_3_6(c: u32)
    ensures
        encoder_handler(ScalarItem::ScalarValue(c)) == EncoderHandlerResult::Bytes(table_3_6(c)),
{
    super::lemmas::lemma_encoder_bytes(c);
    lemma_fourth_row(c);
    assert(super::lemmas::encoded(c) =~= table_3_6(c));
}

/// From position `i` on, the spec's "process a queue" equals
/// [`unicode_encode`] of the rest.
proof fn lemma_process_queue_equals(input: Seq<u32>, i: nat)
    requires
        i <= input.len(),
    ensures
        encoder_process_queue(input, i) == unicode_encode(input.subrange(i as int, input.len() as int)),
    decreases input.len() - i
{
    let rest = input.subrange(i as int, input.len() as int);
    if i < input.len() {
        lemma_handler_equals_table_3_6(input[i as int]);
        lemma_process_queue_equals(input, i + 1);
        assert(rest.drop_first() =~= input.subrange((i + 1) as int, input.len() as int));
    } else {
        assert(rest =~= seq![]);
    }
}

/// The transcription equals "UTF-8 encode", for every input.
pub proof fn lemma_equals_utf8_encode(input: Seq<u32>)
    ensures
        utf8_encode(input) == unicode_encode(input),
{
    lemma_process_queue_equals(input, 0);
    assert(input.subrange(0, input.len() as int) =~= input);
}

} // verus!
