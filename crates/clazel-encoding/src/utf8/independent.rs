//! An independent transcription of UTF-8 decoding, from a different
//! standard than [`super::spec`], written without reading that file
//! (docs/VERIFICATION.md, "Trust without reviewers", item 2).
//!
//! Sources:
//! - The Unicode Standard, Version 18.0.0, Chapter 3 "Conformance",
//!   <https://www.unicode.org/versions/Unicode18.0.0/core-spec/chapter-3/>:
//!   §3.9.3 D92 with Table 3-6 "UTF-8 Bit Distribution" (`#G27288`) and
//!   Table 3-7 "Well-Formed UTF-8 Byte Sequences" (`#G27506`); §3.9.6
//!   "U+FFFD Substitution of Maximal Subparts" (`#G66453`), D93a and D93b;
//!   conformance clause C10 (`#G23402`); §3.10 D95 (`#G27894`).
//! - For the byte order mark only: Encoding Standard, Living Standard last
//!   updated 19 October 2026, commit `dd7943441a861a60a073bffa55869d91cb6a8288`,
//!   §6 "UTF-8 decode" (<https://encoding.spec.whatwg.org/#utf-8-decode>).
//!   Unicode does not say what a decoder does with a BOM (D95 only names
//!   its bytes), so this part has the same source document as `spec.rs`;
//!   it is independent in transcription only.
//!
//! What each function corresponds to in the Encoding Standard:
//! - [`unicode_decode_with_substitution`]: "UTF-8 decode without BOM"
//!   (errors become U+FFFD).
//! - [`unicode_decode_or_error`]: "UTF-8 decode without BOM or fail".
//! - [`unicode_decode_with_bom_removed`]: "UTF-8 decode".
//!
//! Modelling choices:
//! - A byte sequence is `Seq<u8>`; an offset into it is a `nat`. Code
//!   points are `u32` (as in `contract.rs`), U+FFFD is `0xFFFD`.
//! - Table 3-7 is data: [`table_3_7`] returns row `r` (counting from 0,
//!   top to bottom) as its list of byte ranges, first byte first. Rows 0..8
//!   are the nine rows of the table; any other `r` is an empty row, which
//!   matches nothing.
//! - "Initial subsequence of a well-formed code unit sequence" (D93b a) is
//!   read as "a non-empty prefix of one row of Table 3-7". A longer
//!   well-formed sequence is a concatenation of rows, so any of its prefixes
//!   that is not a prefix of its first row already contains a whole row, and
//!   starts with a well-formed character: such an offset is not
//!   unconvertible, and D93b is only applied at unconvertible offsets.
//!   Rows have at most 4 bytes, so the search for the longest one stops at
//!   4.
//! - "Some subsequence starting at that offset is well-formed" (D93a) is
//!   read as "some row of Table 3-7 matches the bytes at that offset
//!   exactly", for the same reason: every non-empty well-formed sequence
//!   starts with one whole row.
//! - Conversion at a convertible offset converts that one row (a "minimal
//!   well-formed code unit subsequence", D85a) to its scalar value and
//!   continues after it. Rows are prefix-free (no row's ranges are a prefix
//!   of another row's), so at most one length matches; the search tries
//!   lengths 1 to 4 in order.
//! - Table 3-6's bit distribution is arithmetic: the `x` bits of a
//!   continuation byte `10xxxxxx` are `byte % 64`; the payload of a lead
//!   byte `110yyyyy`, `1110zzzz` or `11110uuu` is `byte % 32`, `% 16` or
//!   `% 8`. Concatenating bit fields is multiplying by a power of two and
//!   adding. These are exact because the byte ranges of Table 3-7 fix the
//!   high bits.
//! - C10 ("treat ill-formed code unit sequences as an error condition") is
//!   modelled as returning `None` exactly when some offset reached during
//!   conversion is unconvertible, and `Some(scalar values)` otherwise.

#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// One cell of Table 3-7: the bytes `lo..hi`, inclusive ("A0..BF").
pub struct ByteRange {
    /// First byte of the range.
    pub lo: u8,
    /// Last byte of the range, inclusive.
    pub hi: u8,
}

/// `lo..hi` as written in Table 3-7.
pub open spec fn range(lo: u8, hi: u8) -> ByteRange {
    ByteRange { lo, hi }
}

/// A single byte, written as one value in Table 3-7 ("E0").
pub open spec fn byte(b: u8) -> ByteRange {
    ByteRange { lo: b, hi: b }
}

/// Number of rows in Table 3-7.
pub open spec fn table_3_7_rows() -> nat {
    9
}

/// Unicode §3.9.3, Table 3-7 "Well-Formed UTF-8 Byte Sequences", row `r`:
/// the ranges of its First, Second, Third and Fourth Byte columns, as many
/// as the row has. The "Code Points" column is in each row's comment.
pub open spec fn table_3_7(r: nat) -> Seq<ByteRange> {
    if r == 0 {
        // U+0000..U+007F
        seq![range(0x00, 0x7F)]
    } else if r == 1 {
        // U+0080..U+07FF
        seq![range(0xC2, 0xDF), range(0x80, 0xBF)]
    } else if r == 2 {
        // U+0800..U+0FFF
        seq![byte(0xE0), range(0xA0, 0xBF), range(0x80, 0xBF)]
    } else if r == 3 {
        // U+1000..U+CFFF
        seq![range(0xE1, 0xEC), range(0x80, 0xBF), range(0x80, 0xBF)]
    } else if r == 4 {
        // U+D000..U+D7FF
        seq![byte(0xED), range(0x80, 0x9F), range(0x80, 0xBF)]
    } else if r == 5 {
        // U+E000..U+FFFF
        seq![range(0xEE, 0xEF), range(0x80, 0xBF), range(0x80, 0xBF)]
    } else if r == 6 {
        // U+10000..U+3FFFF
        seq![byte(0xF0), range(0x90, 0xBF), range(0x80, 0xBF), range(0x80, 0xBF)]
    } else if r == 7 {
        // U+40000..U+FFFFF
        seq![range(0xF1, 0xF3), range(0x80, 0xBF), range(0x80, 0xBF), range(0x80, 0xBF)]
    } else if r == 8 {
        // U+100000..U+10FFFF
        seq![byte(0xF4), range(0x80, 0x8F), range(0x80, 0xBF), range(0x80, 0xBF)]
    } else {
        seq![]
    }
}

/// "a range such as A0..BF means any byte from A0 to BF inclusive".
pub open spec fn in_range(b: u8, cell: ByteRange) -> bool {
    cell.lo <= b && b <= cell.hi
}

/// Bytes `k..` of `bytes` fall in the ranges of the same columns of `row`
/// (and `row` has that many columns).
pub open spec fn columns_match_from(bytes: Seq<u8>, row: Seq<ByteRange>, k: nat) -> bool
    decreases bytes.len() - k,
{
    if k >= bytes.len() {
        true
    } else {
        k < row.len() && in_range(bytes[k as int], row[k as int])
            && columns_match_from(bytes, row, k + 1)
    }
}

/// `bytes` is a prefix of row `r` of Table 3-7: each byte is in its
/// column's range.
pub open spec fn matches_row_prefix(bytes: Seq<u8>, r: nat) -> bool {
    bytes.len() <= table_3_7(r).len() && columns_match_from(bytes, table_3_7(r), 0)
}

/// `bytes` is exactly row `r` of Table 3-7: one well-formed character.
pub open spec fn matches_row(bytes: Seq<u8>, r: nat) -> bool {
    bytes.len() == table_3_7(r).len() && columns_match_from(bytes, table_3_7(r), 0)
}

/// Some row `r' >= r` of Table 3-7 matches `bytes` exactly.
pub open spec fn some_row_matches_from(bytes: Seq<u8>, r: nat) -> bool
    decreases table_3_7_rows() - r,
{
    if r >= table_3_7_rows() {
        false
    } else {
        matches_row(bytes, r) || some_row_matches_from(bytes, r + 1)
    }
}

/// Some row `r' >= r` of Table 3-7 starts with `bytes`.
pub open spec fn some_row_starts_with_from(bytes: Seq<u8>, r: nat) -> bool
    decreases table_3_7_rows() - r,
{
    if r >= table_3_7_rows() {
        false
    } else {
        matches_row_prefix(bytes, r) || some_row_starts_with_from(bytes, r + 1)
    }
}

/// D92: "Any UTF-8 byte sequence that does not match the patterns listed in
/// Table 3-7 is ill-formed." This is the one-character case: `bytes` is a
/// whole row of the table.
pub open spec fn is_well_formed_character(bytes: Seq<u8>) -> bool {
    some_row_matches_from(bytes, 0)
}

/// D93b a: "the initial subsequence of a well-formed code unit sequence",
/// non-empty (see the modelling choices).
pub open spec fn is_initial_subsequence(bytes: Seq<u8>) -> bool {
    bytes.len() > 0 && some_row_starts_with_from(bytes, 0)
}

/// The `k` bytes at offset `i` exist and are one well-formed character.
pub open spec fn is_character_at(input: Seq<u8>, i: nat, k: nat) -> bool {
    i + k <= input.len() && is_well_formed_character(input.subrange(i as int, (i + k) as int))
}

/// Length of the well-formed character at offset `i`, or 0 if none starts
/// there. Rows have 1 to 4 bytes; the lengths are tried in that order.
pub open spec fn character_len(input: Seq<u8>, i: nat) -> nat {
    if is_character_at(input, i, 1) {
        1
    } else if is_character_at(input, i, 2) {
        2
    } else if is_character_at(input, i, 3) {
        3
    } else if is_character_at(input, i, 4) {
        4
    } else {
        0
    }
}

/// D93a "Unconvertible offset: An offset in a code unit sequence for which
/// no code unit subsequence starting at that offset is well-formed."
pub open spec fn is_unconvertible_offset(input: Seq<u8>, i: nat) -> bool {
    character_len(input, i) == 0
}

/// The `k` bytes at offset `i` exist and are an initial subsequence of a
/// well-formed code unit sequence.
pub open spec fn is_initial_subsequence_at(input: Seq<u8>, i: nat, k: nat) -> bool {
    i + k <= input.len() && is_initial_subsequence(input.subrange(i as int, (i + k) as int))
}

/// D93b "Maximal subpart of an ill-formed subsequence: The longest code unit
/// subsequence starting at an unconvertible offset that is either:
/// a. the initial subsequence of a well-formed code unit sequence, or
/// b. a subsequence of length one."
/// Returns its length.
pub open spec fn maximal_subpart_len(input: Seq<u8>, i: nat) -> nat {
    // a. The longest is tried first; no row is longer than 4 bytes.
    if is_initial_subsequence_at(input, i, 4) {
        4
    } else if is_initial_subsequence_at(input, i, 3) {
        3
    } else if is_initial_subsequence_at(input, i, 2) {
        2
    } else {
        // b. "a subsequence of length one" (a length-one initial
        // subsequence, if there is one, is this too).
        1
    }
}

/// Table 3-6 "UTF-8 Bit Distribution": the scalar value of one well-formed
/// character `bytes` (1 to 4 bytes long).
pub open spec fn scalar_value(bytes: Seq<u8>) -> u32 {
    if bytes.len() == 1 {
        // 0xxxxxxx -> 00000000 0xxxxxxx
        bytes[0] as u32
    } else if bytes.len() == 2 {
        // 110yyyyy 10xxxxxx -> 00000yyy yyxxxxxx
        ((bytes[0] % 32) as int * 64 + (bytes[1] % 64) as int) as u32
    } else if bytes.len() == 3 {
        // 1110zzzz 10yyyyyy 10xxxxxx -> zzzzyyyy yyxxxxxx
        ((bytes[0] % 16) as int * 4096 + (bytes[1] % 64) as int * 64
            + (bytes[2] % 64) as int) as u32
    } else {
        // 11110uuu 10uuzzzz 10yyyyyy 10xxxxxx -> 000uuuuu zzzzyyyy yyxxxxxx
        ((bytes[0] % 8) as int * 262144 + (bytes[1] % 64) as int * 4096
            + (bytes[2] % 64) as int * 64 + (bytes[3] % 64) as int) as u32
    }
}

/// Conversion from offset `i` with "U+FFFD Substitution of Maximal
/// Subparts" (§3.9.6).
pub open spec fn decode_with_substitution_from(input: Seq<u8>, i: nat) -> Seq<u32>
    decreases input.len() - i,
{
    if i >= input.len() {
        seq![]
    } else if !is_unconvertible_offset(input, i) {
        // A well-formed character: convert it (Table 3-6) and continue
        // after it.
        let n = character_len(input, i);
        seq![scalar_value(input.subrange(i as int, (i + n) as int))]
            + decode_with_substitution_from(input, i + n)
    } else {
        // "Whenever an unconvertible offset is reached during conversion of
        // a code unit sequence:"
        // 1. "The maximal subpart at that offset is replaced by a single
        //    U+FFFD."
        // 2. "The conversion proceeds at the offset immediately after the
        //    maximal subpart."
        seq![0xFFFDu32] + decode_with_substitution_from(input, i + maximal_subpart_len(input, i))
    }
}

/// Unicode §3.9.6: convert `input` from UTF-8, replacing each maximal
/// subpart with U+FFFD. Corresponds to "UTF-8 decode without BOM".
pub open spec fn unicode_decode_with_substitution(input: Seq<u8>) -> Seq<u32> {
    decode_with_substitution_from(input, 0)
}

/// Conversion from offset `i` that treats ill-formed input as an error
/// condition (C10): `None` at the first unconvertible offset.
pub open spec fn decode_or_error_from(input: Seq<u8>, i: nat) -> Option<Seq<u32>>
    decreases input.len() - i,
{
    if i >= input.len() {
        Some(seq![])
    } else if !is_unconvertible_offset(input, i) {
        let n = character_len(input, i);
        match decode_or_error_from(input, i + n) {
            Some(rest) => Some(seq![scalar_value(input.subrange(i as int, (i + n) as int))] + rest),
            None => None,
        }
    } else {
        // C10: "it shall treat ill-formed code unit sequences as an error
        // condition".
        None
    }
}

/// C10 and D93: convert `input` from UTF-8, or `None` if it is ill-formed.
/// Corresponds to "UTF-8 decode without BOM or fail".
pub open spec fn unicode_decode_or_error(input: Seq<u8>) -> Option<Seq<u32>> {
    decode_or_error_from(input, 0)
}

/// Encoding §6 "UTF-8 decode": like [`unicode_decode_with_substitution`],
/// but a leading byte order mark is dropped. D95: "When represented in
/// UTF-8, the byte order mark turns into the byte sequence <EF BB BF>."
pub open spec fn unicode_decode_with_bom_removed(input: Seq<u8>) -> Seq<u32> {
    // 1. "Let buffer be the result of peeking three bytes from ioQueue"
    // 2. "If buffer is 0xEF 0xBB 0xBF, then read three bytes from ioQueue."
    if input.len() >= 3 && input[0] == 0xEF && input[1] == 0xBB && input[2] == 0xBF {
        // 3. "Process a queue with ... "replacement"."
        unicode_decode_with_substitution(input.subrange(3, input.len() as int))
    } else {
        // 3. (no BOM)
        unicode_decode_with_substitution(input)
    }
}

} // verus!
