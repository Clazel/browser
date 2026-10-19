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
//! What each function corresponds to in the Encoding Standard, and the
//! lemma (at the end of this file, after the transcription) proving them
//! equal to [`super::spec`]:
//! - [`unicode_decode_with_substitution`]: "UTF-8 decode without BOM"
//!   (errors become U+FFFD); [`lemma_equals_utf8_decode_without_bom`].
//! - [`unicode_decode_or_error`]: "UTF-8 decode without BOM or fail";
//!   [`lemma_equals_utf8_decode_without_bom_or_fail`].
//! - [`unicode_decode_with_bom_removed`]: "UTF-8 decode";
//!   [`lemma_equals_utf8_decode`].
//!
//! The transcription itself uses nothing from `spec.rs`; only the proof
//! section does.
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
use super::spec::*;
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

// ===========================================================================
// Proof: this transcription equals `spec.rs`. Everything below is proof
// machinery; the transcription ends above.
// ===========================================================================

/// Examples from the Unicode Standard itself, evaluated: D92's example,
/// Tables 3-8, 3-9, 3-10 and 3-11, and §3.9.5's <C2 41 42>.
pub proof fn lemma_unicode_examples() {
    // D92: <004D, 0430, 4E8C, 10302> is <4D D0 B0 E4 BA 8C F0 90 8C 82>.
    assert(unicode_decode_with_substitution(seq![0x4Du8, 0xD0, 0xB0, 0xE4, 0xBA, 0x8C, 0xF0, 0x90, 0x8C, 0x82])
        =~= seq![0x4Du32, 0x430, 0x4E8C, 0x10302]) by (compute_only);
    // Table 3-8. U+FFFD for Non-Shortest Form Sequences
    assert(unicode_decode_with_substitution(seq![0xC0u8, 0xAF, 0xE0, 0x80, 0xBF, 0xF0, 0x81, 0x82, 0x41])
        =~= seq![0xFFFDu32, 0xFFFD, 0xFFFD, 0xFFFD, 0xFFFD, 0xFFFD, 0xFFFD, 0xFFFD, 0x41]) by (compute_only);
    // Table 3-9. U+FFFD for Ill-Formed Sequences for Surrogates
    assert(unicode_decode_with_substitution(seq![0xEDu8, 0xA0, 0x80, 0xED, 0xBF, 0xBF, 0xED, 0xAF, 0x41])
        =~= seq![0xFFFDu32, 0xFFFD, 0xFFFD, 0xFFFD, 0xFFFD, 0xFFFD, 0xFFFD, 0xFFFD, 0x41]) by (compute_only);
    // Table 3-10. U+FFFD for Other Ill-Formed Sequences
    assert(unicode_decode_with_substitution(seq![0xF4u8, 0x91, 0x92, 0x93, 0xFF, 0x41, 0x80, 0xBF, 0x42])
        =~= seq![0xFFFDu32, 0xFFFD, 0xFFFD, 0xFFFD, 0xFFFD, 0x41, 0xFFFD, 0xFFFD, 0x42]) by (compute_only);
    // Table 3-11. U+FFFD for Truncated Sequences
    assert(unicode_decode_with_substitution(seq![0xE1u8, 0x80, 0xE2, 0xF0, 0x91, 0x92, 0xF1, 0xBF, 0x41])
        =~= seq![0xFFFDu32, 0xFFFD, 0xFFFD, 0xFFFD, 0x41]) by (compute_only);
    // §3.9.5: <C2 41 42> must become <U+FFFD, U+0041, U+0042>.
    assert(unicode_decode_with_substitution(seq![0xC2u8, 0x41, 0x42])
        =~= seq![0xFFFDu32, 0x41, 0x42]) by (compute_only);
}

/// Bytes after the lead byte `b0` in its row of Table 3-7, or -1 if no row
/// starts with `b0`.
pub open spec fn trail_count(b0: u8) -> int {
    if b0 <= 0x7F {
        0
    } else if 0xC2 <= b0 && b0 <= 0xDF {
        1
    } else if 0xE0 <= b0 && b0 <= 0xEF {
        2
    } else if 0xF0 <= b0 && b0 <= 0xF4 {
        3
    } else {
        -1
    }
}

/// Lowest second byte allowed after lead byte `b0`.
pub open spec fn second_lo(b0: u8) -> u8 {
    if b0 == 0xE0 { 0xA0 } else if b0 == 0xF0 { 0x90 } else { 0x80 }
}

/// Highest second byte allowed after lead byte `b0`.
pub open spec fn second_hi(b0: u8) -> u8 {
    if b0 == 0xED { 0x9F } else if b0 == 0xF4 { 0x8F } else { 0xBF }
}

/// A byte `80..BF`.
pub open spec fn is_continuation(b: u8) -> bool {
    0x80 <= b && b <= 0xBF
}

/// Table 3-7 restated by lead byte: `s` is a non-empty prefix of a row.
pub open spec fn seq_prefix_ok(s: Seq<u8>) -> bool {
    &&& 1 <= s.len()
    &&& trail_count(s[0]) >= 0
    &&& s.len() <= trail_count(s[0]) + 1
    &&& (s.len() >= 2 ==> second_lo(s[0]) <= s[1] && s[1] <= second_hi(s[0]))
    &&& (s.len() >= 3 ==> is_continuation(s[2]))
    &&& (s.len() >= 4 ==> is_continuation(s[3]))
}

/// [`seq_prefix_ok`] for the `p` bytes of `input` at offset `i`.
pub open spec fn prefix_ok(input: Seq<u8>, i: nat, p: nat) -> bool {
    let b0 = input[i as int];
    &&& 1 <= p
    &&& i + p <= input.len()
    &&& trail_count(b0) >= 0
    &&& p <= trail_count(b0) + 1
    &&& (p >= 2 ==> second_lo(b0) <= input[i + 1int] && input[i + 1int] <= second_hi(b0))
    &&& (p >= 3 ==> is_continuation(input[i + 2int]))
    &&& (p >= 4 ==> is_continuation(input[i + 3int]))
}

/// The Table 3-7 search, done by lead byte.
pub proof fn lemma_rows(s: Seq<u8>)
    requires
        1 <= s.len() <= 4,
    ensures
        some_row_starts_with_from(s, 0) == seq_prefix_ok(s),
        some_row_matches_from(s, 0) == (seq_prefix_ok(s) && s.len() == trail_count(s[0]) + 1),
{
    reveal_with_fuel(some_row_starts_with_from, 10);
    reveal_with_fuel(some_row_matches_from, 10);
    reveal_with_fuel(columns_match_from, 5);
}

/// [`is_initial_subsequence_at`] and [`is_character_at`] by lead byte.
pub proof fn lemma_at(input: Seq<u8>, i: nat, k: nat)
    requires
        i < input.len(),
        1 <= k <= 4,
    ensures
        is_initial_subsequence_at(input, i, k) == prefix_ok(input, i, k),
        is_character_at(input, i, k)
            == (prefix_ok(input, i, k) && k == trail_count(input[i as int]) + 1),
{
    if i + k <= input.len() {
        let s = input.subrange(i as int, (i + k) as int);
        lemma_rows(s);
        assert(s[0] == input[i as int]);
        assert(k >= 2 ==> s[1] == input[i + 1int]);
        assert(k >= 3 ==> s[2] == input[i + 2int]);
        assert(k >= 4 ==> s[3] == input[i + 3int]);
    }
}

/// What the independent transcription does at offset `i`, by lead byte.
pub proof fn lemma_offset(input: Seq<u8>, i: nat)
    requires
        i < input.len(),
    ensures
        ({
            let n = trail_count(input[i as int]) + 1;
            character_len(input, i) == if n >= 1 && prefix_ok(input, i, n as nat) { n } else { 0 }
        }),
        maximal_subpart_len(input, i) == if prefix_ok(input, i, 4) {
            4nat
        } else if prefix_ok(input, i, 3) {
            3nat
        } else if prefix_ok(input, i, 2) {
            2nat
        } else {
            1nat
        },
{
    lemma_at(input, i, 1);
    lemma_at(input, i, 2);
    lemma_at(input, i, 3);
    lemma_at(input, i, 4);
}

/// The value step 3 of the spec's handler stores for lead byte `b0`.
pub open spec fn lead_bits(b0: u8) -> u32 {
    if trail_count(b0) == 1 {
        (b0 & 0x1F) as u32
    } else if trail_count(b0) == 2 {
        (b0 & 0xF) as u32
    } else {
        (b0 & 0x7) as u32
    }
}

/// The spec's "UTF-8 code point" after reading the `p` bytes at `i`.
pub open spec fn partial_code_point(input: Seq<u8>, i: nat, p: nat) -> u32
    decreases p,
{
    if p <= 1 {
        lead_bits(input[i as int])
    } else {
        (partial_code_point(input, i, (p - 1) as nat) << 6u32)
            | ((input[i + p - 1int] & 0x3F) as u32)
    }
}

/// The spec's decoder state after reading the first `p` bytes (lead byte
/// included) of a character at `i` that is not yet complete.
pub open spec fn partial_state(input: Seq<u8>, i: nat, p: nat) -> Utf8Decoder {
    let b0 = input[i as int];
    Utf8Decoder {
        code_point: partial_code_point(input, i, p),
        bytes_seen: (p - 1) as nat,
        bytes_needed: trail_count(b0) as nat,
        lower_boundary: if p == 1 { second_lo(b0) } else { 0x80 },
        upper_boundary: if p == 1 { second_hi(b0) } else { 0xBF },
    }
}

/// Table 3-6's arithmetic equals the spec's shifts and masks.
pub proof fn lemma_bits(x0: u8, x1: u8, x2: u8, x3: u8)
    ensures
        (x0 & 0x1F) == x0 % 32,
        (x0 & 0xF) == x0 % 16,
        (x0 & 0x7) == x0 % 8,
        (x1 & 0x3F) == x1 % 64,
        (x2 & 0x3F) == x2 % 64,
        (x3 & 0x3F) == x3 % 64,
        ((((x0 & 0x1F) as u32) << 6u32) | ((x1 & 0x3F) as u32))
            == ((x0 % 32) as int * 64 + (x1 % 64) as int) as u32,
        ((((((x0 & 0xF) as u32) << 6u32) | ((x1 & 0x3F) as u32)) << 6u32) | ((x2 & 0x3F) as u32))
            == ((x0 % 16) as int * 4096 + (x1 % 64) as int * 64 + (x2 % 64) as int) as u32,
        ((((((((x0 & 0x7) as u32) << 6u32) | ((x1 & 0x3F) as u32)) << 6u32)
            | ((x2 & 0x3F) as u32)) << 6u32) | ((x3 & 0x3F) as u32))
            == ((x0 % 8) as int * 262144 + (x1 % 64) as int * 4096 + (x2 % 64) as int * 64
                + (x3 % 64) as int) as u32,
{
    assert((x0 & 0x1F) == x0 % 32) by (bit_vector);
    assert((x0 & 0xF) == x0 % 16) by (bit_vector);
    assert((x0 & 0x7) == x0 % 8) by (bit_vector);
    assert((x1 & 0x3F) == x1 % 64) by (bit_vector);
    assert((x2 & 0x3F) == x2 % 64) by (bit_vector);
    assert((x3 & 0x3F) == x3 % 64) by (bit_vector);
    let a2: u32 = (x0 & 0x1F) as u32;
    let a3: u32 = (x0 & 0xF) as u32;
    let a4: u32 = (x0 & 0x7) as u32;
    let c1: u32 = (x1 & 0x3F) as u32;
    let c2: u32 = (x2 & 0x3F) as u32;
    let c3: u32 = (x3 & 0x3F) as u32;
    assert((a2 << 6u32) | c1 == a2 * 64 + c1) by (bit_vector)
        requires a2 < 32, c1 < 64;
    assert((((a3 << 6u32) | c1) << 6u32) | c2 == a3 * 4096 + c1 * 64 + c2) by (bit_vector)
        requires a3 < 16, c1 < 64, c2 < 64;
    assert((((((a4 << 6u32) | c1) << 6u32) | c2) << 6u32) | c3
        == a4 * 262144 + c1 * 4096 + c2 * 64 + c3) by (bit_vector)
        requires a4 < 8, c1 < 64, c2 < 64, c3 < 64;
}

/// A complete multi-byte character: the spec's code point is Table 3-6's
/// scalar value.
pub proof fn lemma_value(input: Seq<u8>, i: nat, n: nat)
    requires
        2 <= n,
        prefix_ok(input, i, n),
        n == trail_count(input[i as int]) + 1,
    ensures
        partial_code_point(input, i, n) == scalar_value(input.subrange(i as int, (i + n) as int)),
{
    let s = input.subrange(i as int, (i + n) as int);
    let x0 = input[i as int];
    let x1 = input[i + 1int];
    let x2 = if n >= 3 { input[i + 2int] } else { 0u8 };
    let x3 = if n >= 4 { input[i + 3int] } else { 0u8 };
    lemma_bits(x0, x1, x2, x3);
    assert(s[0] == x0 && s[1] == x1);
    assert(n >= 3 ==> s[2] == x2);
    assert(n >= 4 ==> s[3] == x3);
    reveal_with_fuel(partial_code_point, 4);
}

/// The output after an error at the current offset, continuing at `j`.
pub open spec fn after_error(mode: ErrorMode, input: Seq<u8>, j: nat) -> Option<Seq<u32>> {
    match mode {
        ErrorMode::Replacement => cons(0xFFFD, process_queue(mode, initial_decoder(), input, j)),
        ErrorMode::Fatal => None,
    }
}

/// The independent transcription's step at offset `i`, with the spec's
/// `process_queue` for the rest of the input.
pub open spec fn chunk(mode: ErrorMode, input: Seq<u8>, i: nat) -> Option<Seq<u32>> {
    if !is_unconvertible_offset(input, i) {
        let n = character_len(input, i);
        cons(
            scalar_value(input.subrange(i as int, (i + n) as int)),
            process_queue(mode, initial_decoder(), input, i + n),
        )
    } else {
        after_error(mode, input, i + maximal_subpart_len(input, i))
    }
}

/// At end-of-queue with no bytes needed, the spec finishes.
pub proof fn lemma_finished(mode: ErrorMode, d: Utf8Decoder, input: Seq<u8>)
    requires
        d.bytes_needed == 0,
    ensures
        process_queue(mode, d, input, input.len()) == Some(Seq::<u32>::empty()),
{
}

/// After the first `p` bytes of an incomplete character at `i`, the spec
/// ends that step exactly as the independent transcription does.
pub proof fn lemma_partial(mode: ErrorMode, input: Seq<u8>, i: nat, p: nat)
    requires
        i < input.len(),
        1 <= p,
        p < trail_count(input[i as int]) + 1,
        prefix_ok(input, i, p),
    ensures
        process_queue(mode, partial_state(input, i, p), input, i + p) == chunk(mode, input, i),
    decreases trail_count(input[i as int]) + 1 - p,
{
    let b0 = input[i as int];
    let n = (trail_count(b0) + 1) as nat;
    let d = partial_state(input, i, p);
    lemma_offset(input, i);
    if i + p == input.len() {
        // End-of-queue: step 1 returns error with bytes needed 0, then
        // step 2 returns finished.
        let s = handler(d, Item::EndOfQueue);
        assert(s.result == HandlerResult::Error);
        lemma_finished(mode, s.decoder, input);
        lemma_finished(mode, initial_decoder(), input);
        assert(!prefix_ok(input, i, p + 1));
    } else {
        let b = input[(i + p) as int];
        if !(d.lower_boundary <= b && b <= d.upper_boundary) {
            // Step 4: error, and the byte is restored.
            assert(!prefix_ok(input, i, p + 1));
        } else if p + 1 == n {
            // Step 11: the character is complete.
            assert(prefix_ok(input, i, n));
            lemma_value(input, i, n);
        } else {
            // Step 8: continue.
            assert(prefix_ok(input, i, p + 1));
            assert(handler(d, Item::Byte(b)).decoder == partial_state(input, i, p + 1));
            lemma_partial(mode, input, i, p + 1);
        }
    }
}

/// From the initial state at offset `i`, the spec does what the
/// independent transcription does at `i`.
pub proof fn lemma_chunk(mode: ErrorMode, input: Seq<u8>, i: nat)
    requires
        i < input.len(),
    ensures
        process_queue(mode, initial_decoder(), input, i) == chunk(mode, input, i),
{
    let b0 = input[i as int];
    lemma_offset(input, i);
    if b0 <= 0x7F {
        let s = input.subrange(i as int, i + 1int);
        assert(s[0] == b0);
    } else if trail_count(b0) >= 1 {
        assert(prefix_ok(input, i, 1));
        assert(handler(initial_decoder(), Item::Byte(b0)).decoder == partial_state(input, i, 1));
        lemma_partial(mode, input, i, 1);
    } else {
        assert(!prefix_ok(input, i, 1));
    }
}

/// The two transcriptions agree from offset `i` on, in "replacement" mode.
pub proof fn lemma_replacement_from(input: Seq<u8>, i: nat)
    requires
        i <= input.len(),
    ensures
        process_queue(ErrorMode::Replacement, initial_decoder(), input, i)
            == Some(decode_with_substitution_from(input, i)),
    decreases input.len() - i,
{
    if i == input.len() {
        lemma_finished(ErrorMode::Replacement, initial_decoder(), input);
    } else {
        lemma_chunk(ErrorMode::Replacement, input, i);
        lemma_offset(input, i);
        if !is_unconvertible_offset(input, i) {
            lemma_replacement_from(input, i + character_len(input, i));
        } else {
            lemma_replacement_from(input, i + maximal_subpart_len(input, i));
        }
    }
}

/// The two transcriptions agree from offset `i` on, in "fatal" mode.
pub proof fn lemma_fatal_from(input: Seq<u8>, i: nat)
    requires
        i <= input.len(),
    ensures
        process_queue(ErrorMode::Fatal, initial_decoder(), input, i) == decode_or_error_from(input, i),
    decreases input.len() - i,
{
    if i == input.len() {
        lemma_finished(ErrorMode::Fatal, initial_decoder(), input);
    } else {
        lemma_chunk(ErrorMode::Fatal, input, i);
        lemma_offset(input, i);
        if !is_unconvertible_offset(input, i) {
            lemma_fatal_from(input, i + character_len(input, i));
        }
    }
}

/// Unicode §3.9.6 substitution of maximal subparts is Encoding's
/// "UTF-8 decode without BOM", for every input.
pub proof fn lemma_equals_utf8_decode_without_bom(input: Seq<u8>)
    ensures
        utf8_decode_without_bom(input) == unicode_decode_with_substitution(input),
{
    lemma_replacement_from(input, 0);
}

/// Unicode C10 (ill-formed input is an error) is Encoding's "UTF-8 decode
/// without BOM or fail", for every input.
pub proof fn lemma_equals_utf8_decode_without_bom_or_fail(input: Seq<u8>)
    ensures
        utf8_decode_without_bom_or_fail(input) == unicode_decode_or_error(input),
{
    lemma_fatal_from(input, 0);
}

/// [`unicode_decode_with_bom_removed`] is Encoding's "UTF-8 decode", for
/// every input.
pub proof fn lemma_equals_utf8_decode(input: Seq<u8>)
    ensures
        utf8_decode(input) == unicode_decode_with_bom_removed(input),
{
    lemma_equals_utf8_decode_without_bom(input);
    lemma_equals_utf8_decode_without_bom(input.subrange(3, input.len() as int));
}

} // verus!
