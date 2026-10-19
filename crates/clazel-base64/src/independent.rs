//! An independent transcription of base64, from RFC 4648 rather than the
//! Infra Standard (docs/VERIFICATION.md, "Trust without reviewers", item
//! 2). It was transcribed from the RFC's text, not adapted from
//! [`super::spec`], and uses nothing from it above the proof section; but
//! the same agent session wrote both files, so the two may share a
//! misreading (the limit VERIFICATION.md states). The conformance tests,
//! which draw on WPT and the `base64` crate, carry more weight.
//!
//! Source: RFC 4648, "The Base16, Base32, and Base64 Data Encodings",
//! October 2006, <https://www.rfc-editor.org/rfc/rfc4648>: §4 "Base 64
//! Encoding" with Table 1 "The Base 64 Alphabet", §3.3 (decoders "MUST
//! reject the encoded data if it contains characters outside the base
//! alphabet") and §3.5 "Canonical Encoding" (pad bits "MUST be set to zero
//! by conforming encoders"). RFCs never change once published; this one
//! has no errata affecting §3.3, §3.5 or §4.
//!
//! How this relates to Infra. Infra's "forgiving-base64 encode" *is*
//! RFC 4648 §4, so for the encoder this file is a second transcription of
//! the same text, in a different form (a literal Table 1; bit shifts and
//! masks per 3-byte group, where `spec.rs` uses arithmetic on the group's
//! value). Infra's decoder is its own algorithm; RFC 4648 describes
//! decoding only as undoing §4, for well-formed input. They agree exactly
//! on the canonical, padded, whitespace-free strings ([`canonical`]):
//! - [`lemma_equals_forgiving_base64_encode`]: for every byte sequence,
//!   [`rfc4648_encode`] equals "forgiving-base64 encode".
//! - [`lemma_equals_forgiving_base64_decode`]: for every string that is
//!   [`canonical`], "forgiving-base64 decode" succeeds and equals
//!   [`rfc4648_decode`].
//! - [`lemma_canonical_is_image`]: [`canonical`] strings are exactly the
//!   outputs of [`rfc4648_encode`], so the domain above is stated exactly,
//!   not just restricted.
//! Outside that domain they differ by design: Infra accepts ASCII
//! whitespace (step 1), missing padding, and non-zero pad bits (its note:
//! "YQ" and "YR" both return `a`), which §3.3 and §3.5 let a referring
//! specification allow.
//!
//! Modelling choices:
//! - Characters are `u32` code points (all of them US-ASCII), octets `u8`.
//! - "Proceeding from left to right" is recursion on the first 3 octets
//!   (encode) or the first 4 characters (decode).
//! - "concatenating 3 8-bit input groups" and splitting into "4 concatenated
//!   6-bit groups" is written with shifts and masks on each octet, which is
//!   how the bits of the octets line up.
//! - Decoding: an encoded quantum's characters are looked up in Table 1,
//!   their 6-bit values concatenated, and the result split back into
//!   octets; a final quantum with one "=" carries 16 bits, with two "=", 8
//!   bits (cases (3) and (2) of §4, reversed). Only [`canonical`] input is
//!   given a meaning; elsewhere the result is unspecified.

#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// RFC 4648 Table 1: the "Encoding" of "Value" `v`, read row by row.
pub open spec fn table_1(v: u32) -> u32 {
    // Hexadecimal US-ASCII code of each character, which follows as a comment.
    match v {
        0 => 0x41, /* A */ 1 => 0x42, /* B */ 2 => 0x43, /* C */ 3 => 0x44, /* D */
        4 => 0x45, /* E */ 5 => 0x46, /* F */ 6 => 0x47, /* G */ 7 => 0x48, /* H */
        8 => 0x49, /* I */ 9 => 0x4A, /* J */ 10 => 0x4B, /* K */ 11 => 0x4C, /* L */
        12 => 0x4D, /* M */ 13 => 0x4E, /* N */ 14 => 0x4F, /* O */ 15 => 0x50, /* P */
        16 => 0x51, /* Q */ 17 => 0x52, /* R */ 18 => 0x53, /* S */ 19 => 0x54, /* T */
        20 => 0x55, /* U */ 21 => 0x56, /* V */ 22 => 0x57, /* W */ 23 => 0x58, /* X */
        24 => 0x59, /* Y */ 25 => 0x5A, /* Z */ 26 => 0x61, /* a */ 27 => 0x62, /* b */
        28 => 0x63, /* c */ 29 => 0x64, /* d */ 30 => 0x65, /* e */ 31 => 0x66, /* f */
        32 => 0x67, /* g */ 33 => 0x68, /* h */ 34 => 0x69, /* i */ 35 => 0x6A, /* j */
        36 => 0x6B, /* k */ 37 => 0x6C, /* l */ 38 => 0x6D, /* m */ 39 => 0x6E, /* n */
        40 => 0x6F, /* o */ 41 => 0x70, /* p */ 42 => 0x71, /* q */ 43 => 0x72, /* r */
        44 => 0x73, /* s */ 45 => 0x74, /* t */ 46 => 0x75, /* u */ 47 => 0x76, /* v */
        48 => 0x77, /* w */ 49 => 0x78, /* x */ 50 => 0x79, /* y */ 51 => 0x7A, /* z */
        52 => 0x30, /* 0 */ 53 => 0x31, /* 1 */ 54 => 0x32, /* 2 */ 55 => 0x33, /* 3 */
        56 => 0x34, /* 4 */ 57 => 0x35, /* 5 */ 58 => 0x36, /* 6 */ 59 => 0x37, /* 7 */
        60 => 0x38, /* 8 */ 61 => 0x39, /* 9 */ 62 => 0x2B, /* + */ _ => 0x2F, /* / */
    }
}

/// Table 1's "(pad) =".
pub open spec fn pad_char() -> u32 {
    0x3D  // =
}

/// The value whose encoding is `c`, searching Table 1 from value `v` on.
pub open spec fn value_from(c: u32, v: u32) -> Option<u32>
    decreases 64 - v
{
    if v >= 64 {
        None
    } else if table_1(v) == c {
        Some(v)
    } else {
        value_from(c, (v + 1) as u32)
    }
}

/// The value of base 64 alphabet character `c`, or `None` if `c` is
/// "outside the base alphabet" (§3.3).
pub open spec fn value(c: u32) -> Option<u32> {
    value_from(c, 0)
}

/// `c` is one of the 64 characters of Table 1 (not "=").
pub open spec fn in_alphabet(c: u32) -> bool {
    value(c) is Some
}

/// The value of an alphabet character (0 for anything else).
pub open spec fn val(c: u32) -> u32 {
    match value(c) {
        Some(v) => v,
        None => 0,
    }
}

/// §4, encoding, from left to right.
pub open spec fn rfc4648_encode(octets: Seq<u8>) -> Seq<u32>
    decreases octets.len()
{
    if octets.len() >= 3 {
        // "a 24-bit input group is formed by concatenating 3 8-bit input
        // groups. These 24 bits are then treated as 4 concatenated 6-bit
        // groups, each of which is translated into a single character".
        let (x, y, z) = (octets[0] as u32, octets[1] as u32, octets[2] as u32);
        seq![
            table_1(x >> 2),
            table_1(((x & 0x03) << 4) | (y >> 4)),
            table_1(((y & 0x0F) << 2) | (z >> 6)),
            table_1(z & 0x3F),
        ] + rfc4648_encode(octets.subrange(3, octets.len() as int))
    } else if octets.len() == 2 {
        // (3) "exactly 16 bits ... three characters followed by one "="
        // padding character", the 16 bits followed by two zero bits.
        let (x, y) = (octets[0] as u32, octets[1] as u32);
        seq![table_1(x >> 2), table_1(((x & 0x03) << 4) | (y >> 4)), table_1((y & 0x0F) << 2), pad_char()]
    } else if octets.len() == 1 {
        // (2) "exactly 8 bits ... two characters followed by two "="
        // padding characters", the 8 bits followed by four zero bits.
        let x = octets[0] as u32;
        seq![table_1(x >> 2), table_1((x & 0x03) << 4), pad_char(), pad_char()]
    } else {
        // (1) "an integral multiple of 24 bits ... no "=" padding".
        seq![]
    }
}

/// A final 4-character quantum, as §4 cases (1) to (3) produce it, with
/// zero pad bits (§3.5): four alphabet characters; three and "=", where
/// the third carries two zero pad bits; or two and "==", where the second
/// carries four.
pub open spec fn canonical_final(q: Seq<u32>) -> bool {
    &&& q.len() == 4
    &&& in_alphabet(q[0])
    &&& in_alphabet(q[1])
    &&& {
        ||| in_alphabet(q[2]) && in_alphabet(q[3])
        ||| in_alphabet(q[2]) && q[3] == pad_char() && val(q[2]) & 0x03 == 0
        ||| q[2] == pad_char() && q[3] == pad_char() && val(q[1]) & 0x0F == 0
    }
}

/// A canonical, padded, whitespace-free encoding: whole quanta of 4
/// characters (§4: "a full encoding quantum is always completed"), only
/// alphabet characters (§3.3) except for padding in the final quantum, and
/// zero pad bits (§3.5).
pub open spec fn canonical(s: Seq<u32>) -> bool
    decreases s.len()
{
    if s.len() == 0 {
        true
    } else if s.len() < 4 {
        false
    } else if s.len() == 4 {
        canonical_final(s)
    } else {
        in_alphabet(s[0]) && in_alphabet(s[1]) && in_alphabet(s[2]) && in_alphabet(s[3])
            && canonical(s.subrange(4, s.len() as int))
    }
}

/// Decoding a [`canonical`] string: §4 in reverse, a quantum at a time.
pub open spec fn rfc4648_decode(s: Seq<u32>) -> Seq<u8>
    decreases s.len()
{
    if s.len() < 4 {
        seq![]
    } else {
        let (a, b, c, d) = (val(s[0]), val(s[1]), val(s[2]), val(s[3]));
        let x = ((a << 2) | (b >> 4)) as u8;
        if s[2] == pad_char() {
            // (2): 8 bits.
            seq![x]
        } else {
            let y = (((b & 0x0F) << 4) | (c >> 2)) as u8;
            if s[3] == pad_char() {
                // (3): 16 bits.
                seq![x, y]
            } else {
                let z = (((c & 0x03) << 6) | d) as u8;
                seq![x, y, z] + rfc4648_decode(s.subrange(4, s.len() as int))
            }
        }
    }
}


// ===========================================================================
// Proof: this transcription equals `spec.rs` on its domain. Everything below
// is proof machinery; the transcription ends above.
// ===========================================================================

/// Table 1 here and Table 1 in `spec.rs` agree on values below `n`, and
/// looking a character up finds its value again.
pub open spec fn tables_agree_below(n: u32) -> bool
    decreases n
{
    if n == 0 {
        true
    } else {
        let v = (n - 1) as u32;
        tables_agree_below(v) && table_1(v) == super::spec::table_1_encoding(v as nat) && value(table_1(v)) == Some(v)
    }
}

/// [`tables_agree_below`] as a quantified fact.
proof fn lemma_tables_agree_below(n: u32)
    requires
        n <= 64,
        tables_agree_below(n),
    ensures
        forall|v: u32| v < n ==> table_1(v) == super::spec::table_1_encoding(v as nat) && #[trigger] value(table_1(v)) == Some(v),
    decreases n
{
    if n > 0 {
        lemma_tables_agree_below((n - 1) as u32);
    }
}

/// The two Table 1 transcriptions agree on all 64 rows (evaluated), and
/// "=" is not in the alphabet.
pub proof fn lemma_tables_agree()
    ensures
        forall|v: u32| v < 64 ==> table_1(v) == super::spec::table_1_encoding(v as nat) && #[trigger] value(table_1(v)) == Some(v),
        value(pad_char()) is None,
        pad_char() == super::spec::pad(),
{
    assert(tables_agree_below(64)) by (compute_only);
    assert(value(pad_char()) is None) by (compute_only);
    lemma_tables_agree_below(64);
}

/// A value found by the search is a row of Table 1 holding `c`.
proof fn lemma_value_from_sound(c: u32, v: u32)
    ensures
        value_from(c, v) matches Some(w) ==> w < 64 && table_1(w) == c,
    decreases 64 - v
{
    if v < 64 && table_1(v) != c {
        lemma_value_from_sound(c, (v + 1) as u32);
    }
}

/// The bits of one full 3-octet group, two ways: the `spec.rs` arithmetic
/// on the group's value, and the shifts and masks here; and §4 reversed.
proof fn lemma_group_bits(x: u32, y: u32, z: u32)
    requires
        x < 256,
        y < 256,
        z < 256,
    ensures
        ({
            let g = x * 65536 + y * 256 + z;
            let (a, b, c, d) = (x >> 2, ((x & 0x03) << 4) | (y >> 4), ((y & 0x0F) << 2) | (z >> 6), z & 0x3F);
            &&& g / 262144 % 64 == a && g / 4096 % 64 == b && g / 64 % 64 == c && g % 64 == d
            &&& a < 64 && b < 64 && c < 64 && d < 64
            &&& (a << 2) | (b >> 4) == x
            &&& ((b & 0x0F) << 4) | (c >> 2) == y
            &&& ((c & 0x03) << 6) | d == z
        }),
{
    assert({
        let g = x * 65536 + y * 256 + z;
        let (a, b, c, d) = (x >> 2, ((x & 0x03) << 4) | (y >> 4), ((y & 0x0F) << 2) | (z >> 6), z & 0x3F);
        &&& g / 262144 % 64 == a && g / 4096 % 64 == b && g / 64 % 64 == c && g % 64 == d
        &&& a < 64 && b < 64 && c < 64 && d < 64
        &&& (a << 2) | (b >> 4) == x
        &&& ((b & 0x0F) << 4) | (c >> 2) == y
        &&& ((c & 0x03) << 6) | d == z
    }) by (bit_vector)
        requires
            x < 256,
            y < 256,
            z < 256,
    ;
}

/// The same for the final 16 bits (case (3)).
proof fn lemma_final_16_bits(x: u32, y: u32)
    requires
        x < 256,
        y < 256,
    ensures
        ({
            let g = (x * 256 + y) * 4;
            let (a, b, c) = (x >> 2, ((x & 0x03) << 4) | (y >> 4), (y & 0x0F) << 2);
            &&& g / 4096 % 64 == a && g / 64 % 64 == b && g % 64 == c
            &&& a < 64 && b < 64 && c < 64 && c & 0x03 == 0
            &&& (a << 2) | (b >> 4) == x
            &&& ((b & 0x0F) << 4) | (c >> 2) == y
        }),
{
    assert({
        let g = (x * 256 + y) * 4;
        let (a, b, c) = (x >> 2, ((x & 0x03) << 4) | (y >> 4), (y & 0x0F) << 2);
        &&& g / 4096 % 64 == a && g / 64 % 64 == b && g % 64 == c
        &&& a < 64 && b < 64 && c < 64 && c & 0x03 == 0
        &&& (a << 2) | (b >> 4) == x
        &&& ((b & 0x0F) << 4) | (c >> 2) == y
    }) by (bit_vector)
        requires
            x < 256,
            y < 256,
    ;
}

/// The same for the final 8 bits (case (2)).
proof fn lemma_final_8_bits(x: u32)
    requires
        x < 256,
    ensures
        ({
            let g = x * 16;
            let (a, b) = (x >> 2, (x & 0x03) << 4);
            &&& g / 64 % 64 == a && g % 64 == b
            &&& a < 64 && b < 64 && b & 0x0F == 0
            &&& (a << 2) | (b >> 4) == x
        }),
{
    assert({
        let g = x * 16;
        let (a, b) = (x >> 2, (x & 0x03) << 4);
        &&& g / 64 % 64 == a && g % 64 == b
        &&& a < 64 && b < 64 && b & 0x0F == 0
        &&& (a << 2) | (b >> 4) == x
    }) by (bit_vector)
        requires
            x < 256,
    ;
}

/// §4 reversed and redone: four 6-bit values survive a trip through
/// octets, and so do three (with two zero pad bits) and two (with four).
proof fn lemma_values_bits(a: u32, b: u32, c: u32, d: u32)
    requires
        a < 64,
        b < 64,
        c < 64,
        d < 64,
    ensures
        ({
            let (x, y, z) = ((a << 2) | (b >> 4), ((b & 0x0F) << 4) | (c >> 2), ((c & 0x03) << 6) | d);
            &&& x < 256 && y < 256 && z < 256
            &&& x >> 2 == a
            &&& ((x & 0x03) << 4) | (y >> 4) == b
            &&& ((y & 0x0F) << 2) | (z >> 6) == c
            &&& z & 0x3F == d
            &&& (c & 0x03 == 0 ==> (y & 0x0F) << 2 == c)
            &&& (b & 0x0F == 0 ==> (x & 0x03) << 4 == b)
        }),
{
    assert({
        let (x, y, z) = ((a << 2) | (b >> 4), ((b & 0x0F) << 4) | (c >> 2), ((c & 0x03) << 6) | d);
        &&& x < 256 && y < 256 && z < 256
        &&& x >> 2 == a
        &&& ((x & 0x03) << 4) | (y >> 4) == b
        &&& ((y & 0x0F) << 2) | (z >> 6) == c
        &&& z & 0x3F == d
        &&& (c & 0x03 == 0 ==> (y & 0x0F) << 2 == c)
        &&& (b & 0x0F == 0 ==> (x & 0x03) << 4 == b)
    }) by (bit_vector)
        requires
            a < 64,
            b < 64,
            c < 64,
            d < 64,
    ;
}

/// From octet `i` on, `spec.rs`'s encoder equals [`rfc4648_encode`] of the
/// rest.
proof fn lemma_encode_from_equals(data: Seq<u8>, i: nat)
    requires
        i <= data.len(),
    ensures
        super::spec::encode_from(data, i) == rfc4648_encode(data.subrange(i as int, data.len() as int)),
    decreases data.len() - i
{
    lemma_tables_agree();
    let ii = i as int;
    let rest = data.subrange(ii, data.len() as int);
    if i + 3 <= data.len() {
        lemma_group_bits(data[ii] as u32, data[ii + 1] as u32, data[ii + 2] as u32);
        lemma_encode_from_equals(data, i + 3);
        assert(rest.subrange(3, rest.len() as int) =~= data.subrange(ii + 3, data.len() as int));
    } else if i + 2 == data.len() {
        lemma_final_16_bits(data[ii] as u32, data[ii + 1] as u32);
    } else if i + 1 == data.len() {
        lemma_final_8_bits(data[ii] as u32);
    }
}

/// The transcription's encoder equals "forgiving-base64 encode", for every
/// byte sequence.
pub proof fn lemma_equals_forgiving_base64_encode(data: Seq<u8>)
    ensures
        super::spec::forgiving_base64_encode(data) == rfc4648_encode(data),
{
    lemma_encode_from_equals(data, 0);
    assert(data.subrange(0, data.len() as int) =~= data);
}

/// Every encoding is [`canonical`], and decoding gives the octets back.
proof fn lemma_encode_canonical(octets: Seq<u8>)
    ensures
        canonical(rfc4648_encode(octets)),
        rfc4648_decode(rfc4648_encode(octets)) == octets,
    decreases octets.len()
{
    lemma_tables_agree();
    let e = rfc4648_encode(octets);
    if octets.len() >= 3 {
        let (x, y, z) = (octets[0] as u32, octets[1] as u32, octets[2] as u32);
        lemma_group_bits(x, y, z);
        let rest = octets.subrange(3, octets.len() as int);
        lemma_encode_canonical(rest);
        let e2 = rfc4648_encode(rest);
        assert(e.subrange(4, e.len() as int) =~= e2);
        assert(seq![octets[0], octets[1], octets[2]] + rest =~= octets);
        if e2.len() == 0 {
            assert(rest.len() == 0) by {
                if rest.len() > 0 {
                    assert(e2.len() >= 4);
                }
            }
        }
    } else if octets.len() == 2 {
        lemma_final_16_bits(octets[0] as u32, octets[1] as u32);
        assert(seq![octets[0], octets[1]] =~= octets);
    } else if octets.len() == 1 {
        lemma_final_8_bits(octets[0] as u32);
        assert(seq![octets[0]] =~= octets);
    } else {
        assert(octets =~= seq![]);
    }
}

/// The length of an encoding is 0 or at least 4.
proof fn lemma_encode_len(octets: Seq<u8>)
    ensures
        rfc4648_encode(octets).len() == 0 <==> octets.len() == 0,
{
}

/// A value found in the alphabet, as a number.
proof fn lemma_val(c: u32)
    requires
        in_alphabet(c),
    ensures
        val(c) < 64,
        table_1(val(c)) == c,
{
    lemma_value_from_sound(c, 0);
}

/// Decoding a [`canonical`] string and encoding the result gives the string
/// back.
proof fn lemma_canonical_decode(s: Seq<u32>)
    requires
        canonical(s),
    ensures
        rfc4648_encode(rfc4648_decode(s)) == s,
    decreases s.len()
{
    lemma_tables_agree();
    if s.len() >= 4 {
        lemma_val(s[0]);
        lemma_val(s[1]);
        let (a, b) = (val(s[0]), val(s[1]));
        if s[2] == pad_char() {
            // Two "=": case (2).
            lemma_values_bits(a, b, 0, 0);
            assert(s.len() == 4);
            assert(rfc4648_encode(rfc4648_decode(s)) =~= s);
        } else {
            lemma_val(s[2]);
            let c = val(s[2]);
            if s[3] == pad_char() {
                // One "=": case (3).
                lemma_values_bits(a, b, c, 0);
                assert(s.len() == 4);
                assert(rfc4648_encode(rfc4648_decode(s)) =~= s);
            } else {
                lemma_val(s[3]);
                let d = val(s[3]);
                lemma_values_bits(a, b, c, d);
                let rest = s.subrange(4, s.len() as int);
                if s.len() > 4 {
                    lemma_canonical_decode(rest);
                } else {
                    assert(rest =~= seq![]);
                    assert(rfc4648_decode(rest) =~= seq![]);
                    assert(rfc4648_encode(rfc4648_decode(rest)) =~= rest);
                }
                let o = rfc4648_decode(s);
                let (x, y, z) = ((a << 2) | (b >> 4), ((b & 0x0F) << 4) | (c >> 2), ((c & 0x03) << 6) | d);
                assert(o == seq![x as u8, y as u8, z as u8] + rfc4648_decode(rest));
                assert(o[0] as u32 == x && o[1] as u32 == y && o[2] as u32 == z);
                assert(o.subrange(3, o.len() as int) =~= rfc4648_decode(rest));
                assert(o.len() >= 3);
                let q = seq![
                    table_1(x >> 2),
                    table_1(((x & 0x03) << 4) | (y >> 4)),
                    table_1(((y & 0x0F) << 2) | (z >> 6)),
                    table_1(z & 0x3F),
                ];
                assert(rfc4648_encode(o) == q + rest);
                assert(q =~= s.subrange(0, 4));
                assert(rfc4648_encode(o) =~= s.subrange(0, 4) + rest);
                assert(s.subrange(0, 4) + rest =~= s);
            }
        }
    } else {
        assert(s.len() == 0);
        assert(rfc4648_decode(s) =~= seq![]);
    }
}

/// The domain is stated exactly: the [`canonical`] strings are exactly the
/// encodings of byte sequences, and [`rfc4648_decode`] inverts
/// [`rfc4648_encode`] both ways.
pub proof fn lemma_canonical_is_image(s: Seq<u32>, octets: Seq<u8>)
    ensures
        canonical(rfc4648_encode(octets)),
        rfc4648_decode(rfc4648_encode(octets)) == octets,
        canonical(s) ==> rfc4648_encode(rfc4648_decode(s)) == s,
{
    lemma_encode_canonical(octets);
    if canonical(s) {
        lemma_canonical_decode(s);
    }
}

/// On every [`canonical`] string, "forgiving-base64 decode" succeeds and
/// equals the transcription's decoder.
pub proof fn lemma_equals_forgiving_base64_decode(s: Seq<u32>)
    requires
        canonical(s),
    ensures
        super::spec::forgiving_base64_decode(s) == Some(rfc4648_decode(s)),
{
    let o = rfc4648_decode(s);
    lemma_canonical_decode(s);
    lemma_equals_forgiving_base64_encode(o);
    super::lemmas::lemma_decode_encode(o);
}

/// RFC 4648 §10's test vectors on the transcription.
pub proof fn lemma_rfc_examples() {
    assert(rfc4648_encode(seq![0x66u8, 0x6F, 0x6F, 0x62]) == seq![0x5Au32, 0x6D, 0x39, 0x76, 0x59, 0x67, 0x3D, 0x3D]) by (compute_only);
    assert(rfc4648_encode(seq![0x66u8, 0x6F, 0x6F, 0x62, 0x61]) == seq![0x5Au32, 0x6D, 0x39, 0x76, 0x59, 0x6D, 0x45, 0x3D]) by (compute_only);
    assert(rfc4648_decode(seq![0x5Au32, 0x6D, 0x39, 0x76, 0x59, 0x6D, 0x45, 0x3D]) == seq![0x66u8, 0x6F, 0x6F, 0x62, 0x61]) by (compute_only);
}

} // verus!
