//! Facts proven about the spec itself. They are evidence that the
//! transcription is right (docs/SPEC-STYLE.md), not part of what the
//! implementation must meet.
//!
//! What the standard states or asserts, proven:
//! - [`lemma_sets_include_non_ascii`]: percent-encode after encoding,
//!   step 7.3.3's assertion, "percentEncodeSet includes all non-ASCII code
//!   points", holds for every set.
//! - [`lemma_set_definitions`]: each set includes the one it is defined
//!   from, and the note "The query percent-encode set cannot be defined in
//!   terms of the fragment percent-encode set due to the omission of U+0060
//!   (`)".
//! - [`lemma_form_set_note`]: the note "The
//!   application/x-www-form-urlencoded percent-encode set contains all code
//!   points, except the ASCII alphanumeric, U+002A (*), U+002D (-), U+002E
//!   (.), and U+005F (_)".
//! - [`lemma_percent_sign_note`]: the note that of the sets "only two end
//!   up encoding U+0025 (%)": component and
//!   application/x-www-form-urlencoded.
//! - `examples::lemma_examples` (its own module, see there): the
//!   standard's example table, evaluated.
//! - [`lemma_no_percent_encoded_bytes`]: percent-decode changes nothing in
//!   a byte sequence without a percent-encoded byte (§1.3's first
//!   definition, which uses Infra's ASCII hex digit, not step 2.2's ranges).
//!
//! Decoding inverts encoding:
//! - [`lemma_decode_percent_encode`]: for every byte, percent-decoding its
//!   percent-encoding gives the byte back.
//! - [`lemma_decode_inverts_encode`]: for every set and every scalar value
//!   string, percent-decoding its UTF-8 percent-encoding gives its UTF-8
//!   encoding back, unless the set leaves a U+0025 (%) of the input alone,
//!   or is the application/x-www-form-urlencoded set (whose U+0020 SPACE
//!   becomes "+") and the input has a space. Both exceptions are what the
//!   standard says: the note after percent-encode after encoding ("leave
//!   U+0025 (%) untouched"), and step 7.3.1.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------
// The percent-encode sets.
// ---------------------------------------------------------------------

/// Percent-encode after encoding, step 7.3.3: "Assert: percentEncodeSet
/// includes all non-ASCII code points."
pub proof fn lemma_sets_include_non_ascii(set: PercentEncodeSet, c: u32)
    requires
        is_code_point(c),
        c > 0x7F,
    ensures
        contains(set, c),
{
}

/// Each set includes the one the standard defines it from, and the note
/// on the query set.
pub proof fn lemma_set_definitions(c: u32)
    ensures
        in_c0_control_percent_encode_set(c) ==> in_fragment_percent_encode_set(c),
        in_c0_control_percent_encode_set(c) ==> in_query_percent_encode_set(c),
        in_query_percent_encode_set(c) ==> in_special_query_percent_encode_set(c),
        in_query_percent_encode_set(c) ==> in_path_percent_encode_set(c),
        in_path_percent_encode_set(c) ==> in_userinfo_percent_encode_set(c),
        in_userinfo_percent_encode_set(c) ==> in_component_percent_encode_set(c),
        in_component_percent_encode_set(c)
            ==> in_application_x_www_form_urlencoded_percent_encode_set(c),
        in_fragment_percent_encode_set(0x60) && !in_query_percent_encode_set(0x60),
{
}

/// The note after the application/x-www-form-urlencoded percent-encode
/// set: it "contains all code points, except the ASCII alphanumeric, U+002A
/// (*), U+002D (-), U+002E (.), and U+005F (_)."
pub proof fn lemma_form_set_note(c: u32)
    requires
        is_code_point(c),
    ensures
        in_application_x_www_form_urlencoded_percent_encode_set(c) <==> !(is_ascii_alphanumeric(c)
            || c == 0x2A || c == 0x2D || c == 0x2E || c == 0x5F),
{
}

/// The note after percent-encode after encoding: "Of the possible values
/// for the percentEncodeSet argument only two end up encoding U+0025 (%)
/// [...]: component percent-encode set and
/// application/x-www-form-urlencoded percent-encode set."
pub proof fn lemma_percent_sign_note(set: PercentEncodeSet)
    ensures
        contains(set, 0x25) <==> (set == PercentEncodeSet::Component || set
            == PercentEncodeSet::ApplicationXWwwFormUrlencoded),
{
}

// ---------------------------------------------------------------------
// Percent-decode leaves text without percent-encoded bytes alone.
// ---------------------------------------------------------------------

/// From position `i`.
proof fn lemma_no_percent_encoded_bytes_from(input: Seq<u8>, i: nat)
    requires
        i <= input.len(),
        forall|k: int| !is_percent_encoded_byte_at(isomorphic_decode(input), k),
    ensures
        percent_decode_from(input, i) == input.skip(i as int),
    decreases input.len() - i,
{
    if i < input.len() {
        let s = isomorphic_decode(input);
        assert(!is_percent_encoded_byte_at(s, i as int));
        if input[i as int] == 0x25 && i + 2 < input.len() && in_hex_ranges(input[i + 1int])
            && in_hex_ranges(input[i + 2int]) {
            assert(s[i as int] == 0x25 && s[i + 1int] == input[i + 1int] as u32 && s[i + 2int]
                == input[i + 2int] as u32);
            assert(false);
        }
        lemma_no_percent_encoded_bytes_from(input, i + 1);
        assert(input.skip(i as int) =~= seq![input[i as int]] + input.skip(i + 1int));
    } else {
        assert(input.skip(i as int) =~= seq![]);
    }
}

/// A byte sequence that, isomorphic decoded, contains no percent-encoded
/// byte ("U+0025 (%) followed by two ASCII hex digits") is its own
/// percent-decoding.
pub proof fn lemma_no_percent_encoded_bytes(input: Seq<u8>)
    requires
        forall|k: int| !is_percent_encoded_byte_at(isomorphic_decode(input), k),
    ensures
        percent_decode(input) == input,
{
    lemma_no_percent_encoded_bytes_from(input, 0);
    assert(input.skip(0) =~= input);
}

// ---------------------------------------------------------------------
// Decoding inverts encoding.
// ---------------------------------------------------------------------

/// Every element of `s` is an ASCII code point.
pub open spec fn all_ascii(s: Seq<u32>) -> bool {
    forall|k: int| 0 <= k < s.len() ==> #[trigger] s[k] <= 0x7F
}

/// `s` has no element equal to `c`.
pub open spec fn lacks(s: Seq<u32>, c: u32) -> bool {
    forall|k: int| 0 <= k < s.len() ==> #[trigger] s[k] != c
}

/// UTF-8 encode of ASCII code points from position `i` is their values.
proof fn lemma_utf8_encode_ascii_from(s: Seq<u32>, i: nat)
    requires
        all_ascii(s),
        i <= s.len(),
    ensures
        clazel_encoding::utf8::spec::encoder_process_queue(s, i) == s.skip(i as int).map_values(
            |c: u32| c as u8,
        ),
    decreases s.len() - i,
{
    if i < s.len() {
        clazel_encoding::utf8::lemmas::lemma_encoder_bytes(s[i as int]);
        lemma_utf8_encode_ascii_from(s, i + 1);
        assert(s.skip(i as int).map_values(|c: u32| c as u8) =~= seq![s[i as int] as u8] + s.skip(i + 1int).map_values(|c: u32| c as u8));
    } else {
        assert(s.skip(i as int).map_values(|c: u32| c as u8) =~= seq![]);
    }
}

/// UTF-8 encode of an ASCII string is its code points' values.
pub proof fn lemma_utf8_encode_ascii(s: Seq<u32>)
    requires
        all_ascii(s),
    ensures
        clazel_encoding::utf8::spec::utf8_encode(s) == s.map_values(|c: u32| c as u8),
{
    lemma_utf8_encode_ascii_from(s, 0);
    assert(s.skip(0) =~= s);
}

/// UTF-8 encode outputs an ASCII byte only for that code point: if a
/// scalar value string lacks ASCII code point `b`, its encoding lacks
/// byte `b`. From position `i`.
proof fn lemma_utf8_encode_lacks_from(s: Seq<u32>, b: u8, i: nat)
    requires
        clazel_encoding::utf8::spec::all_scalar_values(s),
        b <= 0x7F,
        lacks(s, b as u32),
        i <= s.len(),
    ensures
        forall|k: int|
            0 <= k < clazel_encoding::utf8::spec::encoder_process_queue(s, i).len()
                ==> #[trigger] clazel_encoding::utf8::spec::encoder_process_queue(s, i)[k] != b,
    decreases s.len() - i,
{
    if i < s.len() {
        let c = s[i as int];
        assert(clazel_encoding::utf8::spec::is_scalar_value(c));
        clazel_encoding::utf8::lemmas::lemma_encoder_bytes(c);
        lemma_utf8_encode_lacks_from(s, b, i + 1);
        let head = clazel_encoding::utf8::lemmas::encoded(c);
        let tail = clazel_encoding::utf8::spec::encoder_process_queue(s, i + 1);
        assert(forall|k: int| 0 <= k < head.len() ==> #[trigger] head[k] != b);
        assert(forall|k: int| 0 <= k < (head + tail).len() ==> #[trigger] (head + tail)[k] != b) by {
            assert forall|k: int| 0 <= k < (head + tail).len() implies #[trigger] (head + tail)[k]
                != b by {
                if k < head.len() {
                    assert((head + tail)[k] == head[k]);
                } else {
                    assert((head + tail)[k] == tail[k - head.len()]);
                }
            }
        }
    }
}

/// The ASCII upper hex digit for `n` < 16 is in percent-decode's ranges,
/// with value `n`.
proof fn lemma_upper_hex_digit(n: u8)
    requires
        n < 16,
    ensures
        ascii_upper_hex_digit(n) <= 0x7F,
        in_hex_ranges(ascii_upper_hex_digit(n) as u8),
        hex_value(ascii_upper_hex_digit(n) as u8) == n,
{
}

/// `percent_decode_from` looks only at the bytes from its position on.
proof fn lemma_decode_shift(p: Seq<u8>, y: Seq<u8>, j: nat)
    requires
        j <= y.len(),
    ensures
        percent_decode_from(p + y, p.len() + j) == percent_decode_from(y, j),
    decreases y.len() - j,
{
    let z = p + y;
    let n = p.len() as int;
    let jj = j as int;
    if j < y.len() {
        assert(z[n + jj] == y[jj]);
        if j + 1 < y.len() {
            assert(z[n + jj + 1] == y[jj + 1]);
        }
        if j + 2 < y.len() {
            assert(z[n + jj + 2] == y[jj + 2]);
            lemma_decode_shift(p, y, j + 3);
            assert(n + j + 3 == n + (j + 3));
        }
        lemma_decode_shift(p, y, j + 1);
        assert(n + j + 1 == n + (j + 1));
    }
}

/// The bytes of the output of step 7.3 for one byte `b`, decoded, are `b`,
/// provided `b` is not a U+0025 (%) the set leaves alone or a space that
/// becomes "+".
proof fn lemma_decode_output_byte(set: PercentEncodeSet, space_as_plus: bool, b: u8, y: Seq<u8>)
    requires
        b == 0x25 ==> contains(set, 0x25),
        space_as_plus ==> b != 0x20,
    ensures
        all_ascii(encode_output_byte(set, space_as_plus, b)),
        percent_decode_from(encode_output_byte(set, space_as_plus, b).map_values(|c: u32| c as u8) + y, 0)
            == seq![b] + percent_decode_from(y, 0),
{
    let x = encode_output_byte(set, space_as_plus, b).map_values(|c: u32| c as u8);
    lemma_decode_shift(x, y, 0);
    if !contains(set, b as u32) {
        if b > 0x7F {
            lemma_sets_include_non_ascii(set, b as u32);
        }
        assert(x =~= seq![b]);
        assert((x + y)[0] == b);
    } else {
        lemma_upper_hex_digit(b / 16);
        lemma_upper_hex_digit(b % 16);
        assert(x =~= seq![0x25u8, ascii_upper_hex_digit(b / 16) as u8, ascii_upper_hex_digit(b % 16) as u8]);
        assert((x + y)[0] == 0x25 && (x + y)[1] == x[1] && (x + y)[2] == x[2]);
        assert(16 * (b / 16) + b % 16 == b);
    }
}

/// Step 7.3 from position `i`, decoded, gives `bytes` from `i` back.
proof fn lemma_decode_output_bytes(set: PercentEncodeSet, space_as_plus: bool, bytes: Seq<u8>, i: nat)
    requires
        i <= bytes.len(),
        forall|k: int| 0 <= k < bytes.len() && #[trigger] bytes[k] == 0x25 ==> contains(set, 0x25),
        forall|k: int| 0 <= k < bytes.len() && space_as_plus ==> #[trigger] bytes[k] != 0x20,
    ensures
        all_ascii(encode_output_bytes(set, space_as_plus, bytes, i)),
        percent_decode(encode_output_bytes(set, space_as_plus, bytes, i).map_values(|c: u32| c as u8))
            == bytes.skip(i as int),
    decreases bytes.len() - i,
{
    let out = encode_output_bytes(set, space_as_plus, bytes, i);
    if i < bytes.len() {
        let b = bytes[i as int];
        let head = encode_output_byte(set, space_as_plus, b);
        let tail = encode_output_bytes(set, space_as_plus, bytes, i + 1);
        lemma_decode_output_bytes(set, space_as_plus, bytes, i + 1);
        lemma_decode_output_byte(set, space_as_plus, b, tail.map_values(|c: u32| c as u8));
        assert(out == head + tail);
        assert(out.map_values(|c: u32| c as u8) =~= head.map_values(|c: u32| c as u8) + tail.map_values(
            |c: u32| c as u8,
        ));
        assert(bytes.skip(i as int) =~= seq![b] + bytes.skip(i + 1int));
        assert forall|k: int| 0 <= k < out.len() implies #[trigger] out[k] <= 0x7F by {
            if k < head.len() {
                assert(out[k] == head[k]);
            } else {
                assert(out[k] == tail[k - head.len()]);
            }
        }
    } else {
        assert(out.map_values(|c: u32| c as u8) =~= seq![]);
        assert(bytes.skip(i as int) =~= seq![]);
    }
}

/// For every byte, percent-decoding its percent-encoding gives it back.
pub proof fn lemma_decode_percent_encode(b: u8)
    ensures
        percent_decode_string(percent_encode(b)) == seq![b],
{
    let s = percent_encode(b);
    lemma_upper_hex_digit(b / 16);
    lemma_upper_hex_digit(b % 16);
    assert(all_ascii(s));
    lemma_utf8_encode_ascii(s);
    let x = s.map_values(|c: u32| c as u8);
    let empty: Seq<u8> = seq![];
    assert(x + empty =~= x);
    lemma_decode_shift(x, empty, 0);
    assert(x[0] == 0x25 && x[1] == ascii_upper_hex_digit(b / 16) as u8 && x[2]
        == ascii_upper_hex_digit(b % 16) as u8);
    assert(16 * (b / 16) + b % 16 == b);
    assert(seq![b] + empty =~= seq![b]);
}

/// Decoding inverts encoding: for every percent-encode set and scalar
/// value string `s`, percent-decoding the UTF-8 percent-encoding of `s` is
/// the UTF-8 encoding of `s`, whenever the set encodes U+0025 (%) or `s`
/// has none, and the set is not application/x-www-form-urlencoded or `s`
/// has no U+0020 SPACE.
pub proof fn lemma_decode_inverts_encode(s: Seq<u32>, set: PercentEncodeSet)
    requires
        clazel_encoding::utf8::spec::all_scalar_values(s),
        contains(set, 0x25) || lacks(s, 0x25),
        set != PercentEncodeSet::ApplicationXWwwFormUrlencoded || lacks(s, 0x20),
    ensures
        percent_decode_string(utf8_percent_encode(s, set)) == clazel_encoding::utf8::spec::utf8_encode(s),
{
    let bytes = clazel_encoding::utf8::spec::utf8_encode(s);
    let space_as_plus = set == PercentEncodeSet::ApplicationXWwwFormUrlencoded;
    if !contains(set, 0x25) {
        lemma_utf8_encode_lacks_from(s, 0x25, 0);
    }
    if space_as_plus {
        lemma_utf8_encode_lacks_from(s, 0x20, 0);
    }
    lemma_decode_output_bytes(set, space_as_plus, bytes, 0);
    let out = encode_output_bytes(set, space_as_plus, bytes, 0);
    lemma_utf8_encode_ascii(out);
    assert(bytes.skip(0) =~= bytes);
}

} // verus!
