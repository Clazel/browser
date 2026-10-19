//! Executable-style specification of percent-encoded bytes, transcribed
//! from the WHATWG URL Standard, §1.3 "Percent-encoded bytes"
//! (<https://url.spec.whatwg.org/#percent-encoded-bytes>; source `url.bs`
//! at commit `845bafca22fb0c5a42c4bf384a9bdea525a2f10d`, 19 October 2026).
//! Nothing here runs; it defines what "correct" means. Every definition
//! cites the standard, and each `// N.` comment is the step number in the
//! cited algorithm.
//!
//! Modelling choices (each one is a deliberate, reviewable deviation in form,
//! never in meaning):
//! - A byte sequence is `Seq<u8>`. A string is a `Seq<u32>` of code points,
//!   as in `clazel-encoding`; a scalar value string is one whose elements
//!   are all scalar values (`all_scalar_values`), which the contracts
//!   require of their inputs.
//! - A percent-encode set (a set of code points) is a [`PercentEncodeSet`]
//!   naming one of the eight sets the standard defines, with
//!   [`contains`] as membership. Each set is a predicate on `u32`, written
//!   as the standard words it ("the C0 control percent-encode set and
//!   U+0020 SPACE, ..."). A `u32` above U+10FFFF is not a code point and
//!   is in no set; the algorithms below only ever test isomorphs of bytes.
//! - "For each byte byte in input" with "skip the next two bytes"
//!   (percent-decode, step 2) is the recursive [`percent_decode_from`]
//!   over a read position `i`: skipping is advancing `i` by three instead
//!   of one. "Append to output" is building the result front to back, so
//!   `output` is the bytes appended before position `i` followed by
//!   `percent_decode_from(input, i)`.
//! - "Percent-encode after encoding" is transcribed for `encoding` UTF-8
//!   only ([`percent_encode_after_encoding_utf8`]). Other encodings need
//!   their encoders, which arrive with HTML (docs/phases/phase-1.md); WPT
//!   rows for them are expected failures in `tests/conformance_percent.rs`.
//!   With UTF-8:
//!   - step 1's assertion holds (encoding is UTF-8);
//!   - "encode or fail" (Encoding §6) with UTF-8's encoder returns null and
//!     outputs "UTF-8 encode" of the whole queue, because UTF-8's encoder
//!     never returns error (Encoding §8.1.2: "The UTF-8 encoder cannot
//!     return error"), so "process a queue" runs to end-of-queue and returns
//!     finished. [`encode_or_fail_utf8`] is that result, built from
//!     `clazel-encoding`'s proven `utf8_encode` rather than a second
//!     transcription;
//!   - step 7's loop therefore runs exactly once: step 6 sets
//!     potentialError to 0 (non-null), and the first step 7.2 sets it to
//!     null. Its body is written once, with step 7.4 a no-op on null;
//!   - steps 3 and 4 (get an encoder, convert to an I/O queue) have no
//!     state to model: UTF-8's encoder is stateless and the queue is the
//!     input sequence itself.
//! - "UTF-8 encoding" (percent-decode a string, step 1) is "UTF-8 encode"
//!   (Encoding §6), from `clazel-encoding`.

#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------
// Infra definitions the section uses (https://infra.spec.whatwg.org/).
// ---------------------------------------------------------------------

/// Infra §4.6: an ASCII digit is a code point in the range U+0030 (0) to
/// U+0039 (9), inclusive.
pub open spec fn is_ascii_digit(c: u32) -> bool {
    0x30 <= c <= 0x39
}

/// Infra §4.6: an ASCII upper hex digit is an ASCII digit or a code point
/// in the range U+0041 (A) to U+0046 (F), inclusive.
pub open spec fn is_ascii_upper_hex_digit(c: u32) -> bool {
    is_ascii_digit(c) || 0x41 <= c <= 0x46
}

/// Infra §4.6: an ASCII lower hex digit is an ASCII digit or a code point
/// in the range U+0061 (a) to U+0066 (f), inclusive.
pub open spec fn is_ascii_lower_hex_digit(c: u32) -> bool {
    is_ascii_digit(c) || 0x61 <= c <= 0x66
}

/// Infra §4.6: an ASCII hex digit is an ASCII upper hex digit or ASCII
/// lower hex digit.
pub open spec fn is_ascii_hex_digit(c: u32) -> bool {
    is_ascii_upper_hex_digit(c) || is_ascii_lower_hex_digit(c)
}

/// Infra §4.6: a C0 control is a code point in the range U+0000 NULL to
/// U+001F INFORMATION SEPARATOR ONE, inclusive.
pub open spec fn is_c0_control(c: u32) -> bool {
    c <= 0x1F
}

/// Infra §4.6: a code point is a Unicode code point, U+0000 to U+10FFFF.
pub open spec fn is_code_point(c: u32) -> bool {
    c <= 0x10FFFF
}

/// The ASCII upper hex digit for the value `n`, 0 to 15. "Two ASCII upper
/// hex digits representing byte" (percent-encode) are the digits for
/// `byte / 16` and `byte % 16`, most significant first, as in the
/// standard's examples ("0x23" gives "%23").
pub open spec fn ascii_upper_hex_digit(n: u8) -> u32 {
    if n < 10 {
        (0x30 + n) as u32
    } else {
        (0x37 + n) as u32
    }
}

// ---------------------------------------------------------------------
// §1.3, first paragraph.
// ---------------------------------------------------------------------

/// "A percent-encoded byte is a string consisting of U+0025 (%) followed
/// by two ASCII hex digits": one starts at position `k` of `s`.
pub open spec fn is_percent_encoded_byte_at(s: Seq<u32>, k: int) -> bool {
    0 <= k && k + 2 < s.len() && s[k] == 0x25 && is_ascii_hex_digit(s[k + 1])
        && is_ascii_hex_digit(s[k + 2])
}

// ---------------------------------------------------------------------
// §1.3: percent-encode and percent-decode.
// ---------------------------------------------------------------------

/// "To percent-encode a byte byte, return a string consisting of U+0025
/// (%), followed by two ASCII upper hex digits representing byte."
/// (<https://url.spec.whatwg.org/#percent-encode>)
pub open spec fn percent_encode(byte: u8) -> Seq<u32> {
    seq![0x25u32, ascii_upper_hex_digit(byte / 16), ascii_upper_hex_digit(byte % 16)]
}

/// Percent-decode, step 2.2's ranges: "0x30 (0) to 0x39 (9), 0x41 (A) to
/// 0x46 (F), and 0x61 (a) to 0x66 (f), all inclusive".
pub open spec fn in_hex_ranges(b: u8) -> bool {
    (0x30 <= b <= 0x39) || (0x41 <= b <= 0x46) || (0x61 <= b <= 0x66)
}

/// The value of a byte in [`in_hex_ranges`], "interpreted as a hexadecimal
/// number" after isomorphic decoding: digits 0 to 9, then A to F (and a to
/// f) are 10 to 15.
pub open spec fn hex_value(b: u8) -> int {
    if 0x30 <= b <= 0x39 {
        b - 0x30
    } else if 0x41 <= b <= 0x46 {
        b - 0x37
    } else {
        b - 0x57
    }
}

/// Percent-decode's step 2 from read position `i` of `input`: the bytes
/// it appends to output from there on (see the modelling choices).
pub open spec fn percent_decode_from(input: Seq<u8>, i: nat) -> Seq<u8>
    decreases input.len() - i
    when i <= input.len()
{
    if i >= input.len() {
        // The for-each loop is done; 3. "Return output."
        seq![]
    } else {
        let byte = input[i as int];
        if byte != 0x25 {
            // 2.1 "If byte is not 0x25 (%), then append byte to output."
            seq![byte] + percent_decode_from(input, i + 1)
        } else if !(i + 2 < input.len() && in_hex_ranges(input[i + 1int])
            && in_hex_ranges(input[i + 2int])) {
            // 2.2 "Otherwise, if byte is 0x25 (%) and the next two bytes
            //     after byte in input are not in the ranges [...], append
            //     byte to output." "Not in the ranges" means not both are:
            //     the standard's example decodes `%1G` to `%1G`. Missing
            //     bytes (fewer than two after byte) are not in the ranges.
            seq![byte] + percent_decode_from(input, i + 1)
        } else {
            // 2.3 "Otherwise:"
            // 2.3.1 "Let bytePoint be the two bytes after byte in input,
            //       decoded, and then interpreted as a hexadecimal number."
            let byte_point = 16 * hex_value(input[i + 1int]) + hex_value(input[i + 2int]);
            // 2.3.2 "Append a byte whose value is bytePoint to output."
            // 2.3.3 "Skip the next two bytes in input."
            seq![byte_point as u8] + percent_decode_from(input, i + 3)
        }
    }
}

/// "To percent-decode a byte sequence input"
/// (<https://url.spec.whatwg.org/#percent-decode>).
pub open spec fn percent_decode(input: Seq<u8>) -> Seq<u8> {
    // 1. "Let output be an empty byte sequence."
    // 2. "For each byte byte in input:" (from position 0)
    percent_decode_from(input, 0)
}

/// "To percent-decode a scalar value string input"
/// (<https://url.spec.whatwg.org/#string-percent-decode>).
pub open spec fn percent_decode_string(input: Seq<u32>) -> Seq<u8> {
    // 1. "Let bytes be the UTF-8 encoding of input."
    let bytes = clazel_encoding::utf8::spec::utf8_encode(input);
    // 2. "Return the percent-decoding of bytes."
    percent_decode(bytes)
}

// ---------------------------------------------------------------------
// §1.3: the percent-encode sets.
// ---------------------------------------------------------------------

/// The percent-encode sets §1.3 defines ("A percent-encode set is a set of
/// code points").
#[derive(Clone, Copy, Debug)]
pub enum PercentEncodeSet {
    /// The C0 control percent-encode set.
    C0Control,
    /// The fragment percent-encode set.
    Fragment,
    /// The query percent-encode set.
    Query,
    /// The special-query percent-encode set.
    SpecialQuery,
    /// The path percent-encode set.
    Path,
    /// The userinfo percent-encode set.
    Userinfo,
    /// The component percent-encode set.
    Component,
    /// The `application/x-www-form-urlencoded` percent-encode set.
    ApplicationXWwwFormUrlencoded,
}

/// "The C0 control percent-encode set is a percent-encode set consisting of
/// C0 controls and all code points greater than U+007E (~)."
pub open spec fn in_c0_control_percent_encode_set(c: u32) -> bool {
    is_c0_control(c) || (is_code_point(c) && c > 0x7E)
}

/// "The fragment percent-encode set is a percent-encode set consisting of
/// the C0 control percent-encode set and U+0020 SPACE, U+0022 ("), U+003C
/// (<), U+003E (>), and U+0060 (`)."
pub open spec fn in_fragment_percent_encode_set(c: u32) -> bool {
    in_c0_control_percent_encode_set(c) || c == 0x20 || c == 0x22 || c == 0x3C || c == 0x3E
        || c == 0x60
}

/// "The query percent-encode set is a percent-encode set consisting of the
/// C0 control percent-encode set and U+0020 SPACE, U+0022 ("), U+0023 (#),
/// U+003C (<), and U+003E (>)."
pub open spec fn in_query_percent_encode_set(c: u32) -> bool {
    in_c0_control_percent_encode_set(c) || c == 0x20 || c == 0x22 || c == 0x23 || c == 0x3C
        || c == 0x3E
}

/// "The special-query percent-encode set is a percent-encode set
/// consisting of the query percent-encode set and U+0027 (')."
pub open spec fn in_special_query_percent_encode_set(c: u32) -> bool {
    in_query_percent_encode_set(c) || c == 0x27
}

/// "The path percent-encode set is a percent-encode set consisting of the
/// query percent-encode set and U+003F (?), U+005E (^), U+0060 (`), U+007B
/// ({), and U+007D (})."
pub open spec fn in_path_percent_encode_set(c: u32) -> bool {
    in_query_percent_encode_set(c) || c == 0x3F || c == 0x5E || c == 0x60 || c == 0x7B
        || c == 0x7D
}

/// "The userinfo percent-encode set is a percent-encode set consisting of
/// the path percent-encode set and U+002F (/), U+003A (:), U+003B (;),
/// U+003D (=), U+0040 (@), U+005B ([) to U+005D (]), inclusive, and U+007C
/// (|)."
pub open spec fn in_userinfo_percent_encode_set(c: u32) -> bool {
    in_path_percent_encode_set(c) || c == 0x2F || c == 0x3A || c == 0x3B || c == 0x3D
        || c == 0x40 || (0x5B <= c <= 0x5D) || c == 0x7C
}

/// "The component percent-encode set is a percent-encode set consisting of
/// the userinfo percent-encode set and U+0024 ($) to U+0026 (&), inclusive,
/// U+002B (+), and U+002C (,)."
pub open spec fn in_component_percent_encode_set(c: u32) -> bool {
    in_userinfo_percent_encode_set(c) || (0x24 <= c <= 0x26) || c == 0x2B || c == 0x2C
}

/// "The application/x-www-form-urlencoded percent-encode set is a
/// percent-encode set consisting of the component percent-encode set and
/// U+0021 (!), U+0027 (') to U+0029 RIGHT PARENTHESIS, inclusive, and
/// U+007E (~)."
pub open spec fn in_application_x_www_form_urlencoded_percent_encode_set(c: u32) -> bool {
    in_component_percent_encode_set(c) || c == 0x21 || (0x27 <= c <= 0x29) || c == 0x7E
}

/// "`set` includes `c`".
pub open spec fn contains(set: PercentEncodeSet, c: u32) -> bool {
    match set {
        PercentEncodeSet::C0Control => in_c0_control_percent_encode_set(c),
        PercentEncodeSet::Fragment => in_fragment_percent_encode_set(c),
        PercentEncodeSet::Query => in_query_percent_encode_set(c),
        PercentEncodeSet::SpecialQuery => in_special_query_percent_encode_set(c),
        PercentEncodeSet::Path => in_path_percent_encode_set(c),
        PercentEncodeSet::Userinfo => in_userinfo_percent_encode_set(c),
        PercentEncodeSet::Component => in_component_percent_encode_set(c),
        PercentEncodeSet::ApplicationXWwwFormUrlencoded =>
            in_application_x_www_form_urlencoded_percent_encode_set(c),
    }
}

// ---------------------------------------------------------------------
// §1.3: percent-encode after encoding, with UTF-8, and its two callers.
// ---------------------------------------------------------------------

/// What "encode or fail" (Encoding §6) returns: the bytes it put in output,
/// and potentialError (`None` is null).
pub struct EncodeOrFail {
    /// The bytes pushed to output.
    pub output: Seq<u8>,
    /// The returned value: null, or an unencodable code point's value.
    pub potential_error: Option<u32>,
}

/// "Encode or fail" with UTF-8's encoder, reading the whole of `input` (see
/// the modelling choices).
pub open spec fn encode_or_fail_utf8(input: Seq<u32>) -> EncodeOrFail {
    EncodeOrFail { output: clazel_encoding::utf8::spec::utf8_encode(input), potential_error: None }
}

/// Percent-encode after encoding, step 7.3's body for one `byte` of
/// encodeOutput: what it appends to output.
pub open spec fn encode_output_byte(set: PercentEncodeSet, space_as_plus: bool, byte: u8) -> Seq<u32> {
    if space_as_plus && byte == 0x20 {
        // 7.3.1 "If spaceAsPlus is true and byte is 0x20 (SP), then append
        //       U+002B (+) to output and continue."
        seq![0x2Bu32]
    } else {
        // 7.3.2 "Let isomorph be a code point whose value is byte's value."
        let isomorph = byte as u32;
        // 7.3.3 "Assert: percentEncodeSet includes all non-ASCII code
        //       points." (lemmas::lemma_sets_include_non_ascii)
        if !contains(set, isomorph) {
            // 7.3.4 "If isomorph is not in percentEncodeSet, then append
            //       isomorph to output."
            seq![isomorph]
        } else {
            // 7.3.5 "Otherwise, percent-encode byte and append the result to
            //       output."
            percent_encode(byte)
        }
    }
}

/// Step 7.3, "For each byte of encodeOutput converted to a byte sequence",
/// from position `i` of `bytes`: what it appends to output from there on.
pub open spec fn encode_output_bytes(set: PercentEncodeSet, space_as_plus: bool, bytes: Seq<u8>, i: nat) -> Seq<u32>
    decreases bytes.len() - i
    when i <= bytes.len()
{
    if i >= bytes.len() {
        seq![]
    } else {
        encode_output_byte(set, space_as_plus, bytes[i as int])
            + encode_output_bytes(set, space_as_plus, bytes, i + 1)
    }
}

/// "To percent-encode after encoding, given an encoding encoding, scalar
/// value string input, and a percent-encode set percentEncodeSet", with
/// encoding UTF-8 (<https://url.spec.whatwg.org/#string-percent-encode-after-encoding>).
pub open spec fn percent_encode_after_encoding_utf8(input: Seq<u32>, percent_encode_set: PercentEncodeSet) -> Seq<u32> {
    // 1. "Assert: encoding is UTF-8 or [...]": encoding is UTF-8.
    // 2. "Let spaceAsPlus be true if percentEncodeSet is
    //    application/x-www-form-urlencoded percent-encode set; otherwise
    //    false."
    let space_as_plus = percent_encode_set == PercentEncodeSet::ApplicationXWwwFormUrlencoded;
    // 3. "Let encoder be the result of getting an encoder from encoding."
    // 4. "Let inputQueue be input converted to an I/O queue."
    // 5. "Let output be the empty string."
    // 6. "Let potentialError be 0."
    // 7. "While potentialError is non-null:" (runs once; see the modelling
    //    choices)
    // 7.1 "Let encodeOutput be an empty I/O queue."
    // 7.2 "Set potentialError to the result of running encode or fail with
    //     inputQueue, encoder, and encodeOutput."
    let result = encode_or_fail_utf8(input);
    // 7.3 "For each byte of encodeOutput converted to a byte sequence:"
    // 7.4 "If potentialError is non-null, then append [...]": it is null.
    // 8. "Return output."
    encode_output_bytes(percent_encode_set, space_as_plus, result.output, 0)
}

/// "To UTF-8 percent-encode a scalar value scalarValue using a
/// percentEncodeSet, return the result of running percent-encode after
/// encoding with UTF-8, scalarValue as a string, and percentEncodeSet."
/// (<https://url.spec.whatwg.org/#utf-8-percent-encode>)
pub open spec fn utf8_percent_encode_code_point(scalar_value: u32, percent_encode_set: PercentEncodeSet) -> Seq<u32> {
    percent_encode_after_encoding_utf8(seq![scalar_value], percent_encode_set)
}

/// "To UTF-8 percent-encode a scalar value string input using a
/// percentEncodeSet, return the result of running percent-encode after
/// encoding with UTF-8, input, and percentEncodeSet."
/// (<https://url.spec.whatwg.org/#string-utf-8-percent-encode>)
pub open spec fn utf8_percent_encode(input: Seq<u32>, percent_encode_set: PercentEncodeSet) -> Seq<u32> {
    percent_encode_after_encoding_utf8(input, percent_encode_set)
}

} // verus!
