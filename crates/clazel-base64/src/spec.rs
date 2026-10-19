//! Executable-style specification of forgiving base64, transcribed from the
//! WHATWG Infra Standard, §7 "Forgiving base64"
//! (<https://infra.spec.whatwg.org/#forgiving-base64>), Living Standard at
//! commit `459b7829230ad256a690dabd315db974469af8e7` (19 October 2026), and
//! from RFC 4648 §4 "Base 64 Encoding"
//! (<https://www.rfc-editor.org/rfc/rfc4648#section-4>), which
//! "forgiving-base64 encode" applies and "forgiving-base64 decode" step 8.1
//! cites for Table 1. Nothing here runs; it defines what "correct" means.
//! Each `// N.` comment is the step number in the cited algorithm.
//!
//! Modelling choices (each one is a deliberate, reviewable deviation in form,
//! never in meaning):
//! - A string is `Seq<u32>`, one element per code point (Infra §4.7: "a
//!   string is a sequence of ... code points"). A `u32` above U+10FFFF is
//!   not a code point and cannot occur in a string; nothing here depends on
//!   that, because every value other than the 65 alphabet characters and
//!   the five ASCII whitespace ones makes decode fail at step 4.
//! - A byte sequence is `Seq<u8>`.
//! - "forgiving-base64 encode" returns an ASCII string, which is a
//!   `Seq<u32>` of code points like every other string, so its output is
//!   exactly the type decode accepts.
//! - "Failure" is `None`.
//! - Decode step 2, "If data ends with one or two U+003D (=) code points,
//!   then remove them": when data ends with two or more, both of the last
//!   two are removed; when it ends with exactly one, that one is. A string
//!   that ends with two also ends with one, and removing only one would
//!   leave a "=" that fails step 4, so `ab==` would fail; WPT
//!   (`fetch/data-urls/resources/base64.json`: `ab==` is `[105]`) and every
//!   engine remove two. With three or more, which reading applies makes no
//!   difference: a "=" stays behind and step 4 fails.
//! - The "buffer that can have bits appended to it" (steps 6, 8.2, 8.3 and
//!   9) is [`Buffer`]: the number the appended bits spell, most
//!   significant bit first, and how many bits there are. Appending six bits
//!   `n` to a buffer is `bits * 64 + n`; "interpret them as 8-bit
//!   big-endian numbers" is division and remainder by powers of two;
//!   "discard the last four" is division by 16. These are the arithmetic
//!   meanings of those bit operations, exactly.
//! - "position", a position variable for data (Infra §4.7), is an index
//!   `position: nat`; it "points past the end of data" when
//!   `position >= data.len()`.
//! - Table 1 of RFC 4648 is [`table_1_encoding`], one branch per run of
//!   consecutive rows. Step 8.1, "Find the code point ... in the second
//!   column of Table 1. Let n be the number given in the first cell of the
//!   same row", is [`find_in_table_1`], which searches the rows in order.
//!   The "(pad) =" row has no value and is not searched (step 2 and step 4
//!   leave no "=" for step 8 to find).
//! - The loop of step 8 is the recursive [`decode_loop`], carrying output
//!   and buffer; step 9 is [`decode_step_9`].
//! - RFC 4648 §4's encoding process is [`encode_from`], one 24-bit group per
//!   recursive call, with cases (2) and (3) of its "special processing" as
//!   the last call. A group's bits are the number they spell, as for the
//!   buffer: "concatenating 3 8-bit input groups" is `a * 65536 + b * 256 +
//!   c`, and the k-th of the "4 concatenated 6-bit groups" is that number
//!   divided by `64^(3 - k)`, modulo 64.

#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------
// Infra §4.6 Code points: the definitions the algorithm uses.
// ---------------------------------------------------------------------------

/// "ASCII whitespace is U+0009 TAB, U+000A LF, U+000C FF, U+000D CR, or
/// U+0020 SPACE." (Infra §4.6, <https://infra.spec.whatwg.org/#ascii-whitespace>)
pub open spec fn is_ascii_whitespace(c: u32) -> bool {
    c == 0x09 || c == 0x0A || c == 0x0C || c == 0x0D || c == 0x20
}

/// "An ASCII digit is a code point in the range U+0030 (0) to U+0039 (9),
/// inclusive." (Infra §4.6)
pub open spec fn is_ascii_digit(c: u32) -> bool {
    0x30 <= c <= 0x39
}

/// "An ASCII upper alpha is a code point in the range U+0041 (A) to U+005A
/// (Z), inclusive." (Infra §4.6)
pub open spec fn is_ascii_upper_alpha(c: u32) -> bool {
    0x41 <= c <= 0x5A
}

/// "An ASCII lower alpha is a code point in the range U+0061 (a) to U+007A
/// (z), inclusive." (Infra §4.6)
pub open spec fn is_ascii_lower_alpha(c: u32) -> bool {
    0x61 <= c <= 0x7A
}

/// "An ASCII alpha is an ASCII upper alpha or ASCII lower alpha." (Infra §4.6)
pub open spec fn is_ascii_alpha(c: u32) -> bool {
    is_ascii_upper_alpha(c) || is_ascii_lower_alpha(c)
}

/// "An ASCII alphanumeric is an ASCII digit or ASCII alpha." (Infra §4.6)
pub open spec fn is_ascii_alphanumeric(c: u32) -> bool {
    is_ascii_digit(c) || is_ascii_alpha(c)
}

/// Decode step 4's list: "U+002B (+), U+002F (/), ASCII alphanumeric".
pub open spec fn is_step_4_allowed(c: u32) -> bool {
    c == 0x2B || c == 0x2F || is_ascii_alphanumeric(c)
}

/// U+003D (=), RFC 4648 Table 1's "(pad)".
pub open spec fn pad() -> u32 {
    0x3D
}

// ---------------------------------------------------------------------------
// RFC 4648 §4, Table 1: The Base 64 Alphabet.
// ---------------------------------------------------------------------------

/// Table 1's "Encoding" column for "Value" `value` (0 to 63).
pub open spec fn table_1_encoding(value: nat) -> u32 {
    if value <= 25 {
        // 0 A, 1 B, ..., 25 Z
        (0x41 + value) as u32
    } else if value <= 51 {
        // 26 a, 27 b, ..., 51 z
        (0x61 + (value - 26)) as u32
    } else if value <= 61 {
        // 52 0, 53 1, ..., 61 9
        (0x30 + (value - 52)) as u32
    } else if value == 62 {
        // 62 +
        0x2B
    } else {
        // 63 /
        0x2F
    }
}

/// Decode step 8.1: search Table 1's rows, from `row` to 63, for the one
/// whose second column is `c`, and return its first cell. Not found (only
/// for a code point step 4 has already rejected) gives 0.
pub open spec fn find_in_table_1(c: u32, row: nat) -> nat
    decreases 64 - row
{
    if row >= 64 {
        0
    } else if table_1_encoding(row) == c {
        row
    } else {
        find_in_table_1(c, row + 1)
    }
}

// ---------------------------------------------------------------------------
// Infra §7: forgiving-base64 decode.
// ---------------------------------------------------------------------------

/// Decode step 1, "Remove all ASCII whitespace from data" (Infra §5.1 list
/// "remove": remove all items that match the condition; a string is a
/// list of code points for this purpose). Recursion from the end.
pub open spec fn remove_ascii_whitespace(data: Seq<u32>) -> Seq<u32>
    decreases data.len()
{
    if data.len() == 0 {
        seq![]
    } else if is_ascii_whitespace(data.last()) {
        remove_ascii_whitespace(data.drop_last())
    } else {
        remove_ascii_whitespace(data.drop_last()).push(data.last())
    }
}

/// Decode step 2.1: "If data ends with one or two U+003D (=) code points,
/// then remove them from data." (See the modelling choices.)
pub open spec fn remove_trailing_padding(data: Seq<u32>) -> Seq<u32> {
    if data.len() >= 2 && data[data.len() - 1] == pad() && data[data.len() - 2] == pad() {
        data.subrange(0, data.len() - 2)
    } else if data.len() >= 1 && data[data.len() - 1] == pad() {
        data.subrange(0, data.len() - 1)
    } else {
        data
    }
}

/// Decode step 4's condition: "data contains a code point that is not one
/// of" U+002B (+), U+002F (/), ASCII alphanumeric. Recursion from the end.
pub open spec fn contains_disallowed(data: Seq<u32>) -> bool
    decreases data.len()
{
    if data.len() == 0 {
        false
    } else {
        !is_step_4_allowed(data.last()) || contains_disallowed(data.drop_last())
    }
}

/// "a buffer that can have bits appended to it" (step 6): `bits` is the
/// number the appended bits spell, most significant first; `len` is how many
/// bits it holds.
pub struct Buffer {
    /// The appended bits, read as a big-endian number.
    pub bits: nat,
    /// The number of bits appended since the buffer was last emptied.
    pub len: nat,
}

/// An empty buffer (step 6).
pub open spec fn empty_buffer() -> Buffer {
    Buffer { bits: 0, len: 0 }
}

/// What step 8 leaves behind: output and buffer.
pub struct DecodeState {
    /// output (step 5)
    pub output: Seq<u8>,
    /// buffer (step 6)
    pub buffer: Buffer,
}

/// Step 8: "While position does not point past the end of data:", from
/// `position`, with the output and buffer so far.
pub open spec fn decode_loop(data: Seq<u32>, position: nat, output: Seq<u8>, buffer: Buffer) -> DecodeState
    decreases data.len() - position
{
    if position >= data.len() {
        DecodeState { output, buffer }
    } else {
        // 8.1 "Find the code point pointed to by position in the second
        //     column of Table 1 ... Let n be the number given in the first
        //     cell of the same row."
        let n = find_in_table_1(data[position as int], 0);
        // 8.2 "Append the six bits corresponding to n, most significant bit
        //     first, to buffer."
        let buffer = Buffer { bits: buffer.bits * 64 + n, len: buffer.len + 6 };
        // 8.3 "If buffer has accumulated 24 bits, interpret them as three
        //     8-bit big-endian numbers. Append three bytes with values equal
        //     to those numbers to output, in the same order, and then empty
        //     buffer."
        let (output, buffer) = if buffer.len == 24 {
            (
                output + seq![
                    (buffer.bits / 65536) as u8,
                    (buffer.bits / 256 % 256) as u8,
                    (buffer.bits % 256) as u8,
                ],
                empty_buffer(),
            )
        } else {
            (output, buffer)
        };
        // 8.4 "Advance position by 1."
        decode_loop(data, position + 1, output, buffer)
    }
}

/// Step 9: "If buffer is not empty, it contains either 12 or 18 bits. If it
/// contains 12 bits, then discard the last four and interpret the remaining
/// eight as an 8-bit big-endian number. If it contains 18 bits, then discard
/// the last two and interpret the remaining 16 as two 8-bit big-endian
/// numbers. Append the one or two bytes with values equal to those one or
/// two numbers to output, in the same order."
///
/// The standard asserts that a non-empty buffer holds 12 or 18 bits
/// (`lemmas::lemma_step_9_assertion` proves it); any other length appends
/// nothing here, and is unreachable.
pub open spec fn decode_step_9(output: Seq<u8>, buffer: Buffer) -> Seq<u8> {
    if buffer.len == 12 {
        output.push((buffer.bits / 16) as u8)
    } else if buffer.len == 18 {
        let remaining = buffer.bits / 4;
        output + seq![(remaining / 256) as u8, (remaining % 256) as u8]
    } else {
        output
    }
}

/// "forgiving-base64 decode" (Infra §7, <https://infra.spec.whatwg.org/#forgiving-base64-decode>),
/// given a string `data`. `None` is failure.
pub open spec fn forgiving_base64_decode(data: Seq<u32>) -> Option<Seq<u8>> {
    // 1. "Remove all ASCII whitespace from data."
    let data = remove_ascii_whitespace(data);
    // 2. "If data's code point length divides by 4 leaving no remainder:"
    //    2.1 (see remove_trailing_padding)
    let data = if data.len() % 4 == 0 { remove_trailing_padding(data) } else { data };
    if data.len() % 4 == 1 {
        // 3. "If data's code point length divides by 4 leaving a remainder
        //    of 1, then return failure."
        None
    } else if contains_disallowed(data) {
        // 4. "If data contains a code point that is not one of U+002B (+),
        //    U+002F (/), ASCII alphanumeric then return failure."
        None
    } else {
        // 5. "Let output be an empty byte sequence."
        // 6. "Let buffer be an empty buffer that can have bits appended to it."
        // 7. "Let position be a position variable for data, initially
        //    pointing at the start of data."
        // 8. the loop.
        let state = decode_loop(data, 0, seq![], empty_buffer());
        // 9. the leftover bits; 10. "Return output."
        Some(decode_step_9(state.output, state.buffer))
    }
}

// ---------------------------------------------------------------------------
// Infra §7: forgiving-base64 encode, which is RFC 4648 §4.
// ---------------------------------------------------------------------------

/// RFC 4648 §4: "Each 6-bit group is used as an index into an array of 64
/// printable characters. The character referenced by the index is placed
/// in the output string."
pub open spec fn encode_6_bit_group(group: nat) -> u32 {
    table_1_encoding(group % 64)
}

/// RFC 4648 §4's encoding process for `data` from byte `i` on: "Proceeding
/// from left to right", one 24-bit input group per call.
pub open spec fn encode_from(data: Seq<u8>, i: nat) -> Seq<u32>
    decreases data.len() - i
{
    if i + 3 <= data.len() {
        // "a 24-bit input group is formed by concatenating 3 8-bit input
        // groups."
        let group: nat = data[i as int] as nat * 65536 + data[i as int + 1] as nat * 256 + data[i as int + 2] as nat;
        // "These 24 bits are then treated as 4 concatenated 6-bit groups,
        // each of which is translated into a single character in the base 64
        // alphabet."
        seq![
            encode_6_bit_group(group / 262144),
            encode_6_bit_group(group / 4096),
            encode_6_bit_group(group / 64),
            encode_6_bit_group(group),
        ] + encode_from(data, i + 3)
    } else if i + 1 == data.len() {
        // "Special processing is performed if fewer than 24 bits are
        // available at the end of the data being encoded. ... When fewer
        // than 24 input bits are available in an input group, bits with
        // value zero are added (on the right) to form an integral number of
        // 6-bit groups."
        // (2) "The final quantum of encoding input is exactly 8 bits; here,
        // the final unit of encoded output will be two characters followed
        // by two "=" padding characters." 8 bits and 4 zero bits: 12 bits.
        let group: nat = data[i as int] as nat * 16;
        seq![encode_6_bit_group(group / 64), encode_6_bit_group(group), pad(), pad()]
    } else if i + 2 == data.len() {
        // (3) "The final quantum of encoding input is exactly 16 bits; here,
        // the final unit of encoded output will be three characters followed
        // by one "=" padding character." 16 bits and 2 zero bits: 18 bits.
        let group: nat = (data[i as int] as nat * 256 + data[i as int + 1] as nat) * 4;
        seq![
            encode_6_bit_group(group / 4096),
            encode_6_bit_group(group / 64),
            encode_6_bit_group(group),
            pad(),
        ]
    } else {
        // (1) "The final quantum of encoding input is an integral multiple
        // of 24 bits; here, the final unit of encoded output will be an
        // integral multiple of 4 characters with no "=" padding." All groups
        // are done.
        seq![]
    }
}

/// "forgiving-base64 encode" (Infra §7, <https://infra.spec.whatwg.org/#forgiving-base64-encode>):
/// "apply the base64 algorithm defined in section 4 of RFC 4648 to data and
/// return the result."
pub open spec fn forgiving_base64_encode(data: Seq<u8>) -> Seq<u32> {
    encode_from(data, 0)
}

} // verus!
