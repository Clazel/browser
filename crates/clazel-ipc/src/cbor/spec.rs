//! Executable-style specification of the IPC wire format's CBOR profile,
//! transcribed from RFC 8949 "Concise Binary Object Representation (CBOR)"
//! (December 2020, STD 94, <https://www.rfc-editor.org/rfc/rfc8949>), §3
//! "Specification of the CBOR Encoding" and §4.2.1 "Core Deterministic
//! Encoding Requirements". An RFC is immutable, so there is no commit to
//! pin; RFC 8949 obsoletes RFC 7049, whose Appendix C `independent.rs`
//! transcribes. Nothing here runs; it defines what "correct" means. Each
//! `// N.` comment is a step of the algorithm cited next to it.
//!
//! ## The profile
//!
//! The wire format accepts only these data items:
//! - major type 0 (unsigned integer), 2 (byte string), 3 (text string),
//!   4 (array), and the simple values false and true (major type 7,
//!   additional information 20 and 21);
//! - nothing else: no negative integers (1), maps (5), tags (6), floating
//!   point or other simple values (7), null, undefined, break, or any
//!   indefinite length (additional information 31);
//! - arguments in preferred serialization (§4.2.1: "arguments ... MUST be
//!   as short as possible"). A decoder rejects every other form, so each
//!   data item has exactly one encoding;
//! - a text string's bytes are valid UTF-8 (§3.1: "major type 3 ... a
//!   string of Unicode characters that are encoded as UTF-8"), checked by
//!   `clazel-encoding`'s "UTF-8 decode without BOM or fail" (Encoding
//!   §6), which is fatal on every error and leaves a leading U+FEFF alone;
//! - the input is exactly one data item: bytes after it are rejected
//!   (§5.1 "well-formed encoded CBOR data item" is one item; a frame holds
//!   exactly one).
//!
//! ## Modelling choices
//!
//! Each is a deviation in form, never in meaning, and the argument is given
//! here once:
//! - **An item is its pre-order token sequence.** RFC 8949 §3 defines a
//!   data item as a tree: an array's elements are data items. The spec
//!   represents the tree by the tokens in the order they appear on the
//!   wire, where an [`Token::Array`] token carries its element count and
//!   the elements' tokens follow it. This is a bijection with trees (the
//!   standard parse of a count-prefixed tree, which [`is_item`] checks), and
//!   it makes every function here a loop over tokens: decoding reads one
//!   token at a time, so its termination follows from the position
//!   advancing, with no recursion on the result of a call. The `independent.rs` transcription is also stated
//!   on token sequences.
//! - "The high-order 3 bits" and "the low-order 5 bits" of the initial byte
//!   are `ib / 32` and `ib % 32`, their arithmetic meanings.
//! - "An unsigned integer in network byte order" (§3, additional
//!   information 24 to 27) is [`be_value`]: the number the bytes spell,
//!   most significant first. Its inverse, used by the encoder, is
//!   [`be_bytes`].
//! - Arguments are `nat` while they are read, and become `u64` in a
//!   [`Token`]: that is lossless, because an argument is at most 8 bytes
//!   (`lemmas::lemma_argument_fits_u64`).
//! - "Failure" (a byte string that is not a well-formed item of the
//!   profile) is `None`.
//! - Positions are `nat` indices into the input, and a token's length in
//!   bytes is returned with it, so the decoder never "restores" anything.
//! - The count of items still owed, `pending`, replaces the standard's
//!   recursion into arrays: a token that is an array of `n` replaces one
//!   owed item by `n`, any other token discharges one. Decoding stops when
//!   none is owed ([`decode_from`]).

#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------
// Data model.
// ---------------------------------------------------------------------------

/// One token of a data item in the profile, in wire order. The payload of
/// a string is part of its token; an array's elements are the tokens that
/// follow it.
pub enum Token {
    /// Major type 0: "an unsigned integer in the range 0..2^64-1
    /// inclusive. The value of the encoded item is the argument itself."
    Uint(u64),
    /// Major type 2: "a byte string. The number of bytes in the string is
    /// equal to the argument."
    Bytes(Seq<u8>),
    /// Major type 3: "a text string, specifically a string of Unicode
    /// characters that is encoded as UTF-8". The bytes of the encoding;
    /// valid UTF-8 is a condition on every token the codec produces
    /// ([`token_ok`]).
    Text(Seq<u8>),
    /// Major type 7, additional information 20 (false) or 21 (true).
    Bool(bool),
    /// Major type 4: "an array of data items. The argument is the number
    /// of data items in the array." The items' tokens follow.
    Array(u64),
}

// ---------------------------------------------------------------------------
// §3: the initial byte and its argument.
// ---------------------------------------------------------------------------

/// "The initial byte of each encoded data item contains both information
/// about the major type (the high-order 3 bits ...)". (§3)
pub open spec fn major_type(ib: u8) -> u8 {
    ib / 32
}

/// "... and additional information (the low-order 5 bits)". (§3)
pub open spec fn additional_info(ib: u8) -> u8 {
    ib % 32
}

/// The number of bytes after the initial byte that hold the argument, per
/// §3: "When the value of the additional information is less than 24, it
/// is directly the argument"; 24, 25, 26 and 27 mean "a 1-byte, 2-byte,
/// 4-byte or 8-byte unsigned integer follows". 28 to 30 are "reserved ...
/// not well-formed", and 31 is indefinite length (or break), which the
/// profile does not accept: both give `None`.
pub open spec fn argument_bytes(ai: u8) -> Option<nat> {
    if ai < 24 {
        Some(0)
    } else if ai == 24 {
        Some(1)
    } else if ai == 25 {
        Some(2)
    } else if ai == 26 {
        Some(4)
    } else if ai == 27 {
        Some(8)
    } else {
        None
    }
}

/// "An unsigned integer in network byte order": the number `s` spells,
/// most significant byte first.
pub open spec fn be_value(s: Seq<u8>) -> nat
    decreases s.len()
{
    if s.len() == 0 {
        0
    } else {
        be_value(s.drop_last()) * 256 + s.last() as nat
    }
}

/// The argument of an initial byte with additional information `ai`
/// followed by `extra`: the additional information itself if it is less
/// than 24, and the unsigned integer in `extra` otherwise. (§3)
pub open spec fn argument_value(ai: u8, extra: Seq<u8>) -> nat {
    if ai < 24 {
        ai as nat
    } else {
        be_value(extra)
    }
}

/// §4.2.1: "Preferred serialization MUST be used. In particular, this
/// means that arguments ... MUST be as short as possible, for instance:
/// 0 to 23 ... in a single byte; 24 to 255 ... in two bytes; 256 to 65535
/// ... in three bytes; 65536 to 4294967295 ... in five bytes; 4294967296
/// to 18446744073709551615 ... in nine bytes." Whether `value`, encoded
/// with additional information `ai`, is in that shortest form.
pub open spec fn is_shortest(ai: u8, value: nat) -> bool {
    if ai < 24 {
        true
    } else if ai == 24 {
        value >= 24
    } else if ai == 25 {
        value >= 256
    } else if ai == 26 {
        value >= 65536
    } else {
        // ai == 27 (the others have no argument bytes)
        value >= 4294967296
    }
}

/// Read the initial byte and argument at `pos` (§3), rejecting any form
/// that is not preferred serialization (§4.2.1). Returns (major type,
/// argument, length of initial byte and argument in bytes).
pub open spec fn decode_head(b: Seq<u8>, pos: nat) -> Option<(u8, nat, nat)> {
    if pos >= b.len() {
        // The initial byte is missing.
        None
    } else {
        let ib = b[pos as int];
        let ai = additional_info(ib);
        match argument_bytes(ai) {
            None => None,
            Some(width) => {
                if pos + 1 + width > b.len() {
                    // The argument is truncated.
                    None
                } else {
                    let value = argument_value(ai, b.subrange(pos as int + 1, (pos + 1 + width) as int));
                    if is_shortest(ai, value) {
                        Some((major_type(ib), value, 1 + width))
                    } else {
                        None
                    }
                }
            },
        }
    }
}

/// Whether `s` is a valid text string body: valid UTF-8, decoded with
/// "UTF-8 decode without BOM or fail" (Encoding §6), which returns failure
/// on any error.
pub open spec fn utf8_valid(s: Seq<u8>) -> bool {
    clazel_encoding::utf8::spec::utf8_decode_without_bom_or_fail(s) is Some
}

/// Decode the data item's first token at `pos` (§3, major types 0, 2, 3, 4
/// and 7 as restricted by the profile). Returns the token and its length in
/// bytes, payload included.
pub open spec fn decode_token(b: Seq<u8>, pos: nat) -> Option<(Token, nat)> {
    if pos >= b.len() {
        None
    } else {
        let ib = b[pos as int];
        let major = major_type(ib);
        if major == 7 {
            // 7. Major type 7 (§3.3): only the simple values false (20) and
            //    true (21), which have no argument bytes. Floating point
            //    (25 to 27), other simple values (0 to 19, 24), null (22),
            //    undefined (23) and break (31) are outside the profile.
            let ai = additional_info(ib);
            if ai == 20 {
                Some((Token::Bool(false), 1))
            } else if ai == 21 {
                Some((Token::Bool(true), 1))
            } else {
                None
            }
        } else if major == 0 || major == 2 || major == 3 || major == 4 {
            match decode_head(b, pos) {
                None => None,
                Some((_, value, head_len)) => {
                    if major == 0 {
                        // 0. "an unsigned integer ... The value of the
                        //    encoded item is the argument itself."
                        Some((Token::Uint(value as u64), head_len))
                    } else if major == 4 {
                        // 4. "an array of data items. The argument is the
                        //    number of data items in the array."
                        Some((Token::Array(value as u64), head_len))
                    } else if pos + head_len + value > b.len() {
                        // 2, 3. The `value` bytes of the string are
                        //    missing.
                        None
                    } else {
                        let payload = b.subrange((pos + head_len) as int, (pos + head_len + value) as int);
                        if major == 2 {
                            // 2. "a byte string. The number of bytes in the
                            //    string is equal to the argument."
                            Some((Token::Bytes(payload), head_len + value))
                        } else if utf8_valid(payload) {
                            // 3. "a text string ... encoded as UTF-8".
                            Some((Token::Text(payload), head_len + value))
                        } else {
                            None
                        }
                    }
                },
            }
        } else {
            // 1 (negative integer), 5 (map), 6 (tag): outside the profile.
            None
        }
    }
}

/// The number of data items still to be read after `token`, given that
/// `pending` (at least 1) are owed before it: the token discharges one,
/// and an array of `n` owes its `n` elements.
pub open spec fn pending_after(pending: nat, token: Token) -> nat {
    match token {
        Token::Array(n) => (pending - 1 + n as nat) as nat,
        _ => (pending - 1) as nat,
    }
}

/// The decoding loop: read tokens from `pos` until no data item is owed,
/// then require the input to be used up. `acc` is the tokens read so far.
pub open spec fn decode_from(b: Seq<u8>, pos: nat, pending: nat, acc: Seq<Token>) -> Option<Seq<Token>>
    decreases b.len() - pos via decode_from_decreases
{
    if pending == 0 {
        // The item is complete: "exactly one" item fills the input.
        if pos == b.len() {
            Some(acc)
        } else {
            None
        }
    } else {
        match decode_token(b, pos) {
            None => None,
            Some((token, len)) => decode_from(b, pos + len, pending_after(pending, token), acc.push(token)),
        }
    }
}

/// Decode a byte string as one data item of the profile. `None` is
/// failure: the bytes are not the preferred serialization of one item of
/// the profile.
pub open spec fn decode(b: Seq<u8>) -> Option<Seq<Token>> {
    decode_from(b, 0, 1, seq![])
}

// ---------------------------------------------------------------------------
// Items: which token sequences are one data item of the profile.
// ---------------------------------------------------------------------------

/// A token the profile can encode: a text string must be valid UTF-8.
pub open spec fn token_ok(token: Token) -> bool {
    match token {
        Token::Text(s) => utf8_valid(s),
        _ => true,
    }
}

/// Whether `tokens` are the tokens of exactly `pending` consecutive data
/// items (§3: an array is followed by exactly its number of elements), each
/// token one the profile can encode.
pub open spec fn is_items(tokens: Seq<Token>, pending: nat) -> bool
    decreases tokens.len()
{
    if tokens.len() == 0 {
        pending == 0
    } else if pending == 0 {
        false
    } else {
        token_ok(tokens[0]) && is_items(tokens.drop_first(), pending_after(pending, tokens[0]))
    }
}

/// Whether `tokens` are one data item of the profile.
pub open spec fn is_item(tokens: Seq<Token>) -> bool {
    is_items(tokens, 1)
}

// ---------------------------------------------------------------------------
// §4.2.1: the encoder (preferred serialization).
// ---------------------------------------------------------------------------

/// The `width` bytes spelling `value` in network byte order, most
/// significant first (the inverse of [`be_value`] for `value < 256^width`).
pub open spec fn be_bytes(value: nat, width: nat) -> Seq<u8>
    decreases width
{
    if width == 0 {
        seq![]
    } else {
        be_bytes(value / 256, (width - 1) as nat).push((value % 256) as u8)
    }
}

/// The initial byte and argument of major type `major` and argument
/// `value` in preferred serialization (§4.2.1): the shortest form that
/// holds `value`.
pub open spec fn encode_head(major: u8, value: nat) -> Seq<u8> {
    if value < 24 {
        // "0 to 23 ... in a single byte"
        seq![(major * 32 + value) as u8]
    } else if value < 256 {
        // "24 to 255 ... in two bytes"
        seq![(major * 32 + 24) as u8] + be_bytes(value, 1)
    } else if value < 65536 {
        // "256 to 65535 ... in three bytes"
        seq![(major * 32 + 25) as u8] + be_bytes(value, 2)
    } else if value < 4294967296 {
        // "65536 to 4294967295 ... in five bytes"
        seq![(major * 32 + 26) as u8] + be_bytes(value, 4)
    } else {
        // "4294967296 to 18446744073709551615 ... in nine bytes"
        seq![(major * 32 + 27) as u8] + be_bytes(value, 8)
    }
}

/// The preferred serialization of one token.
pub open spec fn encode_token(token: Token) -> Seq<u8> {
    match token {
        Token::Uint(n) => encode_head(0, n as nat),
        Token::Bytes(s) => encode_head(2, s.len()) + s,
        Token::Text(s) => encode_head(3, s.len()) + s,
        // Major type 7 (§3.3): 20 is false and 21 is true; 7 * 32 = 224.
        Token::Bool(false) => seq![244u8],
        Token::Bool(true) => seq![245u8],
        Token::Array(n) => encode_head(4, n as nat),
    }
}

/// The preferred serialization of a token sequence: each token's, in order.
pub open spec fn encode(tokens: Seq<Token>) -> Seq<u8>
    decreases tokens.len()
{
    if tokens.len() == 0 {
        seq![]
    } else {
        encode_token(tokens[0]) + encode(tokens.drop_first())
    }
}

/// Termination of [`decode_from`]: every token is at least one byte, and
/// ends within the input.
#[via_fn]
pub proof fn decode_from_decreases(b: Seq<u8>, pos: nat, pending: nat, acc: Seq<Token>) {
    super::termination::lemma_decode_token_progress(b, pos);
}

} // verus!
