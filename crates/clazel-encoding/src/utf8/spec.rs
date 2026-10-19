//! Executable-style specification of UTF-8 decoding, transcribed from the
//! WHATWG Encoding Standard. Nothing here runs; it defines what "correct"
//! means. Every definition cites the standard, and each `// N.` comment is
//! the step number in the cited algorithm.
//!
//! Modelling choices (each one is a deliberate, reviewable deviation in form,
//! never in meaning):
//! - An I/O queue of bytes is modelled as `input: Seq<u8>` plus a read
//!   position `i`. Position `input.len()` is end-of-queue, which "read"
//!   never removes (§3, read an item).
//! - "Restore byte to ioQueue" (§3 restore = list prepend) is modelled by
//!   *not* advancing `i`. This is equivalent because the restored byte is
//!   exactly the one just read from position `i`.
//! - The output I/O queue is a `Seq<u32>` of code points, with end-of-queue
//!   left implicit.
//!
//! Modelling choices for the encoder (§8.1.2, and "UTF-8 encode" in §6):
//! - An I/O queue of scalar values is `input: Seq<u32>` plus a read position
//!   `i`, with end-of-queue at `input.len()`, as for bytes. A `u32` that is
//!   not a scalar value can be represented but never occurs: §4.1 process
//!   an item, step 3, asserts the encoder never sees a surrogate, and the
//!   hook takes "an I/O queue of scalar values". The contract states this
//!   as a precondition (`contract::encode_requires`). For a `u32` above
//!   U+10FFFF the handler below takes the step 3 branch for U+10000 to
//!   U+10FFFF; the standard defines nothing there and nothing depends on it.
//! - The output I/O queue is a `Seq<u8>`, initially empty (the hooks'
//!   "default « »"), with end-of-queue left implicit.
//! - UTF-8's encoder's handler only ever returns finished or bytes (it has
//!   no error step; the standard notes "The UTF-8 encoder cannot return
//!   error"), so [`EncoderHandlerResult`] has only those two results.
//!   Process an item step 7, the only step that reads the error mode, is
//!   then unreachable, so the "html" mode of "encode" step 2 is not a
//!   parameter. Its assertions, steps 1 and 2, hold for an encoder in
//!   "html" mode.
//! - The handler's "unused" I/O queue argument is omitted.
//! - The handler's while loop (step 5) is the recursive
//!   [`encoder_while_count`], with `bytes` as an accumulator.

#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// An item read from an I/O queue of bytes (§3, I/O queue).
pub enum Item {
    /// A byte.
    Byte(u8),
    /// end-of-queue.
    EndOfQueue,
}

/// A handler's result (§4.1, handler): finished, one item, error, or continue.
/// The UTF-8 decoder never returns more than one item, nor an error with a
/// code point.
pub enum HandlerResult {
    /// finished
    Finished,
    /// "a code point whose value is" the payload
    CodePoint(u32),
    /// error
    Error,
    /// continue
    Continue,
}

/// Error mode for a decoder (§4.1, error mode).
pub enum ErrorMode {
    /// "replacement": push U+FFFD and keep going.
    Replacement,
    /// "fatal": stop and return the error.
    Fatal,
}

/// UTF-8's decoder's associated state (§8.1.1).
pub struct Utf8Decoder {
    /// UTF-8 code point
    pub code_point: u32,
    /// UTF-8 bytes seen
    pub bytes_seen: nat,
    /// UTF-8 bytes needed
    pub bytes_needed: nat,
    /// UTF-8 lower boundary
    pub lower_boundary: u8,
    /// UTF-8 upper boundary
    pub upper_boundary: u8,
}

/// The decoder state, with the initial values listed in §8.1.1:
/// "Each a number, initially 0", lower boundary "initially 0x80", upper
/// boundary "initially 0xBF".
pub open spec fn initial_decoder() -> Utf8Decoder {
    Utf8Decoder {
        code_point: 0,
        bytes_seen: 0,
        bytes_needed: 0,
        lower_boundary: 0x80,
        upper_boundary: 0xBF,
    }
}

/// The result of one handler invocation: the new decoder state, the
/// handler's return value, and whether the handler restored `byte` to the
/// input queue.
pub struct Step {
    /// Decoder state after the handler ran.
    pub decoder: Utf8Decoder,
    /// What the handler returned.
    pub result: HandlerResult,
    /// True if the handler ran "Restore byte to ioQueue".
    pub restored: bool,
}

/// Shorthand for a step that does not restore its byte.
pub open spec fn step(decoder: Utf8Decoder, result: HandlerResult) -> Step {
    Step { decoder, result, restored: false }
}

/// UTF-8's decoder's handler (§8.1.1, <https://encoding.spec.whatwg.org/#utf-8-decoder>).
pub open spec fn handler(d: Utf8Decoder, item: Item) -> Step {
    match item {
        Item::EndOfQueue => {
            if d.bytes_needed != 0 {
                // 1. "set UTF-8 bytes needed to 0 and return error."
                step(Utf8Decoder { bytes_needed: 0, ..d }, HandlerResult::Error)
            } else {
                // 2. "If byte is end-of-queue, then return finished."
                step(d, HandlerResult::Finished)
            }
        },
        Item::Byte(byte) => {
            if d.bytes_needed == 0 {
                // 3. "If UTF-8 bytes needed is 0, based on byte:"
                if byte <= 0x7F {
                    // 0x00 to 0x7F: "Return a code point whose value is byte."
                    step(d, HandlerResult::CodePoint(byte as u32))
                } else if 0xC2 <= byte <= 0xDF {
                    // 0xC2 to 0xDF: 3.1 bytes needed = 1; 3.2 code point = byte & 0x1F.
                    step(
                        Utf8Decoder { bytes_needed: 1, code_point: (byte & 0x1F) as u32, ..d },
                        HandlerResult::Continue,
                    )
                } else if 0xE0 <= byte <= 0xEF {
                    // 0xE0 to 0xEF:
                    step(
                        Utf8Decoder {
                            // 1. "If byte is 0xE0, then set UTF-8 lower boundary to 0xA0."
                            lower_boundary: if byte == 0xE0 { 0xA0 } else { d.lower_boundary },
                            // 2. "If byte is 0xED, then set UTF-8 upper boundary to 0x9F."
                            upper_boundary: if byte == 0xED { 0x9F } else { d.upper_boundary },
                            // 3. "Set UTF-8 bytes needed to 2."
                            bytes_needed: 2,
                            // 4. "Set UTF-8 code point to byte & 0xF."
                            code_point: (byte & 0xF) as u32,
                            ..d
                        },
                        HandlerResult::Continue,
                    )
                } else if 0xF0 <= byte <= 0xF4 {
                    // 0xF0 to 0xF4:
                    step(
                        Utf8Decoder {
                            // 1. "If byte is 0xF0, then set UTF-8 lower boundary to 0x90."
                            lower_boundary: if byte == 0xF0 { 0x90 } else { d.lower_boundary },
                            // 2. "If byte is 0xF4, then set UTF-8 upper boundary to 0x8F."
                            upper_boundary: if byte == 0xF4 { 0x8F } else { d.upper_boundary },
                            // 3. "Set UTF-8 bytes needed to 3."
                            bytes_needed: 3,
                            // 4. "Set UTF-8 code point to byte & 0x7."
                            code_point: (byte & 0x7) as u32,
                            ..d
                        },
                        HandlerResult::Continue,
                    )
                } else {
                    // Otherwise: "Return error."
                    step(d, HandlerResult::Error)
                }
                // ("Return continue." after the switch is folded into each
                // branch above; the 0x00-0x7F and Otherwise branches return
                // before reaching it.)
            } else if !(d.lower_boundary <= byte <= d.upper_boundary) {
                // 4. "If byte is not in the range UTF-8 lower boundary to UTF-8
                //    upper boundary, inclusive:"
                // 4.1 resets code point, bytes needed and bytes seen to 0, and
                //     the boundaries to 0x80 / 0xBF, which is exactly the
                //     initial state.
                // 4.2 "Restore byte to ioQueue."
                // 4.3 "Return error."
                Step { decoder: initial_decoder(), result: HandlerResult::Error, restored: true }
            } else {
                // 5. boundaries back to 0x80 / 0xBF.
                // 6. "Set UTF-8 code point to (UTF-8 code point << 6) | (byte & 0x3F)"
                let code_point = (d.code_point << 6u32) | ((byte & 0x3F) as u32);
                // 7. "Increase UTF-8 bytes seen by one."
                let bytes_seen = d.bytes_seen + 1;
                if bytes_seen != d.bytes_needed {
                    // 8. "If UTF-8 bytes seen is not equal to UTF-8 bytes
                    //    needed, then return continue."
                    step(
                        Utf8Decoder {
                            code_point,
                            bytes_seen,
                            bytes_needed: d.bytes_needed,
                            lower_boundary: 0x80,
                            upper_boundary: 0xBF,
                        },
                        HandlerResult::Continue,
                    )
                } else {
                    // 9. "Let codePoint be UTF-8 code point."
                    // 10. code point, bytes needed, bytes seen set to 0 (with
                    //     step 5's boundaries this is the initial state).
                    // 11. "Return a code point whose value is codePoint."
                    step(initial_decoder(), HandlerResult::CodePoint(code_point))
                }
            }
        },
    }
}

/// The item at read position `i` (§3, read an item): the byte there, or
/// end-of-queue once the bytes are exhausted.
pub open spec fn item_at(input: Seq<u8>, i: nat) -> Item {
    if i < input.len() {
        Item::Byte(input[i as int])
    } else {
        Item::EndOfQueue
    }
}

/// Where reading continues after a step: the restored byte, or the end-of-queue
/// that read never removes, is read again; otherwise the next byte is.
pub open spec fn next_position(input: Seq<u8>, i: nat, s: Step) -> nat {
    if i < input.len() && !s.restored {
        i + 1
    } else {
        i
    }
}

/// Prepend a code point to a successful output; propagate failure.
pub open spec fn cons(c: u32, rest: Option<Seq<u32>>) -> Option<Seq<u32>> {
    match rest {
        Some(out) => Some(seq![c] + out),
        None => None,
    }
}

/// "Process a queue" (§4.1, #concept-encoding-run), with "process an item"
/// (#concept-encoding-process) inlined, for UTF-8's decoder reading `input`
/// from position `i`. Returns the output code points, or `None` where the
/// standard returns an error (only possible in "fatal" mode).
///
/// Termination: every step either consumes a byte, or (restore, or the
/// end-of-queue error) moves bytes needed from non-zero to zero.
pub open spec fn process_queue(mode: ErrorMode, d: Utf8Decoder, input: Seq<u8>, i: nat) -> Option<Seq<u32>>
    decreases input.len() - i, if d.bytes_needed == 0 { 0int } else { 1int }
    when i <= input.len()
{
    // 1.1 "Let result be the result of processing an item with the result of
    //      reading from input": process an item, 4. run the handler.
    let s = handler(d, item_at(input, i));
    let j = next_position(input, i, s);
    match s.result {
        // process an item, 5. finished: push end-of-queue (implicit), return.
        HandlerResult::Finished => Some(seq![]),
        // 6. one or more items: push them to output.
        HandlerResult::CodePoint(c) => cons(c, process_queue(mode, s.decoder, input, j)),
        // 7. error, switch on mode.
        HandlerResult::Error => match mode {
            // "replacement": "Push U+FFFD (\u{FFFD}) to output."
            ErrorMode::Replacement => cons(0xFFFD, process_queue(mode, s.decoder, input, j)),
            // "fatal": "Return result."
            ErrorMode::Fatal => None,
        },
        // 1.2 "If result is not continue, then return result." Continue loops.
        HandlerResult::Continue => process_queue(mode, s.decoder, input, j),
    }
}

/// True if `input` starts with the UTF-8 byte order mark 0xEF 0xBB 0xBF.
///
/// Erratum: §3 "peek" says "For each n in the range 1 to number, inclusive:
/// ... append ioQueue[n]". Infra lists are zero-based, so read literally
/// this peeks at bytes 1..=3 instead of 0..=2, and "UTF-8 decode" step 2
/// would test the wrong bytes. We specify the evident intent (the first
/// three bytes), which is also what every shipping engine does.
pub open spec fn starts_with_bom(input: Seq<u8>) -> bool {
    input.len() >= 3 && input[0] == 0xEF && input[1] == 0xBB && input[2] == 0xBF
}

/// "UTF-8 decode without BOM" (§6, #utf-8-decode-without-bom).
pub open spec fn utf8_decode_without_bom(input: Seq<u8>) -> Seq<u32> {
    // 1. "Process a queue with an instance of UTF-8's decoder, ioQueue,
    //    output, and "replacement"." 2. "Return output."
    // In "replacement" mode the result is never `None` (lemmas::
    // lemma_replacement_never_fails); `seq![]` is unreachable.
    match process_queue(ErrorMode::Replacement, initial_decoder(), input, 0) {
        Some(out) => out,
        None => seq![],
    }
}

/// "UTF-8 decode" (§6, #utf-8-decode).
pub open spec fn utf8_decode(input: Seq<u8>) -> Seq<u32> {
    // 1. "Let buffer be the result of peeking three bytes from ioQueue"
    // 2. "If buffer is 0xEF 0xBB 0xBF, then read three bytes from ioQueue."
    let rest = if starts_with_bom(input) { input.subrange(3, input.len() as int) } else { input };
    // 3. process the queue in "replacement" mode; 4. return output.
    utf8_decode_without_bom(rest)
}

/// "UTF-8 decode without BOM or fail" (§6, #utf-8-decode-without-bom-or-fail).
/// `None` is "failure".
pub open spec fn utf8_decode_without_bom_or_fail(input: Seq<u8>) -> Option<Seq<u32>> {
    // 1. process the queue in "fatal" mode. 2. error => failure. 3. output.
    process_queue(ErrorMode::Fatal, initial_decoder(), input, 0)
}

/// An item read from an I/O queue of scalar values (§3, I/O queue).
pub enum ScalarItem {
    /// A scalar value.
    ScalarValue(u32),
    /// end-of-queue.
    EndOfQueue,
}

/// What UTF-8's encoder's handler returns (§4.1, handler): finished, or one
/// or more items, here bytes. See the modelling choices for the omitted
/// error and continue.
pub enum EncoderHandlerResult {
    /// finished
    Finished,
    /// the bytes returned, in order
    Bytes(Seq<u8>),
}

/// UTF-8's encoder's handler, step 5: "While count is greater than 0:".
/// `bytes` is what has been appended so far.
pub open spec fn encoder_while_count(code_point: u32, count: nat, bytes: Seq<u8>) -> Seq<u8>
    decreases count
{
    if count > 0 {
        // 5.1 "Set temp to codePoint >> (6 × (count − 1))."
        let temp = code_point >> ((6 * (count - 1)) as u32);
        // 5.2 "Append to bytes 0x80 | (temp & 0x3F)."
        let bytes = bytes.push((0x80u32 | (temp & 0x3Fu32)) as u8);
        // 5.3 "Decrease count by one."
        encoder_while_count(code_point, (count - 1) as nat, bytes)
    } else {
        bytes
    }
}

/// UTF-8's encoder's handler (§8.1.2, <https://encoding.spec.whatwg.org/#utf-8-encoder>),
/// given codePoint.
pub open spec fn encoder_handler(code_point: ScalarItem) -> EncoderHandlerResult {
    match code_point {
        // 1. "If codePoint is end-of-queue, then return finished."
        ScalarItem::EndOfQueue => EncoderHandlerResult::Finished,
        ScalarItem::ScalarValue(code_point) => {
            if code_point <= 0x7F {
                // 2. "If codePoint is an ASCII code point, then return a byte
                //    whose value is codePoint." (Infra: an ASCII code point
                //    is U+0000 NULL to U+007F DELETE, inclusive.)
                EncoderHandlerResult::Bytes(seq![code_point as u8])
            } else {
                // 3. "Set count and offset based on the range codePoint is in:"
                let (count, offset) = if 0x80 <= code_point <= 0x7FF {
                    // U+0080 to U+07FF, inclusive: 1 and 0xC0
                    (1nat, 0xC0u32)
                } else if 0x800 <= code_point <= 0xFFFF {
                    // U+0800 to U+FFFF, inclusive: 2 and 0xE0
                    (2nat, 0xE0u32)
                } else {
                    // U+10000 to U+10FFFF, inclusive: 3 and 0xF0 (see the
                    // modelling choices for values above U+10FFFF)
                    (3nat, 0xF0u32)
                };
                // 4. "Let bytes be a byte sequence whose first byte is
                //    (codePoint >> (6 × count)) + offset."
                let bytes = seq![((code_point >> ((6 * count) as u32)) + offset) as u8];
                // 5. the while loop; 6. "Return bytes bytes, in order."
                EncoderHandlerResult::Bytes(encoder_while_count(code_point, count, bytes))
            }
        },
    }
}

/// The item at read position `i` of a queue of scalar values (§3, read an
/// item): the scalar value there, or end-of-queue once they are exhausted.
pub open spec fn scalar_item_at(input: Seq<u32>, i: nat) -> ScalarItem {
    if i < input.len() {
        ScalarItem::ScalarValue(input[i as int])
    } else {
        ScalarItem::EndOfQueue
    }
}

/// "Process a queue" (§4.1, #concept-encoding-run), with "process an item"
/// (#concept-encoding-process) inlined, for UTF-8's encoder reading `input`
/// from position `i`. Returns the output bytes.
pub open spec fn encoder_process_queue(input: Seq<u32>, i: nat) -> Seq<u8>
    decreases input.len() - i
    when i <= input.len()
{
    // 1.1 "Let result be the result of processing an item with the result of
    //      reading from input": process an item, 4. run the handler.
    match encoder_handler(scalar_item_at(input, i)) {
        // process an item, 5. finished: push end-of-queue (implicit), return.
        // 1.2 "If result is not continue, then return result."
        EncoderHandlerResult::Finished => seq![],
        // 6. one or more items: 6.2 push them to output. (6.1 asserts only
        // about decoders.) 8. "Return continue.", so 1.2 loops.
        EncoderHandlerResult::Bytes(bytes) => bytes + encoder_process_queue(input, i + 1),
    }
}

/// "UTF-8 encode" (§6, #utf-8-encode): "return the result of encoding
/// ioQueue with encoding UTF-8 and output", where "encode" (§6 "Legacy
/// hooks for standards", #encode) is:
pub open spec fn utf8_encode(input: Seq<u32>) -> Seq<u8> {
    // 1. "Let encoder be the result of getting an encoder from encoding."
    //    (get an encoder: 1. the assertion holds for UTF-8; 2. "Return an
    //    instance of encoding's encoder." UTF-8's encoder has no state.)
    // 2. "Process a queue with encoder, ioQueue, output, and "html"."
    // 3. "Return output."
    encoder_process_queue(input, 0)
}

/// A Unicode scalar value: a code point that is not a surrogate (Infra §4.5).
pub open spec fn is_scalar_value(c: u32) -> bool {
    c <= 0x10FFFF && !(0xD800 <= c <= 0xDFFF)
}

/// Every element of `s` is a scalar value.
pub open spec fn all_scalar_values(s: Seq<u32>) -> bool {
    forall|k: int| 0 <= k < s.len() ==> is_scalar_value(#[trigger] s[k])
}

} // verus!
