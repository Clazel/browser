//! Facts proven about the UTF-8 spec in [`super::spec`]. They do not
//! constrain the implementation directly; they show the transcription
//! behaves as the standard says it should, which is evidence that the
//! transcription is right.
//!
//! Main results:
//! - [`lemma_output_scalar_values`]: for every input and either error mode,
//!   the decoder outputs only Unicode scalar values. The standard *asserts*
//!   this (§4.1 process an item, step 6.1: "result does not contain any
//!   surrogates"); here it is proven.
//! - [`lemma_replacement_never_fails`]: "replacement" mode never returns an
//!   error, so `utf8_decode` is total.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Boundaries are the defaults 0x80 / 0xBF.
pub open spec fn default_bounds(d: Utf8Decoder) -> bool {
    d.lower_boundary == 0x80 && d.upper_boundary == 0xBF
}

/// The states reachable by the handler from the initial state, by bytes
/// needed and bytes seen. `code_point` holds the bits decoded so far, and
/// its range is exactly what the lead byte and boundaries allow.
pub open spec fn reachable(d: Utf8Decoder) -> bool {
    &&& d.bytes_needed <= 3
    &&& (d.bytes_needed == 0 ==> d.bytes_seen == 0 && default_bounds(d))
    &&& (d.bytes_needed > 0 ==> d.bytes_seen < d.bytes_needed)
    // Two-byte sequences, after C2..DF.
    &&& (d.bytes_needed == 1 ==> 0x2 <= d.code_point <= 0x1F && default_bounds(d))
    // Three-byte sequences, after E0..EF. E0 forbids overlongs; ED forbids surrogates.
    &&& (d.bytes_needed == 2 && d.bytes_seen == 0 ==> {
        &&& d.code_point <= 0xF
        &&& d.lower_boundary == (if d.code_point == 0 { 0xA0u8 } else { 0x80u8 })
        &&& d.upper_boundary == (if d.code_point == 0xD { 0x9Fu8 } else { 0xBFu8 })
    })
    &&& (d.bytes_needed == 2 && d.bytes_seen == 1 ==> {
        &&& 0x20 <= d.code_point <= 0x3FF
        &&& !(0x360 <= d.code_point <= 0x37F)
        &&& default_bounds(d)
    })
    // Four-byte sequences, after F0..F4. F0 forbids overlongs; F4 caps at U+10FFFF.
    &&& (d.bytes_needed == 3 && d.bytes_seen == 0 ==> {
        &&& d.code_point <= 4
        &&& d.lower_boundary == (if d.code_point == 0 { 0x90u8 } else { 0x80u8 })
        &&& d.upper_boundary == (if d.code_point == 4 { 0x8Fu8 } else { 0xBFu8 })
    })
    &&& (d.bytes_needed == 3 && d.bytes_seen == 1 ==> 0x10 <= d.code_point <= 0x10F && default_bounds(d))
    &&& (d.bytes_needed == 3 && d.bytes_seen == 2 ==> 0x400 <= d.code_point <= 0x43FF && default_bounds(d))
}

/// Spec step 6's bit operation is arithmetic for a continuation byte:
/// `(cp << 6) | (byte & 0x3F) == cp * 64 + (byte - 0x80)`.
pub proof fn lemma_shift_or(cp: u32, byte: u8)
    requires
        cp <= 0x43FF,
        0x80 <= byte <= 0xBF,
    ensures
        (cp << 6u32) | ((byte & 0x3F) as u32) == cp * 64 + (byte - 0x80),
{
    assert((byte & 0x3F) == byte - 0x80) by (bit_vector)
        requires 0x80 <= byte <= 0xBF;
    let low: u32 = (byte & 0x3F) as u32;
    assert((cp << 6u32) | low == cp * 64 + low) by (bit_vector)
        requires cp <= 0x43FF, low < 64;
}

/// Lead-byte masks used in step 3.
pub proof fn lemma_lead_masks(byte: u8)
    ensures
        0xC2 <= byte <= 0xDF ==> 0x2 <= (byte & 0x1F) <= 0x1F,
        0xE0 <= byte <= 0xEF ==> (byte & 0xF) == byte - 0xE0,
        0xF0 <= byte <= 0xF4 ==> (byte & 0x7) == byte - 0xF0,
{
    assert(0xC2 <= byte <= 0xDF ==> 0x2 <= (byte & 0x1F) <= 0x1F) by (bit_vector);
    assert(0xE0 <= byte <= 0xEF ==> (byte & 0xF) == byte - 0xE0) by (bit_vector);
    assert(0xF0 <= byte <= 0xF4 ==> (byte & 0x7) == byte - 0xF0) by (bit_vector);
}

/// One handler step on a byte preserves `reachable`, and any code point it
/// returns is a scalar value.
pub proof fn lemma_handler_byte(d: Utf8Decoder, byte: u8)
    requires
        reachable(d),
    ensures
        reachable(handler(d, Item::Byte(byte)).decoder),
        handler(d, Item::Byte(byte)).result matches HandlerResult::CodePoint(c) ==> is_scalar_value(c),
{
    lemma_lead_masks(byte);
    if d.bytes_needed != 0 && d.lower_boundary <= byte <= d.upper_boundary {
        lemma_shift_or(d.code_point, byte);
    }
}

/// End-of-queue never yields a code point, and leaves bytes needed at 0.
pub proof fn lemma_handler_end(d: Utf8Decoder)
    ensures
        !(handler(d, Item::EndOfQueue).result matches HandlerResult::CodePoint(_)),
        handler(d, Item::EndOfQueue).decoder.bytes_needed == 0,
        handler(d, Item::EndOfQueue).result matches HandlerResult::Finished <==> d.bytes_needed == 0,
{
}

/// Prepending a scalar value keeps all outputs scalar.
pub proof fn lemma_cons_scalar(c: u32, rest: Option<Seq<u32>>)
    requires
        is_scalar_value(c),
        rest matches Some(out) ==> all_scalar_values(out),
    ensures
        cons(c, rest) matches Some(out) ==> all_scalar_values(out),
{
    if let Some(out) = rest {
        let full = seq![c] + out;
        assert forall|k: int| 0 <= k < full.len() implies is_scalar_value(#[trigger] full[k]) by {
            if k > 0 {
                assert(full[k] == out[k - 1]);
            }
        }
    }
}

/// From any reachable state (or, at end-of-queue, any state with bytes
/// needed 0), process a queue outputs only scalar values.
pub proof fn lemma_process_queue_scalar(mode: ErrorMode, d: Utf8Decoder, input: Seq<u8>, i: nat)
    requires
        i <= input.len(),
        reachable(d) || (i == input.len() && d.bytes_needed == 0),
    ensures
        process_queue(mode, d, input, i) matches Some(out) ==> all_scalar_values(out),
    decreases input.len() - i, if d.bytes_needed == 0 { 0int } else { 1int }
{
    let s = handler(d, item_at(input, i));
    let j = next_position(input, i, s);
    if i < input.len() {
        lemma_handler_byte(d, input[i as int]);
    } else {
        lemma_handler_end(d);
    }
    match s.result {
        HandlerResult::Finished => {},
        HandlerResult::CodePoint(c) => {
            lemma_process_queue_scalar(mode, s.decoder, input, j);
            lemma_cons_scalar(c, process_queue(mode, s.decoder, input, j));
        },
        HandlerResult::Error => {
            if mode is Replacement {
                lemma_process_queue_scalar(mode, s.decoder, input, j);
                lemma_cons_scalar(0xFFFD, process_queue(mode, s.decoder, input, j));
            }
        },
        HandlerResult::Continue => {
            lemma_process_queue_scalar(mode, s.decoder, input, j);
        },
    }
}

/// "replacement" mode never returns an error.
pub proof fn lemma_process_queue_replacement_some(d: Utf8Decoder, input: Seq<u8>, i: nat)
    requires
        i <= input.len(),
    ensures
        process_queue(ErrorMode::Replacement, d, input, i) is Some,
    decreases input.len() - i, if d.bytes_needed == 0 { 0int } else { 1int }
{
    let s = handler(d, item_at(input, i));
    let j = next_position(input, i, s);
    if !(s.result is Finished) {
        lemma_process_queue_replacement_some(s.decoder, input, j);
    }
}

/// The UTF-8 decoder outputs only scalar values, for every input, in both
/// error modes. This proves the assertion in §4.1 process an item step 6.1.
pub proof fn lemma_output_scalar_values(mode: ErrorMode, input: Seq<u8>)
    ensures
        process_queue(mode, initial_decoder(), input, 0) matches Some(out) ==> all_scalar_values(out),
{
    lemma_process_queue_scalar(mode, initial_decoder(), input, 0);
}

/// "UTF-8 decode without BOM" never hits the unreachable `seq![]` fallback.
pub proof fn lemma_replacement_never_fails(input: Seq<u8>)
    ensures
        process_queue(ErrorMode::Replacement, initial_decoder(), input, 0) is Some,
{
    lemma_process_queue_replacement_some(initial_decoder(), input, 0);
}

/// Every hook in §6 outputs only scalar values.
pub proof fn lemma_hooks_scalar(input: Seq<u8>)
    ensures
        all_scalar_values(utf8_decode_without_bom(input)),
        all_scalar_values(utf8_decode(input)),
        utf8_decode_without_bom_or_fail(input) matches Some(out) ==> all_scalar_values(out),
{
    lemma_output_scalar_values(ErrorMode::Replacement, input);
    lemma_replacement_never_fails(input);
    lemma_output_scalar_values(ErrorMode::Fatal, input);
    if starts_with_bom(input) {
        let rest = input.subrange(3, input.len() as int);
        lemma_output_scalar_values(ErrorMode::Replacement, rest);
        lemma_replacement_never_fails(rest);
    }
}

} // verus!
