//! The executable UTF-8 decoder, proven to meet [`super::contract`].
//!
//! The code mirrors the spec: [`run_handler`] is UTF-8's decoder's handler
//! (§8.1.1) and [`process_queue`] is "process a queue" (§4.1). Each is
//! proven equal to its spec function, so the step comments live in
//! [`super::spec`] and are not repeated here.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// UTF-8's decoder's associated state, as machine integers.
struct Decoder {
    code_point: u32,
    bytes_seen: u8,
    bytes_needed: u8,
    lower_boundary: u8,
    upper_boundary: u8,
}

impl View for Decoder {
    type V = Utf8Decoder;

    closed spec fn view(&self) -> Utf8Decoder {
        Utf8Decoder {
            code_point: self.code_point,
            bytes_seen: self.bytes_seen as nat,
            bytes_needed: self.bytes_needed as nat,
            lower_boundary: self.lower_boundary,
            upper_boundary: self.upper_boundary,
        }
    }
}

impl Decoder {
    fn new() -> (d: Decoder)
        ensures
            d@ == initial_decoder(),
    {
        Decoder { code_point: 0, bytes_seen: 0, bytes_needed: 0, lower_boundary: 0x80, upper_boundary: 0xBF }
    }
}

/// UTF-8's decoder's handler. Returns the handler's result and whether it
/// restored `byte` to the queue.
fn run_handler(d: &mut Decoder, item: Item) -> (r: (HandlerResult, bool))
    requires
        item is Byte ==> super::lemmas::reachable(old(d)@),
    ensures
        final(d)@ == handler(old(d)@, item).decoder,
        r.0 == handler(old(d)@, item).result,
        r.1 == handler(old(d)@, item).restored,
{
    match item {
        Item::EndOfQueue => {
            if d.bytes_needed != 0 {
                d.bytes_needed = 0;
                (HandlerResult::Error, false)
            } else {
                (HandlerResult::Finished, false)
            }
        },
        Item::Byte(byte) => {
            if d.bytes_needed == 0 {
                match byte {
                    0x00..=0x7F => (HandlerResult::CodePoint(byte as u32), false),
                    0xC2..=0xDF => {
                        d.bytes_needed = 1;
                        d.code_point = (byte & 0x1F) as u32;
                        (HandlerResult::Continue, false)
                    },
                    0xE0..=0xEF => {
                    if byte == 0xE0 {
                        d.lower_boundary = 0xA0;
                    }
                    if byte == 0xED {
                        d.upper_boundary = 0x9F;
                    }
                    d.bytes_needed = 2;
                    d.code_point = (byte & 0xF) as u32;
                    (HandlerResult::Continue, false)
                    },
                    0xF0..=0xF4 => {
                    if byte == 0xF0 {
                        d.lower_boundary = 0x90;
                    }
                    if byte == 0xF4 {
                        d.upper_boundary = 0x8F;
                    }
                    d.bytes_needed = 3;
                    d.code_point = (byte & 0x7) as u32;
                    (HandlerResult::Continue, false)
                    },
                    _ => (HandlerResult::Error, false),
                }
            } else if !(d.lower_boundary..=d.upper_boundary).contains(&byte) {
                *d = Decoder::new();
                (HandlerResult::Error, true)
            } else {
                d.lower_boundary = 0x80;
                d.upper_boundary = 0xBF;
                d.code_point = (d.code_point << 6u32) | ((byte & 0x3F) as u32);
                // Never saturates: bytes seen < bytes needed <= 3 (`reachable`).
                d.bytes_seen = d.bytes_seen.saturating_add(1);
                if d.bytes_seen != d.bytes_needed {
                    (HandlerResult::Continue, false)
                } else {
                    let code_point = d.code_point;
                    *d = Decoder::new();
                    (HandlerResult::CodePoint(code_point), false)
                }
            }
        },
    }
}

/// `prefix` followed by a successful output; failure stays failure.
spec fn prepend(prefix: Seq<u32>, rest: Option<Seq<u32>>) -> Option<Seq<u32>> {
    match rest {
        Some(out) => Some(prefix + out),
        None => None,
    }
}

proof fn lemma_prepend_cons(prefix: Seq<u32>, c: u32, rest: Option<Seq<u32>>)
    ensures
        prepend(prefix, cons(c, rest)) == prepend(prefix.push(c), rest),
{
    if let Some(out) = rest {
        assert(prefix + (seq![c] + out) =~= prefix.push(c) + out);
    }
}

/// One step of `process_queue`, stated as an equation.
proof fn lemma_unfold(mode: ErrorMode, d: Utf8Decoder, input: Seq<u8>, i: nat)
    requires
        i <= input.len(),
    ensures
        ({
            let s = handler(d, item_at(input, i));
            let j = next_position(input, i, s);
            process_queue(mode, d, input, i) == match s.result {
                HandlerResult::Finished => Some(seq![]),
                HandlerResult::CodePoint(c) => cons(c, process_queue(mode, s.decoder, input, j)),
                HandlerResult::Error => match mode {
                    ErrorMode::Replacement => cons(0xFFFD, process_queue(mode, s.decoder, input, j)),
                    ErrorMode::Fatal => None,
                },
                HandlerResult::Continue => process_queue(mode, s.decoder, input, j),
            }
        }),
{
}

/// The error mode as a flag, so it can be read on every iteration.
spec fn mode_of(fatal: bool) -> ErrorMode {
    if fatal {
        ErrorMode::Fatal
    } else {
        ErrorMode::Replacement
    }
}

/// "Process a queue" with a fresh UTF-8 decoder over all of `input`.
fn process_queue_exec(fatal: bool, input: &[u8]) -> (r: Option<Vec<u32>>)
    ensures
        match (r, process_queue(mode_of(fatal), initial_decoder(), input@, 0)) {
            (Some(out), Some(expected)) => out@ == expected,
            (None, None) => true,
            _ => false,
        },
{
    let ghost mode = mode_of(fatal);
    let ghost expected = process_queue(mode, initial_decoder(), input@, 0);
    let mut d = Decoder::new();
    let mut out: Vec<u32> = Vec::new();
    let mut i: usize = 0;
    proof {
        assert(Seq::<u32>::empty() + expected->0 =~= expected->0);
    }
    loop
        invariant
            mode == mode_of(fatal),
            expected == process_queue(mode, initial_decoder(), input@, 0),
            i <= input.len(),
            super::lemmas::reachable(d@) || (i == input.len() && d@.bytes_needed == 0),
            expected == prepend(out@, process_queue(mode, d@, input@, i as nat)),
        decreases input.len() - i, if d@.bytes_needed == 0 { 0int } else { 1int },
    {
        let ghost d0 = d@;
        let ghost i0 = i as nat;
        let item = match input.get(i) {
            Some(byte) => Item::Byte(*byte),
            None => Item::EndOfQueue,
        };
        assert(item == item_at(input@, i0));
        proof {
            if i < input.len() {
                super::lemmas::lemma_handler_byte(d0, input@[i as int]);
            } else {
                super::lemmas::lemma_handler_end(d0);
            }
        }
        let (result, restored) = run_handler(&mut d, item);
        if i < input.len() && !restored {
            // Never saturates: i < input.len().
            i = i.saturating_add(1);
        }
        assert(i as nat == next_position(input@, i0, handler(d0, item)));
        proof {
            lemma_unfold(mode, d0, input@, i0);
        }
        match result {
            HandlerResult::Finished => {
                proof {
                    assert(out@ + seq![] =~= out@);
                }
                return Some(out);
            },
            HandlerResult::CodePoint(c) => {
                proof {
                    lemma_prepend_cons(out@, c, process_queue(mode, d@, input@, i as nat));
                }
                out.push(c);
            },
            HandlerResult::Error => {
                if fatal {
                    return None;
                }
                proof {
                    lemma_prepend_cons(out@, 0xFFFD, process_queue(mode, d@, input@, i as nat));
                }
                out.push(0xFFFD);
            },
            HandlerResult::Continue => {},
        }
    }
}

/// "UTF-8 decode without BOM" (Encoding §6): errors become U+FFFD.
pub fn decode_without_bom(input: &[u8]) -> (output: Vec<u32>)
    ensures
        super::contract::decode_without_bom_ensures(input@, output@),
{
    proof {
        super::lemmas::lemma_replacement_never_fails(input@);
    }
    process_queue_exec(false, input).unwrap_or_default()
}

/// "UTF-8 decode" (Encoding §6): strips a leading BOM, errors become U+FFFD.
pub fn decode(input: &[u8]) -> (output: Vec<u32>)
    ensures
        super::contract::decode_ensures(input@, output@),
{
    // 1. peek three bytes; 2. if they are the BOM, read (skip) them.
    let has_bom = input.starts_with(&[0xEF, 0xBB, 0xBF]);
    match input.split_at_checked(3) {
        Some((_, rest)) if has_bom => {
            assert(rest@ =~= input@.subrange(3, input@.len() as int));
            decode_without_bom(rest)
        },
        _ => decode_without_bom(input),
    }
}

/// "UTF-8 decode without BOM or fail" (Encoding §6): `None` is failure.
pub fn decode_without_bom_or_fail(input: &[u8]) -> (output: Option<Vec<u32>>)
    ensures
        super::contract::decode_without_bom_or_fail_ensures(
            input@,
            match output {
                Some(v) => Some(v@),
                None => None,
            },
        ),
{
    process_queue_exec(true, input)
}

} // verus!

#[cfg(test)]
mod tests {
    use super::{decode, decode_without_bom, decode_without_bom_or_fail};

    fn code_points(s: &str) -> Vec<u32> {
        s.chars().map(u32::from).collect()
    }

    /// Rust's lossy decoder also substitutes maximal subparts (Encoding
    /// §8.1.1 and Unicode §3.9 agree), so the outputs must match exactly.
    fn check(bytes: &[u8]) {
        let lossy = code_points(&String::from_utf8_lossy(bytes));
        assert_eq!(decode_without_bom(bytes), lossy, "{bytes:02X?}");
        let strict = std::str::from_utf8(bytes).ok().map(code_points);
        assert_eq!(decode_without_bom_or_fail(bytes), strict, "{bytes:02X?}");
    }

    #[test]
    fn all_one_and_two_byte_inputs() {
        // Miri is slow; a stride still covers every lead-byte class.
        let step = if cfg!(miri) { 37 } else { 1 };
        for a in (0..=255u8).step_by(step) {
            check(&[a]);
            for b in (0..=255u8).step_by(step) {
                check(&[a, b]);
            }
        }
    }

    #[test]
    fn boundaries_and_truncation() {
        for bytes in [
            &[0xE0, 0x9F, 0x80][..], // overlong
            &[0xE0, 0xA0, 0x80],
            &[0xED, 0x9F, 0xBF],
            &[0xED, 0xA0, 0x80],       // surrogate
            &[0xF0, 0x8F, 0xBF, 0xBF], // overlong
            &[0xF0, 0x90, 0x80, 0x80],
            &[0xF4, 0x8F, 0xBF, 0xBF],
            &[0xF4, 0x90, 0x80, 0x80], // above U+10FFFF
            &[0xF0, 0x90, 0x80, 0x41], // truncated, restore the A
            &[0xE2, 0x82],             // truncated at end-of-queue
            &[0xF5, 0x80, 0xC0, 0xC1, 0xFF],
        ] {
            check(bytes);
        }
    }

    #[test]
    fn bom() {
        assert_eq!(decode(&[0xEF, 0xBB, 0xBF, 0x41]), vec![0x41]);
        assert_eq!(decode(&[0xEF, 0xBB, 0xBF]), Vec::<u32>::new());
        assert_eq!(decode(&[0xEF, 0xBB]), vec![0xFFFD]);
        assert_eq!(decode_without_bom(&[0xEF, 0xBB, 0xBF]), vec![0xFEFF]);
    }
}
