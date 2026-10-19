//! The executable UTF-8 encoder, proven to meet [`super::contract`].
//!
//! The code mirrors the spec: [`run_handler`] is UTF-8's encoder's handler
//! (§8.1.2), with its while loop kept as a loop, and [`encode`] is "process
//! a queue" (§4.1). Each is proven equal to its spec function, so the step
//! comments live in [`super::spec`] and are not repeated here.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The bytes UTF-8's encoder's handler returns for `code_point`.
spec fn handler_bytes(code_point: u32) -> Seq<u8> {
    match encoder_handler(ScalarItem::ScalarValue(code_point)) {
        EncoderHandlerResult::Bytes(bytes) => bytes,
        EncoderHandlerResult::Finished => seq![],
    }
}

/// UTF-8's encoder's handler for one scalar value: appends the bytes it
/// returns to `out`.
fn run_handler(code_point: u32, out: &mut Vec<u8>)
    requires
        code_point <= 0x10FFFF,
    ensures
        final(out)@ == old(out)@ + handler_bytes(code_point),
{
    let ghost start = out@;
    if code_point <= 0x7F {
        out.push(code_point as u8);
        assert(out@ =~= start + seq![code_point as u8]);
        return;
    }
    let (count, offset): (u32, u32) = if (0x80..=0x7FF).contains(&code_point) {
        (1, 0xC0)
    } else if (0x800..=0xFFFF).contains(&code_point) {
        (2, 0xE0)
    } else {
        (3, 0xF0)
    };
    let ghost count0 = count as nat;
    // Never saturates: count <= 3.
    let shift = count.saturating_mul(6);
    let lead = code_point >> shift;
    assert(lead <= code_point) by (bit_vector)
        requires
            lead == code_point >> shift,
    ;
    // Never saturates: lead <= 0x10FFFF.
    out.push(lead.saturating_add(offset) as u8);
    let ghost first = seq![((code_point >> ((6 * count0) as u32)) + offset) as u8];
    assert(out@ =~= start + first);
    let ghost target = encoder_while_count(code_point, count0, first);
    let ghost mut bytes = first;
    let mut count = count;
    while count > 0
        invariant
            count <= 3,
            out@ == start + bytes,
            target == encoder_while_count(code_point, count0, first),
            encoder_while_count(code_point, count as nat, bytes) == target,
        decreases count,
    {
        // Never saturates: 0 < count <= 3.
        let temp = code_point >> count.saturating_sub(1).saturating_mul(6);
        let byte = (0x80 | (temp & 0x3F)) as u8;
        out.push(byte);
        proof {
            bytes = bytes.push(byte);
        }
        assert(out@ =~= start + bytes);
        count = count.saturating_sub(1);
    }
}

/// "UTF-8 encode" (Encoding §6): "process a queue" with UTF-8's encoder
/// over `input`.
pub fn encode(input: &[u32]) -> (output: Vec<u8>)
    requires
        super::contract::encode_requires(input@),
    ensures
        super::contract::encode_ensures(input@, output@),
{
    let ghost expected = utf8_encode(input@);
    let mut out: Vec<u8> = Vec::new();
    let mut i: usize = 0;
    assert(out@ + expected =~= expected);
    loop
        invariant
            i <= input.len(),
            all_scalar_values(input@),
            expected == utf8_encode(input@),
            expected == out@ + encoder_process_queue(input@, i as nat),
        decreases input.len() - i,
    {
        match input.get(i) {
            None => {
                assert(out@ + seq![] =~= out@);
                return out;
            },
            Some(code_point) => {
                let ghost before = out@;
                assert(is_scalar_value(input@[i as int]));
                run_handler(*code_point, &mut out);
                // Never saturates: i < input.len().
                i = i.saturating_add(1);
                assert(before + (handler_bytes(*code_point) + encoder_process_queue(input@, i as nat))
                    =~= out@ + encoder_process_queue(input@, i as nat));
            },
        }
    }
}

} // verus!

#[cfg(test)]
mod tests {
    use super::encode;

    fn check(s: &str) {
        let scalars: Vec<u32> = s.chars().map(u32::from).collect();
        assert_eq!(encode(&scalars), s.as_bytes(), "{s:?}");
    }

    #[test]
    fn every_scalar_value_alone() {
        // Miri is slow; a stride still covers every length class and boundary.
        let step = if cfg!(miri) { 4099 } else { 1 };
        let mut buf = [0u8; 4];
        for c in (0..=0x10FFFFu32).step_by(step).filter_map(char::from_u32) {
            assert_eq!(
                encode(&[u32::from(c)]),
                c.encode_utf8(&mut buf).as_bytes(),
                "{c:?}"
            );
        }
    }

    #[test]
    fn boundaries() {
        for c in [
            0x0, 0x7F, 0x80, 0x7FF, 0x800, 0xD7FF, 0xE000, 0xFFFD, 0xFFFF, 0x10000, 0x10FFFF,
        ] {
            let Some(c) = char::from_u32(c) else { continue };
            check(&String::from(c));
        }
    }

    #[test]
    fn strings() {
        check("");
        check("A");
        check("héllo, wörld");
        check("\u{0}\u{7F}\u{80}\u{7FF}\u{800}\u{FFFF}\u{10000}\u{10FFFF}");
        check("日本語のテキスト 😀🎉");
        check(&String::from('\u{FEFF}'));
    }
}
