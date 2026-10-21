//! The executable encoder, proven to meet [`super::contract`].
//!
//! The code mirrors [`super::spec::encode_from`]: one 24-bit group per
//! iteration, then the final 8 or 16 bits. The step comments live in the
//! spec and are not repeated here.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// RFC 4648 Table 1: the character for value `value % 64`.
fn encode_6_bit_group(group: u32) -> (c: u32)
    ensures
        c == super::spec::encode_6_bit_group(group as nat),
{
    let value = group % 64;
    if value <= 25 {
        // Never saturates: value <= 25.
        value.saturating_add(0x41)
    } else if value <= 51 {
        // Never saturates: 26 <= value <= 51.
        value.saturating_sub(26).saturating_add(0x61)
    } else if value <= 61 {
        // Never saturates: 52 <= value <= 61.
        value.saturating_sub(52).saturating_add(0x30)
    } else if value == 62 {
        0x2B
    } else {
        0x2F
    }
}

/// One full 24-bit group: appends its four characters to `out`.
fn push_group_24(out: &mut Vec<u32>, a: u8, b: u8, c: u8)
    ensures
        ({
            let group: nat = a as nat * 65536 + b as nat * 256 + c as nat;
            final(out)@ == old(out)@ + seq![
                super::spec::encode_6_bit_group(group / 262144),
                super::spec::encode_6_bit_group(group / 4096),
                super::spec::encode_6_bit_group(group / 64),
                super::spec::encode_6_bit_group(group),
            ]
        }),
{
    let group = (a as u32).saturating_mul(65536)
        .saturating_add((b as u32).saturating_mul(256))
        .saturating_add(c as u32);
    let ghost before = out@;
    out.push(encode_6_bit_group(group / 262144));
    out.push(encode_6_bit_group(group / 4096));
    out.push(encode_6_bit_group(group / 64));
    out.push(encode_6_bit_group(group));
    assert(out@ =~= before + seq![
        super::spec::encode_6_bit_group(group as nat / 262144),
        super::spec::encode_6_bit_group(group as nat / 4096),
        super::spec::encode_6_bit_group(group as nat / 64),
        super::spec::encode_6_bit_group(group as nat),
    ]);
}

/// Case (2), exactly 8 bits left: appends the final two characters and
/// two pads to `out`.
fn push_final_8(out: &mut Vec<u32>, a: u8)
    ensures
        ({
            let group: nat = a as nat * 16;
            final(out)@ == old(out)@ + seq![
                super::spec::encode_6_bit_group(group / 64),
                super::spec::encode_6_bit_group(group),
                pad(),
                pad(),
            ]
        }),
{
    let group = (a as u32).saturating_mul(16);
    let ghost before = out@;
    out.push(encode_6_bit_group(group / 64));
    out.push(encode_6_bit_group(group));
    out.push(0x3D);
    out.push(0x3D);
    assert(out@ =~= before + seq![
        super::spec::encode_6_bit_group(group as nat / 64),
        super::spec::encode_6_bit_group(group as nat),
        pad(),
        pad(),
    ]);
}

/// Case (3), exactly 16 bits left: appends the final three characters and
/// one pad to `out`.
fn push_final_16(out: &mut Vec<u32>, a: u8, b: u8)
    ensures
        ({
            let group: nat = (a as nat * 256 + b as nat) * 4;
            final(out)@ == old(out)@ + seq![
                super::spec::encode_6_bit_group(group / 4096),
                super::spec::encode_6_bit_group(group / 64),
                super::spec::encode_6_bit_group(group),
                pad(),
            ]
        }),
{
    let group = (a as u32).saturating_mul(256).saturating_add(b as u32).saturating_mul(4);
    let ghost before = out@;
    out.push(encode_6_bit_group(group / 4096));
    out.push(encode_6_bit_group(group / 64));
    out.push(encode_6_bit_group(group));
    out.push(0x3D);
    assert(out@ =~= before + seq![
        super::spec::encode_6_bit_group(group as nat / 4096),
        super::spec::encode_6_bit_group(group as nat / 64),
        super::spec::encode_6_bit_group(group as nat),
        pad(),
    ]);
}

/// "forgiving-base64 encode" (Infra §7), which is RFC 4648 §4.
pub fn encode(input: &[u8]) -> (output: Vec<u32>)
    ensures
        super::contract::encode_ensures(input@, output@),
{
    let ghost expected = forgiving_base64_encode(input@);
    let mut out: Vec<u32> = Vec::new();
    let mut i: usize = 0;
    assert(out@ + expected =~= expected);
    // Each branch's arithmetic is proven in its own helper above, so the
    // loop body only joins sequences (it exceeded the default rlimit on
    // Linux x86-64 when the arithmetic was inline).
    loop
        invariant
            i <= input.len(),
            expected == forgiving_base64_encode(input@),
            expected == out@ + encode_from(input@, i as nat),
        decreases input.len() - i
    {
        // Never saturate: i <= input.len() <= usize::MAX, and i + 2 is
        // only used when i + 1 < input.len().
        let i1 = i.saturating_add(1);
        let i2 = i.saturating_add(2);
        match input.get(i) {
            None => {
                assert(out@ + seq![] =~= out@);
                return out;
            },
            Some(&a) => match input.get(i1) {
                None => {
                    let ghost before = out@;
                    push_final_8(&mut out, a);
                    assert(out@ =~= before + encode_from(input@, i as nat));
                    assert(out@ + seq![] =~= out@);
                    return out;
                },
                Some(&b) => match input.get(i2) {
                    None => {
                        let ghost before = out@;
                        push_final_16(&mut out, a, b);
                        assert(out@ =~= before + encode_from(input@, i as nat));
                        assert(out@ + seq![] =~= out@);
                        return out;
                    },
                    Some(&c) => {
                        let ghost before = out@;
                        push_group_24(&mut out, a, b, c);
                        // Never saturates: i + 2 < input.len().
                        i = i.saturating_add(3);
                        assert(before + encode_from(input@, (i - 3) as nat)
                            =~= out@ + encode_from(input@, i as nat));
                    },
                },
            },
        }
    }
}

} // verus!

#[cfg(test)]
mod tests {
    use super::encode;

    fn ascii(s: &[u32]) -> String {
        s.iter().filter_map(|&c| char::from_u32(c)).collect()
    }

    #[test]
    fn rfc_4648_section_10() {
        // RFC 4648 §10 "Test Vectors".
        for (input, expected) in [
            ("", ""),
            ("f", "Zg=="),
            ("fo", "Zm8="),
            ("foo", "Zm9v"),
            ("foob", "Zm9vYg=="),
            ("fooba", "Zm9vYmE="),
            ("foobar", "Zm9vYmFy"),
        ] {
            assert_eq!(ascii(&encode(input.as_bytes())), expected, "{input:?}");
        }
    }

    #[test]
    fn every_byte() {
        for b in 0..=255u8 {
            let out = encode(&[b, b, b]);
            assert_eq!(out.len(), 4);
            assert!(out.iter().all(|&c| c < 0x80));
        }
    }
}
