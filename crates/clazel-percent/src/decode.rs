//! The executable percent-decoders, proven to meet [`super::contract`].
//!
//! [`percent_decode`] is one loop over the input that mirrors
//! [`super::spec::percent_decode_from`], with the invariant "the output so
//! far, followed by `percent_decode_from` from the current position, is
//! the spec's result". The step comments live in [`super::spec`].

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Percent-decode, step 2.2's ranges, for one byte.
fn in_hex_ranges_exec(b: u8) -> (r: bool)
    ensures
        r == in_hex_ranges(b),
{
    (0x30..=0x39).contains(&b) || (0x41..=0x46).contains(&b) || (0x61..=0x66).contains(&b)
}

/// The hexadecimal value of a byte in the step 2.2 ranges.
fn hex_value_exec(b: u8) -> (v: u8)
    requires
        in_hex_ranges(b),
    ensures
        v == hex_value(b),
        v < 16,
{
    // None of these saturate: each range starts at the value subtracted.
    if (0x30..=0x39).contains(&b) {
        b.saturating_sub(0x30)
    } else if (0x41..=0x46).contains(&b) {
        b.saturating_sub(0x37)
    } else {
        b.saturating_sub(0x57)
    }
}

/// Percent-decode, step 2.3.1's bytePoint when the byte at position `i` is
/// 0x25 (%) and the next two are both in the step 2.2 ranges; otherwise
/// `None` (steps 2.1 and 2.2).
fn byte_point_at(input: &[u8], i: usize) -> (r: Option<u8>)
    requires
        i < input.len(),
    ensures
        r is Some <==> (input@[i as int] == 0x25 && i + 2 < input.len() && in_hex_ranges(input@[i + 1int])
            && in_hex_ranges(input@[i + 2int])),
        r matches Some(v) ==> v == 16 * hex_value(input@[i + 1int]) + hex_value(input@[i + 2int]),
{
    if *input.get(i)? != 0x25 {
        return None;
    }
    // Never saturates: i < input.len() <= usize::MAX.
    let first = *input.get(i.saturating_add(1))?;
    let second = *input.get(i.saturating_add(2))?;
    if !(in_hex_ranges_exec(first) && in_hex_ranges_exec(second)) {
        return None;
    }
    let high = hex_value_exec(first);
    let low = hex_value_exec(second);
    // Never saturates: high, low < 16, so at most 255.
    Some(high.saturating_mul(16).saturating_add(low))
}

/// "Percent-decode" a byte sequence (URL §1.3).
pub fn percent_decode(input: &[u8]) -> (output: Vec<u8>)
    ensures
        super::contract::percent_decode_ensures(input@, output@),
{
    let ghost expected = super::spec::percent_decode(input@);
    let mut out: Vec<u8> = Vec::new();
    let mut i: usize = 0;
    assert(out@ + expected =~= expected);
    loop
        invariant
            i <= input.len(),
            expected == super::spec::percent_decode(input@),
            expected == out@ + percent_decode_from(input@, i as nat),
        decreases input.len() - i,
    {
        let ghost before = out@;
        let byte = match input.get(i) {
            None => {
                assert(out@ + seq![] =~= out@);
                return out;
            },
            Some(byte) => *byte,
        };
        match byte_point_at(input, i) {
            Some(byte_point) => {
                out.push(byte_point);
                // Never saturates: i + 2 < input.len().
                i = i.saturating_add(3);
            },
            None => {
                out.push(byte);
                // Never saturates: i < input.len() <= usize::MAX.
                i = i.saturating_add(1);
            },
        }
        assert(before + (seq![out@.last()] + percent_decode_from(input@, i as nat))
            =~= out@ + percent_decode_from(input@, i as nat));
    }
}

/// "Percent-decode" a scalar value string (URL §1.3).
pub fn percent_decode_string(input: &[u32]) -> (output: Vec<u8>)
    requires
        super::contract::percent_decode_string_requires(input@),
    ensures
        super::contract::percent_decode_string_ensures(input@, output@),
{
    let bytes = clazel_encoding::utf8::encode::encode(input);
    percent_decode(bytes.as_slice())
}

} // verus!

#[cfg(test)]
mod tests {
    use super::{percent_decode, percent_decode_string};

    fn scalars(s: &str) -> Vec<u32> {
        s.chars().map(u32::from).collect()
    }

    #[test]
    fn standard_examples() {
        // URL §1.3, example table.
        assert_eq!(percent_decode(b"%25%s%1G"), b"%%s%1G");
        assert_eq!(
            percent_decode_string(&scalars("\u{203D}%25%2E")),
            [0xE2, 0x80, 0xBD, 0x25, 0x2E]
        );
    }

    #[test]
    fn edges() {
        assert_eq!(percent_decode(b""), b"");
        assert_eq!(percent_decode(b"%"), b"%");
        assert_eq!(percent_decode(b"%4"), b"%4");
        assert_eq!(percent_decode(b"%41"), b"A");
        assert_eq!(
            percent_decode(b"%4a%4A%ff%FF%00"),
            [0x4A, 0x4A, 0xFF, 0xFF, 0x00]
        );
        assert_eq!(percent_decode(b"%%41"), b"%A");
        assert_eq!(percent_decode(b"%4%41"), b"%4A");
        assert_eq!(percent_decode(b"%g1%1g"), b"%g1%1g");
        assert_eq!(percent_decode(&[0x25, 0xFF, 0x80]), [0x25, 0xFF, 0x80]);
    }

    #[test]
    fn every_byte_triplet() {
        for b in 0..=255u8 {
            for s in [format!("%{b:02X}"), format!("%{b:02x}")] {
                assert_eq!(percent_decode(s.as_bytes()), [b], "{s}");
            }
        }
    }
}
