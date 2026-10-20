//! The executable percent-encoders and set membership, proven to meet
//! [`super::contract`].
//!
//! [`utf8_percent_encode`] runs `clazel-encoding`'s proven UTF-8 encoder,
//! then one loop over its bytes that mirrors
//! [`super::spec::encode_output_bytes`]. The step comments live in
//! [`super::spec`].

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The ASCII upper hex digit for `n` < 16.
fn upper_hex_digit(n: u8) -> (d: u32)
    requires
        n < 16,
    ensures
        d == ascii_upper_hex_digit(n),
{
    // Never saturates: n < 16.
    if n < 10 {
        (n as u32).saturating_add(0x30)
    } else {
        (n as u32).saturating_add(0x37)
    }
}

/// Appends "percent-encode `byte`" to `out`.
fn push_percent_encoded(byte: u8, out: &mut Vec<u32>)
    ensures
        final(out)@ == old(out)@ + super::spec::percent_encode(byte),
{
    let ghost start = out@;
    let high = byte >> 4u8;
    let low = byte & 0x0Fu8;
    assert(high == byte / 16 && low == byte % 16) by (bit_vector)
        requires
            high == byte >> 4u8,
            low == byte & 0x0Fu8,
    ;
    out.push(0x25);
    out.push(upper_hex_digit(high));
    out.push(upper_hex_digit(low));
    assert(out@ =~= start + super::spec::percent_encode(byte));
}

/// "Percent-encode" a byte (URL §1.3).
pub fn percent_encode(byte: u8) -> (output: Vec<u32>)
    ensures
        super::contract::percent_encode_ensures(byte, output@),
{
    let mut out: Vec<u32> = Vec::new();
    push_percent_encoded(byte, &mut out);
    assert(out@ =~= super::spec::percent_encode(byte));
    out
}

fn in_c0_control_set(c: u32) -> (r: bool)
    ensures
        r == in_c0_control_percent_encode_set(c),
{
    c <= 0x1F || (0x7F..=0x10FFFF).contains(&c)
}

fn in_query_set(c: u32) -> (r: bool)
    ensures
        r == in_query_percent_encode_set(c),
{
    in_c0_control_set(c) || c == 0x20 || c == 0x22 || c == 0x23 || c == 0x3C || c == 0x3E
}

fn in_path_set(c: u32) -> (r: bool)
    ensures
        r == in_path_percent_encode_set(c),
{
    in_query_set(c) || c == 0x3F || c == 0x5E || c == 0x60 || c == 0x7B || c == 0x7D
}

fn in_userinfo_set(c: u32) -> (r: bool)
    ensures
        r == in_userinfo_percent_encode_set(c),
{
    in_path_set(c) || c == 0x2F || c == 0x3A || c == 0x3B || c == 0x3D || c == 0x40
        || (0x5B..=0x5D).contains(&c) || c == 0x7C
}

fn in_component_set(c: u32) -> (r: bool)
    ensures
        r == in_component_percent_encode_set(c),
{
    in_userinfo_set(c) || (0x24..=0x26).contains(&c) || c == 0x2B || c == 0x2C
}

impl PercentEncodeSet {
    /// Whether the set includes the code point `c` (URL §1.3).
    pub fn contains(self, c: u32) -> (r: bool)
        ensures
            super::contract::contains_ensures(self, c, r),
    {
        match self {
            PercentEncodeSet::C0Control => in_c0_control_set(c),
            PercentEncodeSet::Fragment => in_c0_control_set(c) || c == 0x20 || c == 0x22
                || c == 0x3C || c == 0x3E || c == 0x60,
            PercentEncodeSet::Query => in_query_set(c),
            PercentEncodeSet::SpecialQuery => in_query_set(c) || c == 0x27,
            PercentEncodeSet::Path => in_path_set(c),
            PercentEncodeSet::Userinfo => in_userinfo_set(c),
            PercentEncodeSet::Component => in_component_set(c),
            PercentEncodeSet::ApplicationXWwwFormUrlencoded => in_component_set(c) || c == 0x21
                || (0x27..=0x29).contains(&c) || c == 0x7E,
        }
    }

    /// Whether this is the application/x-www-form-urlencoded set
    /// (percent-encode after encoding, step 2's spaceAsPlus).
    fn is_application_x_www_form_urlencoded(self) -> (r: bool)
        ensures
            r == (self == PercentEncodeSet::ApplicationXWwwFormUrlencoded),
    {
        matches!(self, PercentEncodeSet::ApplicationXWwwFormUrlencoded)
    }
}

/// Percent-encode after encoding, step 7.3's body for one byte: appends
/// what it outputs to `out`.
fn push_output_byte(set: PercentEncodeSet, space_as_plus: bool, byte: u8, out: &mut Vec<u32>)
    ensures
        final(out)@ == old(out)@ + encode_output_byte(set, space_as_plus, byte),
{
    let ghost start = out@;
    if space_as_plus && byte == 0x20 {
        out.push(0x2B);
        assert(out@ =~= start + seq![0x2Bu32]);
    } else if !set.contains(byte as u32) {
        out.push(byte as u32);
        assert(out@ =~= start + seq![byte as u32]);
    } else {
        push_percent_encoded(byte, out);
    }
}

/// "Percent-encode after encoding" with UTF-8: the body of both
/// "UTF-8 percent-encode" algorithms.
fn percent_encode_after_encoding_utf8_exec(input: &[u32], set: PercentEncodeSet) -> (output: Vec<u32>)
    requires
        clazel_encoding::utf8::spec::all_scalar_values(input@),
    ensures
        output@ == percent_encode_after_encoding_utf8(input@, set),
{
    let space_as_plus = set.is_application_x_www_form_urlencoded();
    let bytes = clazel_encoding::utf8::encode::encode(input);
    let ghost expected = percent_encode_after_encoding_utf8(input@, set);
    let mut out: Vec<u32> = Vec::new();
    let mut i: usize = 0;
    assert(out@ + expected =~= expected);
    loop
        invariant
            i <= bytes.len(),
            expected == percent_encode_after_encoding_utf8(input@, set),
            expected == out@ + encode_output_bytes(set, space_as_plus, bytes@, i as nat),
        decreases bytes.len() - i,
    {
        match bytes.get(i) {
            None => {
                assert(out@ + seq![] =~= out@);
                return out;
            },
            Some(byte) => {
                let ghost before = out@;
                push_output_byte(set, space_as_plus, *byte, &mut out);
                // Never saturates: i < bytes.len().
                i = i.saturating_add(1);
                assert(before + (encode_output_byte(set, space_as_plus, bytes@[i - 1])
                    + encode_output_bytes(set, space_as_plus, bytes@, i as nat))
                    =~= out@ + encode_output_bytes(set, space_as_plus, bytes@, i as nat));
            },
        }
    }
}

/// "UTF-8 percent-encode" a scalar value (URL §1.3).
pub fn utf8_percent_encode_code_point(scalar_value: u32, set: PercentEncodeSet) -> (output: Vec<u32>)
    requires
        super::contract::utf8_percent_encode_code_point_requires(scalar_value),
    ensures
        super::contract::utf8_percent_encode_code_point_ensures(scalar_value, set, output@),
{
    let input = [scalar_value];
    assert(input@ =~= seq![scalar_value]);
    percent_encode_after_encoding_utf8_exec(&input, set)
}

/// "UTF-8 percent-encode" a scalar value string (URL §1.3).
pub fn utf8_percent_encode(input: &[u32], set: PercentEncodeSet) -> (output: Vec<u32>)
    requires
        super::contract::utf8_percent_encode_requires(input@),
    ensures
        super::contract::utf8_percent_encode_ensures(input@, set, output@),
{
    percent_encode_after_encoding_utf8_exec(input, set)
}

} // verus!

#[cfg(test)]
mod tests {
    use super::{
        PercentEncodeSet, percent_encode, utf8_percent_encode, utf8_percent_encode_code_point,
    };

    fn scalars(s: &str) -> Vec<u32> {
        s.chars().map(u32::from).collect()
    }

    fn string(v: &[u32]) -> String {
        v.iter().filter_map(|&c| char::from_u32(c)).collect()
    }

    #[test]
    fn standard_examples() {
        // URL §1.3, example table (the UTF-8 rows).
        assert_eq!(string(&percent_encode(0x23)), "%23");
        assert_eq!(string(&percent_encode(0x7F)), "%7F");
        let u = PercentEncodeSet::Userinfo;
        assert_eq!(
            string(&utf8_percent_encode_code_point(0x2261, u)),
            "%E2%89%A1"
        );
        assert_eq!(
            string(&utf8_percent_encode_code_point(0x203D, u)),
            "%E2%80%BD"
        );
        assert_eq!(
            string(&utf8_percent_encode(&scalars("Say what\u{203D}"), u)),
            "Say%20what%E2%80%BD"
        );
    }

    #[test]
    fn space_as_plus() {
        let form = PercentEncodeSet::ApplicationXWwwFormUrlencoded;
        assert_eq!(
            string(&utf8_percent_encode(&scalars("1+1 2%20"), form)),
            "1%2B1+2%2520"
        );
        let c = PercentEncodeSet::Component;
        assert_eq!(
            string(&utf8_percent_encode(&scalars("1+1 2%20"), c)),
            "1%2B1%202%2520"
        );
    }

    #[test]
    fn every_byte() {
        for b in 0..=255u8 {
            assert_eq!(string(&percent_encode(b)), format!("%{b:02X}"));
        }
    }
}
