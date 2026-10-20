//! The executable decoder, proven to meet [`super::contract`].
//!
//! The code follows "forgiving-base64 decode" (Infra §7) step by step; the
//! step comments and their quotes live in [`super::spec`]. The buffer is a
//! `u32` holding at most 24 bits, and its length in bits.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Infra §4.6 ASCII whitespace.
fn is_ascii_whitespace(c: u32) -> (r: bool)
    ensures
        r == super::spec::is_ascii_whitespace(c),
{
    c == 0x09 || c == 0x0A || c == 0x0C || c == 0x0D || c == 0x20
}

/// Step 4's list: U+002B (+), U+002F (/), ASCII alphanumeric.
fn is_step_4_allowed(c: u32) -> (r: bool)
    ensures
        r == super::spec::is_step_4_allowed(c),
{
    c == 0x2B || c == 0x2F || (0x30..=0x39).contains(&c) || (0x41..=0x5A).contains(&c) || (
    0x61..=0x7A).contains(&c)
}

/// Step 8.1: the value of `c` in RFC 4648 Table 1.
fn find_in_table_1(c: u32) -> (n: u32)
    requires
        super::spec::is_step_4_allowed(c),
    ensures
        n as nat == super::spec::find_in_table_1(c, 0),
        n < 64,
{
    proof {
        super::lemmas::lemma_find_allowed(c);
    }
    if (0x41..=0x5A).contains(&c) {
        // Never saturates: c >= 0x41.
        c.saturating_sub(0x41)
    } else if (0x61..=0x7A).contains(&c) {
        // Never saturates: c >= 0x61.
        c.saturating_sub(0x61).saturating_add(26)
    } else if (0x30..=0x39).contains(&c) {
        // Never saturates: c >= 0x30.
        c.saturating_sub(0x30).saturating_add(52)
    } else if c == 0x2B {
        62
    } else {
        63
    }
}

/// Step 1: `input` without its ASCII whitespace.
fn remove_ascii_whitespace(input: &[u32]) -> (data: Vec<u32>)
    ensures
        data@ == super::spec::remove_ascii_whitespace(input@),
{
    let mut data: Vec<u32> = Vec::new();
    let mut i: usize = 0;
    assert(input@.subrange(0, 0) =~= Seq::<u32>::empty());
    while i < input.len()
        invariant
            i <= input.len(),
            data@ == super::spec::remove_ascii_whitespace(input@.subrange(0, i as int)),
        decreases input.len() - i
    {
        let ghost prefix = input@.subrange(0, i as int + 1);
        assert(prefix.drop_last() =~= input@.subrange(0, i as int));
        assert(prefix.last() == input@[i as int]);
        match input.get(i) {
            Some(&c) if !is_ascii_whitespace(c) => data.push(c),
            _ => {},
        }
        // Never saturates: i < input.len().
        i = i.saturating_add(1);
    }
    assert(input@.subrange(0, input.len() as int) =~= input@);
    data
}

/// "forgiving-base64 decode" (Infra §7). `None` is failure.
pub fn decode(input: &[u32]) -> (output: Option<Vec<u8>>)
    ensures
        super::contract::decode_ensures(
            input@,
            match output {
                Some(v) => Some(v@),
                None => None,
            },
        ),
{
    // 1.
    let data = remove_ascii_whitespace(input);
    let ghost d1 = data@;
    // 2. `len` is data's code point length after step 2.
    let mut len = data.len();
    if len.is_multiple_of(4) {
        // Never wrap: each branch checks len first.
        let last_is_pad = len >= 1 && data.get(len.saturating_sub(1)) == Some(&0x3D);
        let second_last_is_pad = len >= 2 && data.get(len.saturating_sub(2)) == Some(&0x3D);
        if last_is_pad && second_last_is_pad {
            len = len.saturating_sub(2);
        } else if last_is_pad {
            len = len.saturating_sub(1);
        }
    }
    let ghost d2 = d1.subrange(0, len as int);
    assert(d2 =~= super::lemmas::after_step_2(input@));
    // 3.
    if len % 4 == 1 {
        return None;
    }
    // 4.
    let mut k: usize = 0;
    while k < len
        invariant
            k <= len <= data.len(),
            d2 == data@.subrange(0, len as int),
            d2 == super::lemmas::after_step_2(input@),
            forall|j: int| 0 <= j < k ==> super::spec::is_step_4_allowed(#[trigger] d2[j]),
        decreases len - k
    {
        match data.get(k) {
            Some(&c) if !is_step_4_allowed(c) => {
                proof {
                    assert(d2[k as int] == c);
                    super::lemmas::lemma_contains_disallowed(d2);
                }
                return None;
            },
            _ => {},
        }
        // Never saturates: k < len.
        k = k.saturating_add(1);
    }
    proof {
        super::lemmas::lemma_contains_disallowed(d2);
    }
    // 5. to 7.
    let mut output: Vec<u8> = Vec::new();
    let mut bits: u32 = 0;
    let mut bit_len: u32 = 0;
    let mut position: usize = 0;
    let ghost target = decode_loop(d2, 0, seq![], empty_buffer());
    // 8.
    while position < len
        invariant
            position <= len <= data.len(),
            d2 == data@.subrange(0, len as int),
            d2 == super::lemmas::after_step_2(input@),
            len % 4 != 1,
            !contains_disallowed(d2),
            target == decode_loop(d2, 0, seq![], empty_buffer()),
            forall|j: int| 0 <= j < len ==> super::spec::is_step_4_allowed(#[trigger] d2[j]),
            target == decode_loop(d2, position as nat, output@, Buffer { bits: bits as nat, len: bit_len as nat }),
            bit_len == 0 || bit_len == 6 || bit_len == 12 || bit_len == 18,
            super::lemmas::buffer_fits(Buffer { bits: bits as nat, len: bit_len as nat }),
        decreases len - position
    {
        if let Some(&c) = data.get(position) {
            assert(d2[position as int] == c);
            // 8.1
            let n = find_in_table_1(c);
            // 8.2. Never saturates: bits < 2^18 and n < 64.
            bits = bits.saturating_mul(64).saturating_add(n);
            bit_len = bit_len.saturating_add(6);
            // 8.3
            if bit_len == 24 {
                let ghost before = output@;
                output.push((bits / 65536) as u8);
                output.push((bits / 256 % 256) as u8);
                output.push((bits % 256) as u8);
                assert(output@ =~= before + seq![
                    (bits as nat / 65536) as u8,
                    (bits as nat / 256 % 256) as u8,
                    (bits as nat % 256) as u8,
                ]);
                bits = 0;
                bit_len = 0;
            }
        }
        // 8.4. Never saturates: position < len.
        position = position.saturating_add(1);
    }
    // 9.
    proof {
        super::lemmas::lemma_decode_loop_buffer(d2, 0, seq![], empty_buffer());
    }
    if bit_len == 12 {
        output.push((bits / 16) as u8);
    } else if bit_len == 18 {
        let remaining = bits / 4;
        output.push((remaining / 256) as u8);
        output.push((remaining % 256) as u8);
    }
    assert(output@ =~= decode_step_9(target.output, target.buffer));
    // 10.
    Some(output)
}

} // verus!

#[cfg(test)]
mod tests {
    use super::decode;

    fn run(s: &str) -> Option<Vec<u8>> {
        let input: Vec<u32> = s.chars().map(u32::from).collect();
        decode(&input)
    }

    #[test]
    fn rfc_4648_section_10() {
        for (expected, input) in [
            ("", ""),
            ("f", "Zg=="),
            ("fo", "Zm8="),
            ("foo", "Zm9v"),
            ("foob", "Zm9vYg=="),
            ("fooba", "Zm9vYmE="),
            ("foobar", "Zm9vYmFy"),
        ] {
            assert_eq!(
                run(input).as_deref(),
                Some(expected.as_bytes()),
                "{input:?}"
            );
        }
    }

    #[test]
    fn forgiving() {
        assert_eq!(run(" Zm 9v\n"), Some(b"foo".to_vec()));
        assert_eq!(run("Zg"), Some(b"f".to_vec()));
        assert_eq!(run("Zm8"), Some(b"fo".to_vec()));
        assert_eq!(run("YQ"), run("YR"));
        assert_eq!(run("Z"), None);
        assert_eq!(run("Zg="), None);
        assert_eq!(run("Zg==="), None);
        assert_eq!(run("Z\u{B}g"), None);
        assert_eq!(run("Zm-v"), None);
    }
}
