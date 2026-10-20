//! The executable decoder, proven to meet [`super::contract`].
//!
//! The code follows RFC 3492 §6.2 line by line; the quotes live in
//! [`super::spec`]. Integers are `u64`; every addition and multiplication
//! of the RFC's variables is checked against `maxint` as the RFC says.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

use super::shared::MAXINT;

verus! {

/// The position of the last delimiter in `input`.
fn find_last_delimiter(input: &[u32]) -> (r: Option<usize>)
    ensures
        match r {
            Some(d) => last_delimiter(input@, input.len() as nat) == Some(d as nat) && d < input.len(),
            None => last_delimiter(input@, input.len() as nat) is None,
        },
{
    let mut end = input.len();
    while end > 0
        invariant
            end <= input.len(),
            last_delimiter(input@, input.len() as nat) == last_delimiter(input@, end as nat),
        decreases end
    {
        // Never saturates: end > 0.
        let j = end.saturating_sub(1);
        if input.get(j) == Some(&0x2D) {
            return Some(j);
        }
        end = j;
    }
    None
}

/// §6.2's inner loop from `position`, with `i` as it is before the loop:
/// the new `i` and position, or `None` for failure.
fn decode_vli_exec(input: &[u32], start: usize, oldi: u64, bias: u64) -> (r: Option<(u64, usize)>)
    requires
        start <= input.len(),
        bias <= super::shared::BIAS_BOUND,
    ensures
        match r {
            Some((i2, p2)) => decode_vli(input@, start as nat, oldi as nat, 1, base(), bias as nat) == Some(
                (i2 as nat, p2 as nat),
            ) && oldi <= i2 <= MAXINT && p2 <= input.len(),
            None => decode_vli(input@, start as nat, oldi as nat, 1, base(), bias as nat) is None,
        },
{
    let ghost target = decode_vli(input@, start as nat, oldi as nat, 1, base(), bias as nat);
    let mut position = start;
    let mut i = oldi;
    let mut w: u64 = 1;
    let mut k: u64 = 36;
    loop
        invariant
            position <= input.len(),
            bias <= super::shared::BIAS_BOUND,
            1 <= w <= MAXINT,
            k <= 36 * w,
            oldi <= i,
            target == decode_vli(input@, start as nat, oldi as nat, 1, base(), bias as nat),
            target == decode_vli(input@, position as nat, i as nat, w as nat, k as nat, bias as nat),
        decreases input.len() - position
    {
        // "consume a code point, or fail if there was none to consume"
        let c = match input.get(position) {
            Some(&c) => c,
            None => return None,
        };
        // "let digit = the code point's digit-value, fail if it has none"
        let digit = super::shared::digit_value(c)?;
        // Never saturates: position < input.len().
        position = position.saturating_add(1);
        // "let i = i + digit * w, fail on overflow". digit * w never
        // saturates: digit < 36 and w <= maxint.
        assert(digit * w <= 35 * MAXINT) by (nonlinear_arith)
            requires digit < 36, w <= MAXINT;
        let product = digit.saturating_mul(w);
        i = match i.checked_add(product) {
            Some(sum) if sum <= MAXINT => sum,
            _ => return None,
        };
        // "let t = ..."
        let t = super::shared::threshold(k, bias);
        // "if digit < t then break"
        if digit < t {
            return Some((i, position));
        }
        // "let w = w * (base - t), fail on overflow". Never saturates:
        // w <= maxint and base - t <= 35.
        let ghost old_w = w;
        w = w.saturating_mul(36u64.saturating_sub(t));
        proof {
            let f = 36 - t;
            assert(old_w * f <= MAXINT * 35) by (nonlinear_arith)
                requires old_w <= MAXINT, f <= 35;
            assert(old_w * f >= 10 * old_w) by (nonlinear_arith)
                requires f >= 10;
        }
        if w > MAXINT {
            return None;
        }
        // Never saturates: k <= 36 * w (old) and the new w is at least 10
        // times the old one.
        k = k.saturating_add(36);
    }
}

/// RFC 3492 §6.2 decoding. `None` is failure.
pub fn decode(input: &[u32]) -> (output: Option<Vec<u32>>)
    ensures
        super::contract::decode_ensures(
            input@,
            match output {
                Some(v) => Some(v@),
                None => None,
            },
        ),
{
    // "consume all code points before the last delimiter (if there is one)
    //  and copy them to output, fail on any non-basic code point"
    let mut output: Vec<u32> = Vec::new();
    let mut position: usize = 0;
    if let Some(d) = find_last_delimiter(input) {
        let mut j: usize = 0;
        while j < d
            invariant
                j <= d < input.len(),
                last_delimiter(input@, input.len() as nat) == Some(d as nat),
                output@ == input@.subrange(0, j as int),
                !contains_non_basic(input@.subrange(0, j as int)),
            decreases d - j
        {
            let c = match input.get(j) {
                Some(&c) => c,
                None => return None,
            };
            proof {
                let next = input@.subrange(0, j as int + 1);
                assert(next.drop_last() =~= input@.subrange(0, j as int));
                assert(next.last() == c);
            }
            if c >= 0x80 {
                proof {
                    super::lemmas::lemma_contains_non_basic(input@.subrange(0, d as int));
                    assert(input@.subrange(0, d as int)[j as int] == c);
                    assert(contains_non_basic(input@.subrange(0, d as int)));
                    assert(punycode_decode(input@) is None);
                }
                return None;
            }
            output.push(c);
            // Never saturates: j < d.
            j = j.saturating_add(1);
        }
        // "if more than zero code points were consumed then consume one more"
        if d > 0 {
            // Never saturates: d < input.len().
            position = d.saturating_add(1);
        }
    }
    let mut n: u64 = 128;
    let mut i: u64 = 0;
    let mut bias: u64 = 72;
    let ghost target = punycode_decode(input@);
    // "while the input is not exhausted do begin"
    while position < input.len()
        invariant
            position <= input.len(),
            output.len() <= position,
            n <= MAXINT,
            bias <= super::shared::BIAS_BOUND,
            i <= output.len(),
            target == punycode_decode(input@),
            target == decode_loop(input@, position as nat, n as nat, i as nat, bias as nat, output@),
        decreases input.len() - position
    {
        // "let oldi = i", "let w = 1", the inner loop.
        let oldi = i;
        proof {
            super::termination::lemma_decode_vli_advances(input@, position as nat, i as nat, 1, base(), bias as nat);
        }
        let (new_i, new_position) = match decode_vli_exec(input, position, i, bias) {
            Some(r) => r,
            None => {
                assert(decode_loop(input@, position as nat, n as nat, i as nat, bias as nat, output@) is None);
                return None;
            },
        };
        i = new_i;
        position = new_position;
        // Never wraps: output.len() < input.len().
        let length_plus_one = (output.len() as u64).saturating_add(1);
        // "let bias = adapt(i - oldi, length(output) + 1, test oldi is 0?)"
        // Never saturates: oldi <= i.
        bias = super::shared::adapt(i.saturating_sub(oldi), length_plus_one, oldi == 0);
        // "let n = n + i div (length(output) + 1), fail on overflow"
        let quotient = i.checked_div(length_plus_one)?;
        proof {
            vstd::arithmetic::div_mod::lemma_div_nonincreasing(i as int, length_plus_one as int);
        }
        // Never saturates: both are at most maxint.
        n = n.saturating_add(quotient);
        if n > MAXINT {
            assert(target is None);
            return None;
        }
        // "let i = i mod (length(output) + 1)"
        let remainder = i.checked_rem(length_plus_one)?;
        // "insert n into output at position i"
        output.insert(remainder as usize, n as u32);
        // "increment i". Never saturates: remainder <= output.len().
        i = remainder.saturating_add(1);
    }
    Some(output)
}

} // verus!

#[cfg(test)]
mod tests {
    use super::decode;

    fn run(s: &str) -> Option<Vec<u32>> {
        let input: Vec<u32> = s.chars().map(u32::from).collect();
        decode(&input)
    }

    #[test]
    fn basics() {
        assert_eq!(run(""), Some(vec![]));
        assert_eq!(run("abc-"), Some(vec![0x61, 0x62, 0x63]));
        assert_eq!(run("--"), Some(vec![0x2D]));
        // A leading delimiter with nothing before it is a digit, and "-"
        // has no digit-value.
        assert_eq!(run("-a"), None);
        // Non-basic before the delimiter.
        assert_eq!(run("\u{E9}-a"), None);
        // Unexpected end of input inside an integer.
        assert_eq!(run("z"), None);
        // "egbpdaj6bu4bxfgehfvwxn" is RFC 3492 §7.1 (A).
        assert_eq!(run("egbpdaj6bu4bxfgehfvwxn").map(|v| v.len()), Some(17));
        // Overflow of i.
        assert_eq!(run("99999999999999999999"), None);
    }
}
