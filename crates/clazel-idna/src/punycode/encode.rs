//! The executable encoder, proven to meet [`super::contract`].
//!
//! The code follows RFC 3492 §6.3 line by line; the quotes live in
//! [`super::spec`]. Integers are `u64`; `delta` is checked against
//! `maxint` wherever the RFC says "fail on overflow". `h` counts the code
//! points less than `n` (and those equal to `n` already handled), which is
//! what bounds it by the input's length.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

use super::shared::MAXINT;

verus! {

/// "the number of basic code points in the input ... copy them to the
/// output in order".
fn basic_code_points_exec(input: &[u32]) -> (output: Vec<u32>)
    ensures
        output@ == basic_code_points(input@),
        output.len() <= input.len(),
{
    let mut output: Vec<u32> = Vec::new();
    let mut j: usize = 0;
    while j < input.len()
        invariant
            j <= input.len(),
            output@ == basic_code_points(input@.subrange(0, j as int)),
            output.len() <= j,
        decreases input.len() - j
    {
        proof {
            let next = input@.subrange(0, j as int + 1);
            assert(next.drop_last() =~= input@.subrange(0, j as int));
            assert(next.last() == input@[j as int]);
        }
        match input.get(j) {
            Some(&c) if c < 0x80 => output.push(c),
            _ => {},
        }
        // Never saturates: j < input.len().
        j = j.saturating_add(1);
    }
    assert(input@.subrange(0, input.len() as int) =~= input@);
    output
}

/// "let m = the minimum code point >= n in the input".
fn min_at_least_exec(input: &[u32], n: u64) -> (r: Option<u32>)
    ensures
        r == min_at_least(input@, n as nat),
{
    let mut best: Option<u32> = None;
    let mut j: usize = 0;
    while j < input.len()
        invariant
            j <= input.len(),
            best == min_at_least(input@.subrange(0, j as int), n as nat),
        decreases input.len() - j
    {
        proof {
            let next = input@.subrange(0, j as int + 1);
            assert(next.drop_last() =~= input@.subrange(0, j as int));
            assert(next.last() == input@[j as int]);
        }
        match input.get(j) {
            Some(&c) if c as u64 >= n => {
                best = match best {
                    Some(r) if r < c => Some(r),
                    _ => Some(c),
                };
            },
            _ => {},
        }
        // Never saturates: j < input.len().
        j = j.saturating_add(1);
    }
    assert(input@.subrange(0, input.len() as int) =~= input@);
    best
}

/// §6.3's loop over `k` and the final digit, for `q`: appends the code
/// points to `output`.
fn encode_vli_exec(output: &mut Vec<u32>, q: u64, bias: u64)
    requires
        q <= MAXINT,
        bias <= super::shared::BIAS_BOUND,
    ensures
        final(output)@ == old(output)@ + encode_vli(q as nat, base(), bias as nat),
{
    let ghost start = old(output)@;
    let mut q = q;
    let mut k: u64 = 36;
    let ghost q0 = q;
    loop
        invariant
            q <= MAXINT,
            bias <= super::shared::BIAS_BOUND,
            k + 36 * q <= 36 + 36 * q0,
            q0 <= MAXINT,
            output@ + encode_vli(q as nat, k as nat, bias as nat) == start + encode_vli(q0 as nat, base(), bias as nat),
        ensures
            q < threshold(k as nat, bias as nat),
            output@ + encode_vli(q as nat, k as nat, bias as nat) == start + encode_vli(q0 as nat, base(), bias as nat),
        decreases q
    {
        // "let t = ..."
        let t = super::shared::threshold(k, bias);
        // "if q < t then break"
        if q < t {
            break;
        }
        // Never saturate: t <= q and 10 <= base - t <= 35.
        let d = 36u64.saturating_sub(t);
        let rest = q.saturating_sub(t);
        let (digit, next) = match (rest.checked_rem(d), rest.checked_div(d)) {
            (Some(r), Some(x)) => (r, x),
            _ => (0, 0),
        };
        proof {
            vstd::arithmetic::div_mod::lemma_div_nonincreasing(rest as int, d as int);
            super::termination::lemma_encode_vli_shrinks(q as nat, k as nat, bias as nat);
        }
        // "output the code point for digit t + ((q - t) mod (base - t))"
        let ghost before = output@;
        let ghost tail = encode_vli(next as nat, (k + 36) as nat, bias as nat);
        output.push(super::shared::digit_code_point(t.saturating_add(digit)));
        assert(output@ + tail =~= before + encode_vli(q as nat, k as nat, bias as nat));
        // "let q = (q - t) div (base - t)"
        q = next;
        // Never saturates: k + 36 * q <= 36 + 36 * q0, and q fell by at
        // least 1.
        k = k.saturating_add(36);
    }
    // "output the code point for digit q"
    let ghost before = output@;
    output.push(super::shared::digit_code_point(q));
    assert(output@ =~= before + encode_vli(q as nat, k as nat, bias as nat));
}

/// RFC 3492 §6.3 encoding. `None` is failure (overflow).
pub fn encode(input: &[u32]) -> (output: Option<Vec<u32>>)
    ensures
        super::contract::encode_ensures(
            input@,
            match output {
                Some(v) => Some(v@),
                None => None,
            },
        ),
{
    // "let h = b = the number of basic code points in the input"
    // "copy them to the output in order, followed by a delimiter if b > 0"
    let mut output = basic_code_points_exec(input);
    let b = output.len();
    if b > 0 {
        output.push(0x2D);
    }
    let ghost target = punycode_encode(input@);
    let mut n: u64 = 128;
    let mut delta: u64 = 0;
    let mut bias: u64 = 72;
    let mut h: usize = b;
    proof {
        super::lemmas::lemma_count_basic(input@);
    }
    // "while h < length(input) do begin"
    while h < input.len()
        invariant
            target == punycode_encode(input@),
            b == basic_code_points(input@).len(),
            128 <= n <= 0x1_0000_0000,
            delta <= MAXINT + 1,
            bias <= super::shared::BIAS_BOUND,
            h as nat == super::lemmas::count_less(input@, n as nat),
            target == encode_outer(
                input@,
                n as nat,
                b as nat,
                EncodeState { delta: delta as nat, bias: bias as nat, h: h as nat, output: output@ },
            ),
        decreases 0x1_0000_0001 - n
    {
        proof {
            super::lemmas::lemma_count_min(input@, n as nat);
        }
        // "let m = the minimum code point >= n in the input"
        let m = min_at_least_exec(input, n)?;
        // "let delta = delta + (m - n) * (h + 1), fail on overflow".
        // m - n never saturates (m >= n); h + 1 never saturates (h <
        // input.len()). An overflowing product exceeds maxint too.
        let difference = (m as u64).saturating_sub(n);
        let h_plus_one = (h as u64).saturating_add(1);
        delta = match difference.checked_mul(h_plus_one) {
            Some(product) => match delta.checked_add(product) {
                Some(sum) if sum <= MAXINT => sum,
                _ => return None,
            },
            None => {
                proof {
                    assert(difference as nat * h_plus_one as nat <= delta as nat + difference as nat
                        * h_plus_one as nat);
                }
                return None;
            },
        };
        // "let n = m"
        n = m as u64;
        proof {
            super::lemmas::lemma_count_step(input@, n as nat);
            assert(input@.subrange(0, 0) =~= Seq::<u32>::empty());
        }
        let ghost start = EncodeState { delta: delta as nat, bias: bias as nat, h: h as nat, output: output@ };
        let ghost inner = encode_inner(input@, 0, n as nat, b as nat, start);
        // "for each code point c in the input (in order) do begin"
        let mut j: usize = 0;
        while j < input.len()
            invariant
                target == punycode_encode(input@),
                b == basic_code_points(input@).len(),
                128 <= n <= MAXINT,
                delta <= MAXINT,
                bias <= super::shared::BIAS_BOUND,
                j <= input.len(),
                h as nat == super::lemmas::count_less(input@, n as nat) + super::lemmas::count_equal(input@.subrange(0, j as int), n as nat),
                super::lemmas::count_less(input@, n as nat) + super::lemmas::count_equal(input@, n as nat) <= input.len(),
                target == match inner {
                    Some(state) => encode_outer(
                        input@,
                        n as nat + 1,
                        b as nat,
                        EncodeState { delta: state.delta + 1, bias: state.bias, h: state.h, output: state.output },
                    ),
                    None => None,
                },
                inner == encode_inner(
                    input@,
                    j as nat,
                    n as nat,
                    b as nat,
                    EncodeState { delta: delta as nat, bias: bias as nat, h: h as nat, output: output@ },
                ),
            decreases input.len() - j
        {
            let c = match input.get(j) {
                Some(&c) => c,
                None => return None,
            };
            proof {
                super::lemmas::lemma_count_equal_prefix(input@, j as int, n as nat);
                super::lemmas::lemma_count_equal_prefix_le(input@, j as int + 1, n as nat);
            }
            // "if c < n then increment delta, fail on overflow"
            if (c as u64) < n {
                if delta >= MAXINT {
                    return None;
                }
                delta = delta.saturating_add(1);
            }
            // "if c == n then begin"
            if c as u64 == n {
                // "let q = delta", the loop over k, the final digit.
                encode_vli_exec(&mut output, delta, bias);
                // "let bias = adapt(delta, h + 1, test h equals b?)".
                // h + 1 never saturates: h < input.len().
                bias = super::shared::adapt(delta, (h as u64).saturating_add(1), h == b);
                // "let delta = 0", "increment h"
                delta = 0;
                h = h.saturating_add(1);
            }
            // Never saturates: j < input.len().
            j = j.saturating_add(1);
        }
        proof {
            assert(input@.subrange(0, input.len() as int) =~= input@);
            super::lemmas::lemma_count_step(input@, n as nat);
        }
        // "increment delta and n". Neither saturates: delta <= maxint and
        // n <= maxint.
        delta = delta.saturating_add(1);
        n = n.saturating_add(1);
    }
    Some(output)
}

} // verus!

#[cfg(test)]
mod tests {
    use super::encode;

    fn run(s: &str) -> Option<String> {
        let input: Vec<u32> = s.chars().map(u32::from).collect();
        encode(&input).map(|v| v.into_iter().filter_map(char::from_u32).collect())
    }

    #[test]
    fn basics() {
        assert_eq!(run("").as_deref(), Some(""));
        assert_eq!(run("abc").as_deref(), Some("abc-"));
        assert_eq!(run("-").as_deref(), Some("--"));
        assert_eq!(run("b\u{FC}cher").as_deref(), Some("bcher-kva"));
        assert_eq!(run("\u{E9}").as_deref(), Some("9ca"));
        // RFC 3492 §7.1 (S).
        assert_eq!(run("-> $1.00 <-").as_deref(), Some("-> $1.00 <--"));
    }

    #[test]
    fn overflow() {
        // A code point near maxint after many basic code points makes
        // delta = (m - n) * (h + 1) overflow.
        let mut input = vec![0x61u32; 4];
        input.push(0xFFFF_FFFF);
        assert_eq!(encode(&input), None);
        // Alone, it does not.
        assert!(encode(&[0xFFFF_FFFF]).is_some());
    }
}
