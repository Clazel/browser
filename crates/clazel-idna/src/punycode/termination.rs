//! Termination of the recursive loops in [`super::spec`]. Verus needs these
//! facts to accept the spec's `decreases` clauses (each names a `via`
//! function in `spec.rs`, which only calls these); they say nothing else
//! about the spec.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// A generalized variable-length integer consumes at least one code point.
pub proof fn lemma_decode_vli_advances(input: Seq<u32>, position: nat, i: nat, w: nat, k: nat, bias: nat)
    ensures
        decode_vli(input, position, i, w, k, bias) matches Some((_, p)) ==> position < p <= input.len(),
    decreases input.len() - position
{
    if position < input.len() {
        if let Some(digit) = digit_value(input[position as int]) {
            let t = threshold(k, bias);
            lemma_decode_vli_advances(input, position + 1, i + digit * w, w * (base() - t) as nat, k + base(), bias);
        }
    }
}

/// In the bias adaptation loop, `delta div (base - tmin)` is smaller than
/// `delta`.
pub proof fn lemma_adapt_loop_shrinks(delta: nat)
    ensures
        delta > 0 ==> delta / ((base() - tmin()) as nat) < delta,
{
    if delta > 0 {
        vstd::arithmetic::div_mod::lemma_div_decreases(delta as int, 35);
    }
}

/// While `q >= t`, the next `q`, `(q - t) div (base - t)`, is smaller.
pub proof fn lemma_encode_vli_shrinks(q: nat, k: nat, bias: nat)
    ensures
        q >= threshold(k, bias) ==> ((q - threshold(k, bias)) as nat / ((base() - threshold(k, bias)) as nat))
            < q,
{
    let t = threshold(k, bias);
    if q >= t {
        let d = (base() - t) as nat;
        assert(d >= 10);
        vstd::arithmetic::div_mod::lemma_div_nonincreasing((q - t) as int, d as int);
    }
}

/// The minimum code point `>= n` is `>= n`, and a `u32`.
pub proof fn lemma_min_at_least(input: Seq<u32>, n: nat)
    ensures
        min_at_least(input, n) matches Some(m) ==> m >= n,
    decreases input.len()
{
    if input.len() > 0 {
        lemma_min_at_least(input.drop_last(), n);
    }
}

} // verus!
