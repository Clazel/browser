//! Executable pieces the decoder and encoder share: §5's digit-values,
//! the clamped threshold `t`, and §6.1's `adapt`, each proven equal to its
//! [`super::spec`] counterpart. Integers are `u64`, wide enough that none of
//! the RFC's intermediate values wraps before it is checked against
//! `maxint`.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// §6.4 `maxint` (32-bit unsigned).
pub const MAXINT: u64 = 0xFFFF_FFFF;

/// A bound on every `bias` [`adapt`] returns for a `delta <= maxint`.
pub const BIAS_BOUND: u64 = 0x100_0000_0000;

/// §5's digit-value of `c`, or `None`.
pub fn digit_value(c: u32) -> (r: Option<u64>)
    ensures
        match r {
            Some(d) => super::spec::digit_value(c) == Some(d as nat) && d < 36,
            None => super::spec::digit_value(c) is None,
        },
{
    if (0x41..=0x5A).contains(&c) {
        // Never saturates: c >= 0x41.
        Some(c.saturating_sub(0x41) as u64)
    } else if (0x61..=0x7A).contains(&c) {
        // Never saturates: c >= 0x61.
        Some(c.saturating_sub(0x61) as u64)
    } else if (0x30..=0x39).contains(&c) {
        // Never saturates: c >= 0x30.
        Some(c.saturating_sub(0x30).saturating_add(26) as u64)
    } else {
        None
    }
}

/// "the code point for digit d", lowercase.
pub fn digit_code_point(d: u64) -> (c: u32)
    requires
        d < 36,
    ensures
        c == super::spec::digit_code_point(d as nat),
        super::spec::digit_value(c) == Some(d as nat),
{
    if d < 26 {
        // Never saturates: d < 26.
        (d as u32).saturating_add(0x61)
    } else {
        // Never saturates: 26 <= d < 36.
        (d as u32).saturating_sub(26).saturating_add(0x30)
    }
}

/// "let t = tmin if k <= bias, or tmax if k >= bias + tmax, or k - bias
/// otherwise".
pub fn threshold(k: u64, bias: u64) -> (t: u64)
    requires
        bias <= BIAS_BOUND,
    ensures
        t == super::spec::threshold(k as nat, bias as nat),
        1 <= t <= 26,
{
    if k <= bias {
        1
    } else if k >= bias.saturating_add(26) {
        // bias + 26 never saturates: bias <= BIAS_BOUND.
        26
    } else {
        // Never saturates: k > bias.
        k.saturating_sub(bias)
    }
}

/// §6.1 `adapt(delta, numpoints, firsttime)`.
pub fn adapt(delta: u64, numpoints: u64, firsttime: bool) -> (r: u64)
    requires
        delta <= MAXINT,
        numpoints >= 1,
    ensures
        r == super::spec::adapt(delta as nat, numpoints as nat, firsttime),
        r <= BIAS_BOUND,
{
    let delta = if firsttime {
        delta / 700
    } else {
        delta / 2
    };
    let quotient = delta.checked_div(numpoints).unwrap_or(0);
    proof {
        vstd::arithmetic::div_mod::lemma_div_nonincreasing(delta as int, numpoints as int);
    }
    // Never saturates: both are at most maxint.
    let mut delta = delta.saturating_add(quotient);
    let ghost delta0 = delta;
    let mut k: u64 = 0;
    while delta > 455
        invariant
            delta0 <= 2 * MAXINT,
            k + 36 * delta <= 36 * delta0,
            adapt_loop(delta0 as nat, 0) == adapt_loop(delta as nat, k as nat),
        decreases delta
    {
        let next = delta / 35;
        assert(next < delta);
        delta = next;
        // Never saturates: k + 36 * delta <= 36 * delta0.
        k = k.saturating_add(36);
    }
    let scaled = delta.saturating_mul(36);
    let fraction = scaled.checked_div(delta.saturating_add(38)).unwrap_or(0);
    proof {
        vstd::arithmetic::div_mod::lemma_div_nonincreasing(scaled as int, (delta + 38) as int);
    }
    // Never saturates: k <= 36 * delta0 and fraction <= 36 * 455.
    k.saturating_add(fraction)
}

} // verus!
