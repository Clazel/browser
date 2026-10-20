//! The round trip: decoding what the encoder produced gives back its
//! input ([`lemma_decode_encode`]). RFC 3492 §6.2 states the converse
//! uniqueness property in words ("there is only one encoded string that
//! can represent a given sequence of integers"); the round trip is what
//! makes the two procedures inverses.
//!
//! It holds whenever the decoder's intermediate values fit in `maxint`.
//! The encoder only checks `delta`, but the decoder also checks `i`, which
//! is `delta` plus an insertion position, and `w`, which can reach 35
//! times the integer being decoded. [`round_trip_bounded`] states a
//! sufficient condition: `35 * (c + 1) * (length + 1) <= maxint` for every
//! code point `c`. Every string of scalar values (at most U+10FFFF) up to
//! 100 code points long meets it ([`lemma_scalar_values_bounded`]), which
//! covers every DNS label (63 octets at most).
//!
//! The proof follows the encoder. At each point of its loops, the decoder,
//! having read the encoder's output so far, holds exactly the code points
//! of the input that the encoder has already passed over (all those below
//! `n`, and those equal to `n` before the current index), and its state
//! number `n * (length + 1) + i` plus the encoder's `delta` is the
//! encoder's state number (§3.2, "insertion unsort coding").

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The bound under which the round trip holds (see the module docs).
pub open spec fn round_trip_bounded(s: Seq<u32>) -> bool {
    forall|x: int| 0 <= x < s.len() ==> 35 * ((#[trigger] s[x]) as nat + 1) * (s.len() + 1) <= maxint()
}

/// Strings of at most 100 scalar values meet [`round_trip_bounded`].
pub proof fn lemma_scalar_values_bounded(s: Seq<u32>)
    requires
        s.len() <= 100,
        forall|x: int| 0 <= x < s.len() ==> #[trigger] s[x] <= 0x10FFFF,
    ensures
        round_trip_bounded(s),
{
    assert forall|x: int| 0 <= x < s.len() implies 35 * ((#[trigger] s[x]) as nat + 1) * (s.len() + 1)
        <= maxint() by {
        let c = s[x] as nat + 1;
        let l = s.len() + 1;
        assert(35 * c * l <= maxint()) by (nonlinear_arith)
            requires c <= 0x110000, l <= 101;
    }
}

/// The code points of `s` less than `bound`, in order.
pub open spec fn keep_below(s: Seq<u32>, bound: nat) -> Seq<u32>
    decreases s.len()
{
    if s.len() == 0 {
        seq![]
    } else if (s.last() as nat) < bound {
        keep_below(s.drop_last(), bound).push(s.last())
    } else {
        keep_below(s.drop_last(), bound)
    }
}

/// `c` is one of the 36 digit code points.
pub open spec fn is_digit(c: u32) -> bool {
    digit_value(c) is Some
}

/// `longer` is `shorter` followed by digit code points only.
pub open spec fn extends(shorter: Seq<u32>, longer: Seq<u32>) -> bool {
    &&& longer.len() >= shorter.len()
    &&& longer.subrange(0, shorter.len() as int) == shorter
    &&& forall|k: int| shorter.len() <= k < longer.len() ==> is_digit(#[trigger] longer[k])
}

proof fn lemma_extends_transitive(a: Seq<u32>, b: Seq<u32>, c: Seq<u32>)
    requires
        extends(a, b),
        extends(b, c),
    ensures
        extends(a, c),
{
    assert(c.subrange(0, a.len() as int) =~= c.subrange(0, b.len() as int).subrange(0, a.len() as int));
    assert forall|k: int| a.len() <= k < c.len() implies is_digit(#[trigger] c[k]) by {
        if k < b.len() {
            assert(c[k] == c.subrange(0, b.len() as int)[k]);
        }
    }
}

/// Every digit maps to a digit code point, and back.
pub proof fn lemma_digit_code_point(d: nat)
    requires
        d < 36,
    ensures
        digit_value(digit_code_point(d)) == Some(d),
        digit_code_point(d) != delimiter(),
{
}

/// A generalized variable-length integer is made of digit code points.
proof fn lemma_encode_vli_digits(q: nat, k: nat, bias: nat)
    ensures
        encode_vli(q, k, bias).len() >= 1,
        forall|x: int| 0 <= x < encode_vli(q, k, bias).len() ==> is_digit(#[trigger] encode_vli(q, k, bias)[x]),
    decreases q
{
    let t = threshold(k, bias);
    if q < t {
        lemma_digit_code_point(q);
    } else {
        let d = (base() - t) as nat;
        let r = (q - t) as nat;
        vstd::arithmetic::div_mod::lemma_mod_bound(r as int, d as int);
        lemma_digit_code_point(t + r % d);
        super::termination::lemma_encode_vli_shrinks(q, k, bias);
        lemma_encode_vli_digits(r / d, k + base(), bias);
        let head = seq![digit_code_point(t + r % d)];
        let tail = encode_vli(r / d, k + base(), bias);
        assert forall|x: int| 0 <= x < encode_vli(q, k, bias).len() implies is_digit(
            #[trigger] encode_vli(q, k, bias)[x],
        ) by {
            if x > 0 {
                assert(encode_vli(q, k, bias)[x] == tail[x - 1]);
            }
        }
    }
}

proof fn lemma_extends_by_vli(output: Seq<u32>, q: nat, k: nat, bias: nat)
    ensures
        extends(output, output + encode_vli(q, k, bias)),
{
    lemma_encode_vli_digits(q, k, bias);
    let v = encode_vli(q, k, bias);
    assert((output + v).subrange(0, output.len() as int) =~= output);
    assert forall|x: int| output.len() <= x < (output + v).len() implies is_digit(#[trigger] (output + v)[x]) by {
        assert((output + v)[x] == v[x - output.len()]);
    }
}

/// The encoder's loop over the input only appends digit code points.
proof fn lemma_encode_inner_extends(s: Seq<u32>, j: nat, n: nat, b: nat, state: EncodeState)
    ensures
        encode_inner(s, j, n, b, state) matches Some(after) ==> extends(state.output, after.output),
    decreases s.len() - j
{
    assert(state.output.subrange(0, state.output.len() as int) =~= state.output);
    if j < s.len() {
        let c = s[j as int];
        if !(c < n && state.delta + 1 > maxint()) {
            let delta = if c < n {
                state.delta + 1
            } else {
                state.delta
            };
            let next = if c == n {
                EncodeState {
                    delta: 0,
                    bias: adapt(delta, state.h + 1, state.h == b),
                    h: state.h + 1,
                    output: state.output + encode_vli(delta, base(), state.bias),
                }
            } else {
                EncodeState { delta, bias: state.bias, h: state.h, output: state.output }
            };
            lemma_encode_inner_extends(s, j + 1, n, b, next);
            if c == n {
                lemma_extends_by_vli(state.output, delta, base(), state.bias);
            }
            if let Some(after) = encode_inner(s, j + 1, n, b, next) {
                lemma_extends_transitive(state.output, next.output, after.output);
            }
        }
    }
}

/// The encoder's outer loop only appends digit code points.
proof fn lemma_encode_outer_extends(s: Seq<u32>, n: nat, b: nat, state: EncodeState)
    ensures
        encode_outer(s, n, b, state) matches Some(e) ==> extends(state.output, e),
    decreases 0x1_0000_0001 - n
{
    assert(state.output.subrange(0, state.output.len() as int) =~= state.output);
    if state.h < s.len() {
        super::termination::lemma_min_at_least(s, n);
        if let Some(m) = min_at_least(s, n) {
            let delta = state.delta + (m - n) as nat * (state.h + 1);
            if delta <= maxint() {
                let start = EncodeState { delta, bias: state.bias, h: state.h, output: state.output };
                lemma_encode_inner_extends(s, 0, m as nat, b, start);
                if let Some(after) = encode_inner(s, 0, m as nat, b, start) {
                    let next = EncodeState { delta: after.delta + 1, bias: after.bias, h: after.h, output: after.output };
                    lemma_encode_outer_extends(s, m as nat + 1, b, next);
                    if let Some(e) = encode_outer(s, m as nat + 1, b, next) {
                        lemma_extends_transitive(state.output, after.output, e);
                    }
                }
            }
        }
    }
}

// ---------------------------------------------------------------------------
// keep_below
// ---------------------------------------------------------------------------

proof fn lemma_keep_below_len(s: Seq<u32>, bound: nat)
    ensures
        keep_below(s, bound).len() == super::lemmas::count_less(s, bound),
    decreases s.len()
{
    if s.len() > 0 {
        lemma_keep_below_len(s.drop_last(), bound);
    }
}

proof fn lemma_keep_below_add(a: Seq<u32>, b: Seq<u32>, bound: nat)
    ensures
        keep_below(a + b, bound) == keep_below(a, bound) + keep_below(b, bound),
    decreases b.len()
{
    if b.len() == 0 {
        assert(a + b =~= a);
        assert(keep_below(a, bound) + keep_below(b, bound) =~= keep_below(a, bound));
    } else {
        assert((a + b).drop_last() =~= a + b.drop_last());
        assert((a + b).last() == b.last());
        lemma_keep_below_add(a, b.drop_last(), bound);
        if (b.last() as nat) < bound {
            assert(keep_below(a, bound) + keep_below(b.drop_last(), bound).push(b.last()) =~= (keep_below(a, bound)
                + keep_below(b.drop_last(), bound)).push(b.last()));
        }
    }
}

proof fn lemma_keep_below_all(s: Seq<u32>, bound: nat)
    requires
        super::lemmas::count_less(s, bound) == s.len(),
    ensures
        keep_below(s, bound) == s,
    decreases s.len()
{
    if s.len() > 0 {
        super::lemmas::lemma_count_step(s.drop_last(), bound);
        lemma_keep_below_all(s.drop_last(), bound);
        assert(s.drop_last().push(s.last()) =~= s);
    }
}

proof fn lemma_keep_below_basic(s: Seq<u32>)
    ensures
        keep_below(s, initial_n()) == basic_code_points(s),
    decreases s.len()
{
    if s.len() > 0 {
        lemma_keep_below_basic(s.drop_last());
    }
}

/// Nothing lies between `n` and the minimum code point `>= n`.
proof fn lemma_keep_below_gap(s: Seq<u32>, n: nat, m: nat)
    requires
        n <= m,
        min_at_least(s, n) matches Some(r) ==> r >= m,
    ensures
        keep_below(s, m) == keep_below(s, n),
    decreases s.len()
{
    if s.len() > 0 {
        let rest = min_at_least(s.drop_last(), n);
        if let Some(r) = rest {
            if (s.last() as nat) >= n {
                assert(r >= m);
            }
        }
        lemma_keep_below_gap(s.drop_last(), n, m);
    }
}

proof fn lemma_keep_below_min(s: Seq<u32>, n: nat)
    ensures
        min_at_least(s, n) matches Some(m) ==> keep_below(s, m as nat) == keep_below(s, n),
    decreases s.len()
{
    if s.len() > 0 {
        lemma_keep_below_min(s.drop_last(), n);
        super::termination::lemma_min_at_least(s.drop_last(), n);
        if let Some(m) = min_at_least(s, n) {
            if let Some(r) = min_at_least(s.drop_last(), n) {
                if (s.last() as nat) >= n && r >= s.last() {
                    lemma_keep_below_gap(s.drop_last(), n, s.last() as nat);
                }
            } else {
                lemma_keep_below_gap(s.drop_last(), n, m as nat);
            }
        }
    }
}

// ---------------------------------------------------------------------------
// The generalized variable-length integers (§3.3).
// ---------------------------------------------------------------------------

/// Decoding the digits the encoder output for `q`, starting with `i0` and
/// weight `w`, adds `q * w` to `i0` and consumes exactly those digits.
proof fn lemma_vli_round_trip(e: Seq<u32>, position: nat, i0: nat, w: nat, k: nat, bias: nat, q: nat)
    requires
        w >= 1,
        35 * (i0 + q * w) <= maxint(),
        position + encode_vli(q, k, bias).len() <= e.len(),
        e.subrange(position as int, (position + encode_vli(q, k, bias).len()) as int) == encode_vli(q, k, bias),
    ensures
        decode_vli(e, position, i0, w, k, bias) == Some((i0 + q * w, position + encode_vli(q, k, bias).len())),
    decreases q
{
    let v = encode_vli(q, k, bias);
    let t = threshold(k, bias);
    lemma_encode_vli_digits(q, k, bias);
    assert(e[position as int] == v[0]);
    if q < t {
        lemma_digit_code_point(q);
    } else {
        let d = (base() - t) as nat;
        let r = (q - t) as nat;
        let digit = t + r % d;
        let next_q = r / d;
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(r as int, d as int);
        vstd::arithmetic::div_mod::lemma_mod_bound(r as int, d as int);
        lemma_digit_code_point(digit);
        super::termination::lemma_encode_vli_shrinks(q, k, bias);
        let tail = encode_vli(next_q, k + base(), bias);
        assert(v =~= seq![digit_code_point(digit)] + tail);
        // digit <= q, so i0 + digit * w <= i0 + q * w.
        assert(digit * w <= q * w) by (nonlinear_arith)
            requires digit <= q;
        // The next weight is at most 35 * w <= 35 * (i0 + q * w).
        assert(w * d <= 35 * (i0 + q * w)) by (nonlinear_arith)
            requires d <= 35, q >= 1, w >= 1;
        // The total is unchanged: digit * w + next_q * (w * d) == q * w.
        let rm = r % d;
        assert(digit * w + next_q * (w * d) == q * w) by (nonlinear_arith)
            requires digit == t + rm, r == d * next_q + rm, q == t + r;
        assert(e.subrange((position + 1) as int, (position + 1 + tail.len()) as int) =~= e.subrange(
            position as int,
            (position + v.len()) as int,
        ).subrange(1, v.len() as int));
        assert(v.subrange(1, v.len() as int) =~= tail);
        assert(w * d >= 1) by (nonlinear_arith)
            requires w >= 1, d >= 1;
        lemma_vli_round_trip(e, position + 1, i0 + digit * w, w * d, k + base(), bias, next_q);
    }
}

// ---------------------------------------------------------------------------
// Insertion unsort coding (§3.2): the decoder tracks the encoder.
// ---------------------------------------------------------------------------

proof fn lemma_keep_below_len_le(s: Seq<u32>, bound: nat)
    ensures
        keep_below(s, bound).len() <= s.len(),
{
    lemma_keep_below_len(s, bound);
    super::lemmas::lemma_count_step(s, bound);
}

/// Splitting at `j` and at `j + 1`.
proof fn lemma_split(s: Seq<u32>, j: int)
    requires
        0 <= j < s.len(),
    ensures
        s.subrange(0, j + 1) == s.subrange(0, j).push(s[j]),
        s.subrange(j, s.len() as int) == seq![s[j]] + s.subrange(j + 1, s.len() as int),
{
    assert(s.subrange(0, j + 1) =~= s.subrange(0, j).push(s[j]));
    assert(s.subrange(j, s.len() as int) =~= seq![s[j]] + s.subrange(j + 1, s.len() as int));
}

/// How the kept code points change when the encoder passes index `j`.
proof fn lemma_keep_step(s: Seq<u32>, j: int, m: nat)
    requires
        0 <= j < s.len(),
    ensures
        keep_below(s.subrange(0, j + 1), m + 1) == if (s[j] as nat) < m + 1 {
            keep_below(s.subrange(0, j), m + 1).push(s[j])
        } else {
            keep_below(s.subrange(0, j), m + 1)
        },
        keep_below(s.subrange(j, s.len() as int), m) == if (s[j] as nat) < m {
            seq![s[j]] + keep_below(s.subrange(j + 1, s.len() as int), m)
        } else {
            keep_below(s.subrange(j + 1, s.len() as int), m)
        },
{
    let c = s[j];
    lemma_split(s, j);
    let prefix = s.subrange(0, j);
    let suffix1 = s.subrange(j + 1, s.len() as int);
    lemma_keep_below_add(seq![c], suffix1, m);
    assert(seq![c].drop_last() =~= Seq::<u32>::empty());
    reveal_with_fuel(keep_below, 2);
    assert(prefix.push(c).drop_last() =~= prefix);
    if (c as nat) < m {
        assert(keep_below(seq![c], m) =~= seq![c]);
    } else {
        assert(keep_below(seq![c], m) =~= Seq::<u32>::empty());
        assert(keep_below(suffix1, m) =~= Seq::<u32>::empty() + keep_below(suffix1, m));
    }
}

/// The decoder's state while the encoder is at index `j` of its pass for
/// `m` (the preconditions of [`lemma_inner`] without the encoder's result).
pub open spec fn tracks(
    s: Seq<u32>,
    j: nat,
    m: nat,
    b: nat,
    state: EncodeState,
    n_d: nat,
    i_d: nat,
    out_d: Seq<u32>,
) -> bool {
    &&& round_trip_bounded(s)
    &&& j <= s.len()
    &&& m <= 0xFFFF_FFFF
    &&& state.h >= b
    &&& state.h == out_d.len()
    &&& out_d == keep_below(s.subrange(0, j as int), m + 1) + keep_below(s.subrange(j as int, s.len() as int), m)
    &&& n_d * (state.h + 1) + i_d + state.delta == m * (state.h + 1) + keep_below(s.subrange(0, j as int), m + 1).len()
    &&& (i_d == 0) == (state.h == b)
}

/// The encoder outputs `delta` at index `j` (where the code point is `m`);
/// the decoder reads it and inserts `m` where the encoder's state says.
proof fn lemma_emit(
    s: Seq<u32>,
    e: Seq<u32>,
    j: nat,
    m: nat,
    b: nat,
    state: EncodeState,
    n_d: nat,
    i_d: nat,
    out_d: Seq<u32>,
)
    requires
        tracks(s, j, m, b, state, n_d, i_d, out_d),
        j < s.len(),
        s[j as int] as nat == m,
        extends(state.output + encode_vli(state.delta, base(), state.bias), e),
    ensures
        ({
            let q = state.delta;
            let next = EncodeState {
                delta: 0,
                bias: adapt(q, state.h + 1, state.h == b),
                h: state.h + 1,
                output: state.output + encode_vli(q, base(), state.bias),
            };
            let position = keep_below(s.subrange(0, j as int), m + 1).len();
            let out_next = out_d.insert(position as int, m as u32);
            &&& tracks(s, j + 1, m, b, next, m, position + 1, out_next)
            &&& decode_loop(e, state.output.len(), n_d, i_d, state.bias, out_d) == decode_loop(
                e,
                next.output.len(),
                m,
                position + 1,
                next.bias,
                out_next,
            )
        }),
{
    let len = s.len();
    let h = state.h;
    let q = state.delta;
    let c = s[j as int];
    let v = encode_vli(q, base(), state.bias);
    let new_bias = adapt(q, h + 1, h == b);
    let next = EncodeState { delta: 0, bias: new_bias, h: h + 1, output: state.output + v };
    let p = state.output.len();
    let prefix = s.subrange(0, j as int);
    let suffix1 = s.subrange(j as int + 1, len as int);
    lemma_keep_step(s, j as int, m);
    lemma_split(s, j as int);
    // The digits for q sit at p in e.
    assert(e.subrange(p as int, (p + v.len()) as int) =~= e.subrange(0, (p + v.len()) as int).subrange(
        p as int,
        (p + v.len()) as int,
    ));
    assert(next.output.subrange(p as int, (p + v.len()) as int) =~= v);
    // Where the decoder inserts: after the kept code points before j.
    let kept = keep_below(prefix, m + 1);
    let rest = keep_below(suffix1, m);
    assert(out_d =~= kept + rest);
    let position = kept.len();
    lemma_keep_below_len_le(prefix, m + 1);
    lemma_keep_below_len_le(suffix1, m);
    assert(h + 1 <= len);
    // The decoder's i after reading q.
    let big_i = i_d + q;
    assert(big_i == (m - n_d) * (h + 1) + position) by (nonlinear_arith)
        requires
            big_i == i_d + q,
            n_d * (h + 1) + i_d + q == m * (h + 1) + position;
    assert(n_d <= m) by (nonlinear_arith)
        requires
            n_d * (h + 1) + i_d + q == m * (h + 1) + position,
            position <= h;
    let gap = (m - n_d) as nat;
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(
        big_i as int,
        (h + 1) as int,
        gap as int,
        position as int,
    );
    // The decoder's bounds: 35 * i <= maxint.
    assert(35 * ((s[j as int]) as nat + 1) * (s.len() + 1) <= maxint());
    assert(35 * big_i <= maxint()) by (nonlinear_arith)
        requires
            big_i == gap * (h + 1) + position,
            gap <= m,
            position <= h,
            h + 1 <= len,
            35 * (m + 1) * (len + 1) <= maxint();
    lemma_encode_vli_digits(q, base(), state.bias);
    lemma_vli_round_trip(e, p, i_d, 1, base(), state.bias, q);
    // One step of the decoder's loop.
    let out_next = out_d.insert(position as int, m as u32);
    assert(out_next =~= keep_below(s.subrange(0, j + 1 as int), m + 1) + keep_below(suffix1, m));
}

/// Inside the encoder's pass for `m`, at index `j`: the decoder holds the
/// code points at most `m` before `j` and those below `m` from `j` on.
proof fn lemma_inner(
    s: Seq<u32>,
    e: Seq<u32>,
    j: nat,
    m: nat,
    b: nat,
    state: EncodeState,
    n_d: nat,
    i_d: nat,
    out_d: Seq<u32>,
)
    requires
        tracks(s, j, m, b, state, n_d, i_d, out_d),
        encode_inner(s, j, m, b, state) matches Some(after) && encode_outer(
            s,
            m + 1,
            b,
            EncodeState { delta: after.delta + 1, bias: after.bias, h: after.h, output: after.output },
        ) == Some(e),
    ensures
        decode_loop(e, state.output.len(), n_d, i_d, state.bias, out_d) == Some(s),
    decreases 0x1_0000_0001 - m, s.len() - j
{
    let len = s.len();
    let h = state.h;
    if j >= len {
        assert(s.subrange(0, j as int) =~= s);
        assert(s.subrange(j as int, len as int) =~= Seq::<u32>::empty());
        assert(out_d =~= keep_below(s, m + 1));
        let next = EncodeState { delta: state.delta + 1, bias: state.bias, h: state.h, output: state.output };
        assert((m + 1) * (h + 1) == m * (h + 1) + h + 1) by (nonlinear_arith);
        lemma_outer(s, e, m + 1, b, next, n_d, i_d, out_d);
        return;
    }
    let c = s[j as int];
    lemma_keep_step(s, j as int, m);
    if c as nat != m {
        let delta = if (c as nat) < m {
            state.delta + 1
        } else {
            state.delta
        };
        let next = EncodeState { delta, bias: state.bias, h: state.h, output: state.output };
        assert(out_d =~= keep_below(s.subrange(0, j + 1 as int), m + 1) + keep_below(
            s.subrange(j + 1 as int, len as int),
            m,
        ));
        lemma_inner(s, e, j + 1, m, b, next, n_d, i_d, out_d);
    } else {
        let q = state.delta;
        let v = encode_vli(q, base(), state.bias);
        let next = EncodeState { delta: 0, bias: adapt(q, h + 1, h == b), h: h + 1, output: state.output + v };
        let after = encode_inner(s, j + 1, m, b, next).unwrap();
        let last = EncodeState { delta: after.delta + 1, bias: after.bias, h: after.h, output: after.output };
        lemma_encode_inner_extends(s, j + 1, m, b, next);
        lemma_encode_outer_extends(s, m + 1, b, last);
        lemma_extends_transitive(next.output, after.output, e);
        let position = keep_below(s.subrange(0, j as int), m + 1).len();
        lemma_emit(s, e, j, m, b, state, n_d, i_d, out_d);
        lemma_inner(s, e, j + 1, m, b, next, m, position + 1, out_d.insert(position as int, m as u32));
    }
}

/// At the top of the encoder's outer loop with `n`: the decoder holds the
/// code points below `n`.
proof fn lemma_outer(s: Seq<u32>, e: Seq<u32>, n: nat, b: nat, state: EncodeState, n_d: nat, i_d: nat, out_d: Seq<u32>)
    requires
        round_trip_bounded(s),
        n <= 0x1_0000_0000,
        state.h >= b,
        state.h == out_d.len(),
        out_d == keep_below(s, n),
        n_d * (state.h + 1) + i_d + state.delta == n * (state.h + 1),
        (i_d == 0) == (state.h == b),
        encode_outer(s, n, b, state) == Some(e),
    ensures
        decode_loop(e, state.output.len(), n_d, i_d, state.bias, out_d) == Some(s),
    decreases 0x1_0000_0001 - n, s.len() + 1
{
    let h = state.h;
    lemma_keep_below_len(s, n);
    super::lemmas::lemma_count_step(s, n);
    if h >= s.len() {
        lemma_keep_below_all(s, n);
    } else {
        super::termination::lemma_min_at_least(s, n);
        lemma_keep_below_min(s, n);
        let m = min_at_least(s, n).unwrap();
        let delta = state.delta + (m - n) as nat * (h + 1);
        let start = EncodeState { delta, bias: state.bias, h, output: state.output };
        assert(s.subrange(0, 0) =~= Seq::<u32>::empty());
        assert(s.subrange(0, s.len() as int) =~= s);
        assert(out_d =~= keep_below(s.subrange(0, 0), (m + 1) as nat) + keep_below(s.subrange(0, s.len() as int), m as nat));
        let gap = (m - n) as nat;
        assert(n_d * (h + 1) + i_d + delta == m * (h + 1)) by (nonlinear_arith)
            requires
                n_d * (h + 1) + i_d + state.delta == n * (h + 1),
                delta == state.delta + gap * (h + 1),
                m == n + gap;
        lemma_inner(s, e, 0, m as nat, b, start, n_d, i_d, out_d);
    }
}

proof fn lemma_basic_code_points_basic(s: Seq<u32>)
    ensures
        !contains_non_basic(basic_code_points(s)),
    decreases s.len()
{
    if s.len() > 0 {
        lemma_basic_code_points_basic(s.drop_last());
        let rest = basic_code_points(s.drop_last());
        if is_basic(s.last()) {
            assert(rest.push(s.last()).drop_last() =~= rest);
        }
    }
}

/// `last_delimiter` finds the delimiter at `p` when only digits follow it.
proof fn lemma_last_delimiter_at(e: Seq<u32>, end: nat, p: nat)
    requires
        p < end <= e.len(),
        e[p as int] == delimiter(),
        forall|k: int| p < k < end ==> is_digit(#[trigger] e[k]),
    ensures
        last_delimiter(e, end) == Some(p),
    decreases end
{
    if end - 1 > p {
        assert(is_digit(e[end - 1]));
        lemma_last_delimiter_at(e, (end - 1) as nat, p);
    }
}

/// `last_delimiter` finds nothing among digits.
proof fn lemma_last_delimiter_none(e: Seq<u32>, end: nat)
    requires
        end <= e.len(),
        forall|k: int| 0 <= k < end ==> is_digit(#[trigger] e[k]),
    ensures
        last_delimiter(e, end) is None,
    decreases end
{
    if end > 0 {
        assert(is_digit(e[end - 1]));
        lemma_last_delimiter_none(e, (end - 1) as nat);
    }
}

/// The round trip: under [`round_trip_bounded`], decoding the encoder's
/// output gives back its input.
pub proof fn lemma_decode_encode(s: Seq<u32>)
    requires
        round_trip_bounded(s),
    ensures
        punycode_encode(s) matches Some(e) ==> punycode_decode(e) == Some(s),
{
    let basic = basic_code_points(s);
    let b = basic.len();
    let out0 = if b > 0 {
        basic.push(delimiter())
    } else {
        basic
    };
    let state = EncodeState { delta: 0, bias: initial_bias(), h: b, output: out0 };
    if let Some(e) = punycode_encode(s) {
        lemma_encode_outer_extends(s, initial_n(), b, state);
        lemma_basic_code_points_basic(s);
        lemma_keep_below_basic(s);
        super::lemmas::lemma_count_basic(s);
        lemma_keep_below_len(s, initial_n());
        if b > 0 {
            assert(e[b as int] == e.subrange(0, out0.len() as int)[b as int]);
            lemma_last_delimiter_at(e, e.len(), b);
            assert(e.subrange(0, b as int) =~= e.subrange(0, out0.len() as int).subrange(0, b as int));
            assert(out0.subrange(0, b as int) =~= basic);
        } else {
            lemma_last_delimiter_none(e, e.len());
        }
        lemma_outer(s, e, initial_n(), b, state, initial_n(), 0, basic);
        assert(decode_loop(e, out0.len(), initial_n(), 0, initial_bias(), basic) == Some(s));
        if b > 0 {
            assert(last_delimiter(e, e.len()) == Some(b));
            assert(e.subrange(0, b as int) == basic);
        } else {
            assert(last_delimiter(e, e.len()) is None);
            assert(basic =~= Seq::<u32>::empty());
        }
    }
}

} // verus!
