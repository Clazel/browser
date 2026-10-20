//! A second transcription of Punycode, from RFC 3492 Appendix C, "Punycode
//! sample implementation" (the C code `punycode.c`, by Adam M. Costello),
//! written from the C source without reference to [`super::spec`], and
//! lemmas proving the two equal on every input.
//!
//! The sample code is a different text from §6's pseudocode: it scans for
//! the last delimiter forwards, finds `m` with a sentinel of `maxint`,
//! tests overflow by division (§6.4's "B > (maxint - A) div C" technique)
//! instead of computing the sum, and detects the wrap of `++delta`. A
//! misreading of §6 that the C code does not share fails the equivalence.
//!
//! Modelling choices:
//! - `punycode_uint` values are `int`. Every operation the C code performs
//!   on them either is preceded by an overflow test that makes it exact,
//!   or (the final `++delta, ++n`) cannot wrap on the sample's domain, so
//!   unbounded arithmetic gives the same values there. The one wrap the
//!   code relies on, `if (++delta == 0)`, is transcribed as its meaning:
//!   `delta` was `maxint`. Unsigned comparisons such as `cp - 48 < 10`
//!   are evaluated modulo 2^32, as C does.
//! - Lengths and indices (`input_length`, `out`, `j`, `in`, `h`, `b`) are
//!   `nat`.
//! - The output buffer has no size limit, so `punycode_big_output` cannot
//!   occur; `case_flags` is null (no mixed-case annotation), so
//!   `encode_digit(d, 0)` gives lowercase and `flagged` is never consulted.
//! - Strings are `Seq<u32>`; the C decoder takes `char`s, which as
//!   `punycode_uint`s are values like any other.
//! - Loops are recursive functions over the C variables they change. The
//!   encoder's main loop fails if `n` passes `maxint`, which C cannot
//!   represent. `n` passes `maxint` only after `m = maxint` is handled,
//!   when every code point has been, so the loop has already ended; the
//!   equivalence proof covers the branch anyway.
//! - Failure (`punycode_bad_input`, `punycode_overflow`) is `None`.

#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// /*** Bootstring parameters for Punycode ***/
// enum { base = 36, tmin = 1, tmax = 26, skew = 38, damp = 700,
//        initial_bias = 72, initial_n = 0x80, delimiter = 0x2D };

/// `static const punycode_uint maxint = -1;` with a 32-bit `punycode_uint`.
pub open spec fn c_maxint() -> int {
    0xFFFF_FFFF
}

/// `x - y` in `punycode_uint` arithmetic.
pub open spec fn c_sub(x: int, y: int) -> int {
    (x - y) % 0x1_0000_0000
}

/// `#define basic(cp) ((punycode_uint)(cp) < 0x80)`
pub open spec fn c_basic(cp: u32) -> bool {
    cp < 0x80
}

/// `#define delim(cp) ((cp) == delimiter)`
pub open spec fn c_delim(cp: u32) -> bool {
    cp == 0x2D
}

/// `decode_digit(cp)`: `cp - 48 < 10 ? cp - 22 : cp - 65 < 26 ? cp - 65 :
/// cp - 97 < 26 ? cp - 97 : base`.
pub open spec fn c_decode_digit(cp: u32) -> int {
    if c_sub(cp as int, 48) < 10 {
        cp - 22
    } else if c_sub(cp as int, 65) < 26 {
        cp - 65
    } else if c_sub(cp as int, 97) < 26 {
        cp - 97
    } else {
        36
    }
}

/// `encode_digit(d, 0)`: `d + 22 + 75 * (d < 26) - ((flag != 0) << 5)`.
pub open spec fn c_encode_digit(d: int) -> u32 {
    (d + 22 + 75 * (if d < 26 {
        1int
    } else {
        0int
    })) as u32
}

/// `t = k <= bias ? tmin : k >= bias + tmax ? tmax : k - bias;`
pub open spec fn c_t(k: int, bias: int) -> int {
    if k <= bias {
        1
    } else if k >= bias + 26 {
        26
    } else {
        k - bias
    }
}

// /*** Bias adaptation function ***/

/// `for (k = 0; delta > ((base - tmin) * tmax) / 2; k += base) delta /= base
/// - tmin; return k + (base - tmin + 1) * delta / (delta + skew);`
pub open spec fn c_adapt_for(delta: int, k: int) -> int
    decreases delta
{
    if delta > 35 * 26 / 2 {
        c_adapt_for(delta / 35, k + 36)
    } else {
        k + 36 * delta / (delta + 38)
    }
}

/// `adapt(delta, numpoints, firsttime)`.
pub open spec fn c_adapt(delta: int, numpoints: int, firsttime: bool) -> int {
    // delta = firsttime ? delta / damp : delta >> 1;
    let delta = if firsttime {
        delta / 700
    } else {
        delta / 2
    };
    // delta += delta / numpoints;
    let delta = delta + delta / numpoints;
    c_adapt_for(delta, 0)
}

// /*** Main decode function ***/

/// `for (b = j = 0; j < input_length; ++j) if (delim(input[j])) b = j;`
pub open spec fn c_find_b(input: Seq<u32>, j: nat, b: nat) -> nat
    decreases input.len() - j
{
    if j >= input.len() {
        b
    } else {
        c_find_b(input, j + 1, if c_delim(input[j as int]) { j } else { b })
    }
}

/// `for (j = 0; j < b; ++j) { if (!basic(input[j])) return
/// punycode_bad_input; output[out++] = input[j]; }`
pub open spec fn c_copy_basic(input: Seq<u32>, j: nat, b: nat, output: Seq<u32>) -> Option<Seq<u32>>
    decreases b - j
{
    if j >= b || j >= input.len() {
        Some(output)
    } else if !c_basic(input[j as int]) {
        None
    } else {
        c_copy_basic(input, j + 1, b, output.push(input[j as int]))
    }
}

/// The decoder's `for (oldi = i, w = 1, k = base; ; k += base)` loop,
/// with `in`, `i`, `w` and `k` at the top of an iteration. Returns `in`
/// and `i` after the `break`.
pub open spec fn c_decode_for(input: Seq<u32>, in_: nat, i: int, w: int, k: int, bias: int) -> Option<(nat, int)>
    decreases input.len() - in_
{
    // if (in >= input_length) return punycode_bad_input;
    if in_ >= input.len() {
        None
    } else {
        // digit = decode_digit(input[in++]);
        let digit = c_decode_digit(input[in_ as int]);
        let in_ = in_ + 1;
        // if (digit >= base) return punycode_bad_input;
        if digit >= 36 {
            None
        } else if digit > (c_maxint() - i) / w {
            // if (digit > (maxint - i) / w) return punycode_overflow;
            None
        } else {
            // i += digit * w;
            let i = i + digit * w;
            // t = ...;
            let t = c_t(k, bias);
            // if (digit < t) break;
            if digit < t {
                Some((in_, i))
            } else if w > c_maxint() / (36 - t) {
                // if (w > maxint / (base - t)) return punycode_overflow;
                None
            } else {
                // w *= (base - t);
                c_decode_for(input, in_, i, w * (36 - t), k + 36, bias)
            }
        }
    }
}

/// The decoder's main loop, `for (in = b > 0 ? b + 1 : 0; in <
/// input_length; ++out)`, with `in`, `n`, `i`, `bias` and the output at
/// the top of an iteration (`out` is the output's length).
pub open spec fn c_decode_main(input: Seq<u32>, in_: nat, n: int, i: int, bias: int, output: Seq<u32>) -> Option<
    Seq<u32>,
>
    decreases input.len() - in_ via c_decode_main_decreases
{
    if in_ >= input.len() {
        Some(output)
    } else {
        let out = output.len() as int;
        let oldi = i;
        match c_decode_for(input, in_, i, 1, 36, bias) {
            None => None,
            Some((in_, i)) => {
                // bias = adapt(i - oldi, out + 1, oldi == 0);
                let bias = c_adapt(i - oldi, out + 1, oldi == 0);
                // if (i / (out + 1) > maxint - n) return punycode_overflow;
                if i / (out + 1) > c_maxint() - n {
                    None
                } else {
                    // n += i / (out + 1);
                    let n = n + i / (out + 1);
                    // i %= (out + 1);
                    let i = i % (out + 1);
                    // memmove(...); output[i++] = n;
                    let output = output.insert(i, n as u32);
                    c_decode_main(input, in_, n, i + 1, bias, output)
                }
            }
        }
    }
}

/// Termination of [`c_decode_main`]: each integer consumes a code point.
#[via_fn]
proof fn c_decode_main_decreases(input: Seq<u32>, in_: nat, n: int, i: int, bias: int, output: Seq<u32>) {
    lemma_c_decode_for_advances(input, in_, i, 1, 36, bias);
}

proof fn lemma_c_decode_for_advances(input: Seq<u32>, in_: nat, i: int, w: int, k: int, bias: int)
    ensures
        c_decode_for(input, in_, i, w, k, bias) matches Some((p, _)) ==> in_ < p <= input.len(),
    decreases input.len() - in_
{
    if in_ < input.len() {
        let digit = c_decode_digit(input[in_ as int]);
        let t = c_t(k, bias);
        lemma_c_decode_for_advances(input, in_ + 1, i + digit * w, w * (36 - t), k + 36, bias);
    }
}

/// `punycode_decode` (RFC 3492 Appendix C). `None` is failure.
pub open spec fn c_punycode_decode(input: Seq<u32>) -> Option<Seq<u32>> {
    // n = initial_n; out = i = 0; bias = initial_bias;
    let b = c_find_b(input, 0, 0);
    match c_copy_basic(input, 0, b, seq![]) {
        None => None,
        Some(output) => c_decode_main(input, if b > 0 { b + 1 } else { 0 }, 0x80, 0, 72, output),
    }
}

// /*** Main encode function ***/

/// `for (j = 0; j < input_length; ++j) if (basic(input[j])) output[out++] =
/// input[j];`
pub open spec fn c_copy_basics(input: Seq<u32>, j: nat, output: Seq<u32>) -> Seq<u32>
    decreases input.len() - j
{
    if j >= input.len() {
        output
    } else {
        c_copy_basics(input, j + 1, if c_basic(input[j as int]) { output.push(input[j as int]) } else { output })
    }
}

/// `for (m = maxint, j = 0; j < input_length; ++j) if (input[j] >= n &&
/// input[j] < m) m = input[j];`, from `j` with `m` so far.
pub open spec fn c_find_m(input: Seq<u32>, j: nat, n: int, m: int) -> int
    decreases input.len() - j
{
    if j >= input.len() {
        m
    } else {
        let c = input[j as int] as int;
        c_find_m(input, j + 1, n, if c >= n && c < m { c } else { m })
    }
}

/// `for (q = delta, k = base; ; k += base) { t = ...; if (q < t) break;
/// output[out++] = encode_digit(t + (q - t) % (base - t), 0); q = (q - t) /
/// (base - t); } output[out++] = encode_digit(q, 0);`
pub open spec fn c_encode_for(q: int, k: int, bias: int) -> Seq<u32>
    decreases q via c_encode_for_decreases
{
    let t = c_t(k, bias);
    if q < t {
        seq![c_encode_digit(q)]
    } else {
        seq![c_encode_digit(t + (q - t) % (36 - t))].add(c_encode_for((q - t) / (36 - t), k + 36, bias))
    }
}

#[via_fn]
proof fn c_encode_for_decreases(q: int, k: int, bias: int) {
    let t = c_t(k, bias);
    if q >= t {
        vstd::arithmetic::div_mod::lemma_div_nonincreasing(q - t, 36 - t);
    }
}

/// The encoder's variables that its inner loop changes.
pub struct CEncode {
    /// `delta`
    pub delta: int,
    /// `bias`
    pub bias: int,
    /// `h`
    pub h: nat,
    /// `output[0 .. out]`
    pub output: Seq<u32>,
}

/// `for (j = 0; j < input_length; ++j) { ... }` inside the main encoding
/// loop, with `n` and `b` fixed.
pub open spec fn c_encode_j(input: Seq<u32>, j: nat, n: int, b: nat, st: CEncode) -> Option<CEncode>
    decreases input.len() - j
{
    if j >= input.len() {
        Some(st)
    } else {
        let c = input[j as int] as int;
        // if (input[j] < n) { if (++delta == 0) return punycode_overflow; }
        if c < n && st.delta == c_maxint() {
            None
        } else {
            let delta = if c < n {
                st.delta + 1
            } else {
                st.delta
            };
            // if (input[j] == n) { ... }
            let st = if c == n {
                CEncode {
                    output: st.output + c_encode_for(delta, 36, st.bias),
                    // bias = adapt(delta, h + 1, h == b);
                    bias: c_adapt(delta, (st.h + 1) as int, st.h == b),
                    // delta = 0;
                    delta: 0,
                    // ++h;
                    h: st.h + 1,
                }
            } else {
                CEncode { delta, bias: st.bias, h: st.h, output: st.output }
            };
            c_encode_j(input, j + 1, n, b, st)
        }
    }
}

/// `while (h < input_length) { ... }`, with `n` and the state at the top
/// of an iteration.
pub open spec fn c_encode_while(input: Seq<u32>, n: int, b: nat, st: CEncode) -> Option<Seq<u32>>
    decreases c_maxint() + 1 - n via c_encode_while_decreases
{
    if st.h >= input.len() {
        Some(st.output)
    } else if n > c_maxint() {
        // Unreachable (see the modelling choices).
        None
    } else {
        // for (m = maxint, j = 0; ...) ...
        let m = c_find_m(input, 0, n, c_maxint());
        // if (m - n > (maxint - delta) / (h + 1)) return punycode_overflow;
        if m - n > (c_maxint() - st.delta) / ((st.h + 1) as int) {
            None
        } else {
            // delta += (m - n) * (h + 1); n = m;
            let delta = st.delta + (m - n) * ((st.h + 1) as int);
            let n = m;
            match c_encode_j(input, 0, n, b, CEncode { delta, bias: st.bias, h: st.h, output: st.output }) {
                None => None,
                Some(st) => {
                    // ++delta, ++n;
                    c_encode_while(
                        input,
                        n + 1,
                        b,
                        CEncode { delta: st.delta + 1, bias: st.bias, h: st.h, output: st.output },
                    )
                },
            }
        }
    }
}

/// Termination of [`c_encode_while`]: `n <= m <= maxint`, so the new `n`,
/// `m + 1`, is larger and at most `maxint + 1`.
#[via_fn]
proof fn c_encode_while_decreases(input: Seq<u32>, n: int, b: nat, st: CEncode) {
    if n <= c_maxint() {
        lemma_c_find_m(input, 0, n, c_maxint());
    }
}

proof fn lemma_c_find_m(input: Seq<u32>, j: nat, n: int, m: int)
    requires
        n <= m,
    ensures
        n <= c_find_m(input, j, n, m) <= m,
    decreases input.len() - j
{
    if j < input.len() {
        let c = input[j as int] as int;
        lemma_c_find_m(input, j + 1, n, if c >= n && c < m { c } else { m });
    }
}

/// `punycode_encode` (RFC 3492 Appendix C) with null `case_flags`. `None`
/// is failure.
pub open spec fn c_punycode_encode(input: Seq<u32>) -> Option<Seq<u32>> {
    // n = initial_n; delta = out = 0; bias = initial_bias;
    let output = c_copy_basics(input, 0, seq![]);
    // h = b = out;
    let b = output.len();
    // if (b > 0) output[out++] = delimiter;
    let output = if b > 0 {
        output.push(0x2D)
    } else {
        output
    };
    c_encode_while(input, 0x80, b, CEncode { delta: 0, bias: 72, h: b, output })
}

// ===========================================================================
// Equivalence with the §6 transcription.
// ===========================================================================

/// §6.4's division test: for `w > 0` and `d >= 0`, `d > x div w` exactly
/// when `d * w > x`, whatever the sign of `x`.
pub proof fn lemma_division_test(d: int, x: int, w: int)
    requires
        w > 0,
        d >= 0,
    ensures
        (d > x / w) == (d * w > x),
{
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(x, w);
    let q = x / w;
    let r = x % w;
    assert(0 <= r < w);
    if d > q {
        assert(d * w >= (q + 1) * w) by (nonlinear_arith)
            requires d >= q + 1, w > 0;
        assert((q + 1) * w == w * q + w) by (nonlinear_arith);
    } else {
        assert(d * w <= q * w) by (nonlinear_arith)
            requires d <= q, w > 0;
        assert(q * w == w * q) by (nonlinear_arith);
    }
}

proof fn lemma_digit_equal(cp: u32)
    ensures
        match super::spec::digit_value(cp) {
            Some(d) => c_decode_digit(cp) == d,
            None => c_decode_digit(cp) == 36,
        },
{
}

proof fn lemma_encode_digit_equal(d: int)
    requires
        0 <= d < 36,
    ensures
        c_encode_digit(d) == super::spec::digit_code_point(d as nat),
{
}

proof fn lemma_adapt_for_equal(delta: nat, k: nat)
    ensures
        c_adapt_for(delta as int, k as int) == super::spec::adapt_loop(delta, k) as int,
    decreases delta
{
    if delta > 455 {
        lemma_adapt_for_equal(delta / 35, k + 36);
    }
}

proof fn lemma_adapt_equal(delta: nat, numpoints: nat, firsttime: bool)
    requires
        numpoints >= 1,
    ensures
        c_adapt(delta as int, numpoints as int, firsttime) == super::spec::adapt(delta, numpoints, firsttime) as int,
{
    let d1: nat = if firsttime {
        delta / 700
    } else {
        delta / 2
    };
    lemma_adapt_for_equal(d1 + d1 / numpoints, 0);
}

proof fn lemma_find_b(input: Seq<u32>, j: nat)
    requires
        j <= input.len(),
    ensures
        c_find_b(
            input,
            j,
            match super::spec::last_delimiter(input, j) {
                Some(d) => d,
                None => 0,
            },
        ) == match super::spec::last_delimiter(input, input.len()) {
            Some(d) => d,
            None => 0,
        },
    decreases input.len() - j
{
    if j < input.len() {
        lemma_find_b(input, j + 1);
    }
}

proof fn lemma_last_delimiter_bound(input: Seq<u32>, end: nat)
    ensures
        super::spec::last_delimiter(input, end) matches Some(d) ==> d < end && d < input.len(),
    decreases end
{
    if end > 0 && end <= input.len() {
        lemma_last_delimiter_bound(input, (end - 1) as nat);
    }
}

proof fn lemma_copy_basic(input: Seq<u32>, j: nat, b: nat)
    requires
        j <= b <= input.len(),
    ensures
        c_copy_basic(input, j, b, input.subrange(0, j as int)) == if exists|x: int|
            j <= x < b && !super::spec::is_basic(#[trigger] input[x]) {
            None
        } else {
            Some(input.subrange(0, b as int))
        },
    decreases b - j
{
    if j < b {
        assert(input.subrange(0, j as int).push(input[j as int]) =~= input.subrange(0, j as int + 1));
        lemma_copy_basic(input, j + 1, b);
        if exists|x: int| j + 1 <= x < b && !super::spec::is_basic(#[trigger] input[x]) {
            let x = choose|x: int| j + 1 <= x < b && !super::spec::is_basic(#[trigger] input[x]);
            assert(j <= x < b);
        }
    }
}

proof fn lemma_decode_for_equal(input: Seq<u32>, position: nat, i: nat, w: nat, k: nat, bias: nat)
    requires
        w >= 1,
    ensures
        c_decode_for(input, position, i as int, w as int, k as int, bias as int) == match super::spec::decode_vli(
            input,
            position,
            i,
            w,
            k,
            bias,
        ) {
            Some((i2, p2)) => Some((p2, i2 as int)),
            None => None,
        },
    decreases input.len() - position
{
    if position < input.len() {
        let cp = input[position as int];
        lemma_digit_equal(cp);
        if let Some(digit) = super::spec::digit_value(cp) {
            lemma_division_test(digit as int, c_maxint() - i, w as int);
            let t = super::spec::threshold(k, bias);
            lemma_division_test(w as int, c_maxint(), 36 - t);
            assert(w * (36 - t) >= 1) by (nonlinear_arith)
                requires w >= 1, t <= 26;
            assert(w * (36 - t) == w * ((36 - t) as nat));
            lemma_decode_for_equal(input, position + 1, i + digit * w, w * (36 - t) as nat, k + 36, bias);
        }
    }
}

proof fn lemma_decode_vli_grows(input: Seq<u32>, position: nat, i: nat, w: nat, k: nat, bias: nat)
    ensures
        super::spec::decode_vli(input, position, i, w, k, bias) matches Some((i2, _)) ==> i2 >= i,
    decreases input.len() - position
{
    if position < input.len() {
        if let Some(digit) = super::spec::digit_value(input[position as int]) {
            let t = super::spec::threshold(k, bias);
            lemma_decode_vli_grows(input, position + 1, i + digit * w, w * (36 - t) as nat, k + 36, bias);
        }
    }
}

proof fn lemma_decode_main_equal(input: Seq<u32>, position: nat, n: nat, i: nat, bias: nat, output: Seq<u32>)
    ensures
        c_decode_main(input, position, n as int, i as int, bias as int, output) == super::spec::decode_loop(
            input,
            position,
            n,
            i,
            bias,
            output,
        ),
    decreases input.len() - position
{
    if position < input.len() {
        lemma_decode_for_equal(input, position, i, 1, 36, bias);
        lemma_decode_vli_grows(input, position, i, 1, 36, bias);
        super::termination::lemma_decode_vli_advances(input, position, i, 1, 36, bias);
        if let Some((i2, p2)) = super::spec::decode_vli(input, position, i, 1, 36, bias) {
            let out = output.len();
            lemma_adapt_equal((i2 - i) as nat, out + 1, i == 0);
            let new_bias = super::spec::adapt((i2 - i) as nat, out + 1, i == 0);
            let new_n = n + i2 / (out + 1);
            let new_i = i2 % (out + 1);
            lemma_decode_main_equal(input, p2, new_n, new_i + 1, new_bias, output.insert(new_i as int, new_n as u32));
        }
    }
}

/// The two decoders agree on every input.
pub proof fn lemma_decode_equal(input: Seq<u32>)
    ensures
        c_punycode_decode(input) == super::spec::punycode_decode(input),
{
    lemma_find_b(input, 0);
    lemma_last_delimiter_bound(input, input.len());
    let b = c_find_b(input, 0, 0);
    assert(input.subrange(0, 0) =~= Seq::<u32>::empty());
    lemma_copy_basic(input, 0, b);
    super::lemmas::lemma_contains_non_basic(input.subrange(0, b as int));
    if exists|x: int| 0 <= x < b && !super::spec::is_basic(#[trigger] input[x]) {
        let x = choose|x: int| 0 <= x < b && !super::spec::is_basic(#[trigger] input[x]);
        assert(input.subrange(0, b as int)[x] == input[x]);
    }
    if super::spec::contains_non_basic(input.subrange(0, b as int)) {
        let x = choose|x: int|
            0 <= x < input.subrange(0, b as int).len() && !super::spec::is_basic(
                #[trigger] input.subrange(0, b as int)[x],
            );
        assert(input.subrange(0, b as int)[x] == input[x]);
    }
    lemma_decode_main_equal(input, if b > 0 { b + 1 } else { 0 }, 0x80, 0, 72, input.subrange(0, b as int));
}

proof fn lemma_copy_basics_equal(input: Seq<u32>, j: nat)
    requires
        j <= input.len(),
    ensures
        c_copy_basics(input, j, super::spec::basic_code_points(input.subrange(0, j as int)))
            == super::spec::basic_code_points(input),
    decreases input.len() - j
{
    if j < input.len() {
        let next = input.subrange(0, j as int + 1);
        assert(next.drop_last() =~= input.subrange(0, j as int));
        lemma_copy_basics_equal(input, j + 1);
    } else {
        assert(input.subrange(0, j as int) =~= input);
    }
}

/// `c_find_m`'s `m` so far is the minimum so far, or `maxint`.
pub open spec fn m_so_far(input: Seq<u32>, j: nat, n: nat) -> int {
    match super::spec::min_at_least(input.subrange(0, j as int), n) {
        Some(r) => r as int,
        None => c_maxint(),
    }
}

proof fn lemma_find_m_equal(input: Seq<u32>, j: nat, n: nat)
    requires
        j <= input.len(),
    ensures
        c_find_m(input, j, n as int, m_so_far(input, j, n)) == m_so_far(input, input.len(), n),
    decreases input.len() - j
{
    if j < input.len() {
        let next = input.subrange(0, j as int + 1);
        assert(next.drop_last() =~= input.subrange(0, j as int));
        lemma_find_m_equal(input, j + 1, n);
    }
}

proof fn lemma_encode_for_equal(q: nat, k: nat, bias: nat)
    ensures
        c_encode_for(q as int, k as int, bias as int) == super::spec::encode_vli(q, k, bias),
    decreases q
{
    let t = super::spec::threshold(k, bias);
    if q < t {
        lemma_encode_digit_equal(q as int);
    } else {
        let d = (36 - t) as nat;
        let r = (q - t) as nat;
        vstd::arithmetic::div_mod::lemma_mod_bound(r as int, d as int);
        vstd::arithmetic::div_mod::lemma_div_nonincreasing(r as int, d as int);
        lemma_encode_digit_equal((t + r % d) as int);
        lemma_encode_for_equal(r / d, k + 36, bias);
    }
}

/// The C encoder's state as the §6 encoder's.
pub open spec fn as_c(st: super::spec::EncodeState) -> CEncode {
    CEncode { delta: st.delta as int, bias: st.bias as int, h: st.h, output: st.output }
}

proof fn lemma_encode_j_equal(input: Seq<u32>, j: nat, n: nat, b: nat, st: super::spec::EncodeState)
    requires
        st.delta <= c_maxint(),
    ensures
        c_encode_j(input, j, n as int, b, as_c(st)) == match super::spec::encode_inner(input, j, n, b, st) {
            Some(after) => Some(as_c(after)),
            None => None,
        },
    decreases input.len() - j
{
    if j < input.len() {
        let c = input[j as int];
        if !(c < n && st.delta + 1 > super::spec::maxint()) {
            let delta = if c < n {
                st.delta + 1
            } else {
                st.delta
            };
            let next = if c == n {
                lemma_encode_for_equal(delta, 36, st.bias);
                lemma_adapt_equal(delta, st.h + 1, st.h == b);
                super::spec::EncodeState {
                    delta: 0,
                    bias: super::spec::adapt(delta, st.h + 1, st.h == b),
                    h: st.h + 1,
                    output: st.output + super::spec::encode_vli(delta, 36, st.bias),
                }
            } else {
                super::spec::EncodeState { delta, bias: st.bias, h: st.h, output: st.output }
            };
            lemma_encode_j_equal(input, j + 1, n, b, next);
        }
    }
}

proof fn lemma_encode_while_equal(input: Seq<u32>, n: nat, b: nat, st: super::spec::EncodeState)
    requires
        n <= 0x1_0000_0000,
    ensures
        c_encode_while(input, n as int, b, as_c(st)) == super::spec::encode_outer(input, n, b, st),
    decreases 0x1_0000_0001 - n
{
    if st.h < input.len() {
        assert(input.subrange(0, input.len() as int) =~= input);
        assert(input.subrange(0, 0) =~= Seq::<u32>::empty());
        super::termination::lemma_min_at_least(input, n);
        if n <= c_maxint() {
            lemma_find_m_equal(input, 0, n);
            let m = c_find_m(input, 0, n as int, c_maxint());
            lemma_c_find_m(input, 0, n as int, c_maxint());
            lemma_division_test(m - n, c_maxint() - st.delta, (st.h + 1) as int);
            match super::spec::min_at_least(input, n) {
                Some(m2) => {
                    assert(m == m2);
                    let delta = st.delta + (m2 - n) as nat * (st.h + 1);
                    if delta <= super::spec::maxint() {
                        let start = super::spec::EncodeState { delta, bias: st.bias, h: st.h, output: st.output };
                        lemma_encode_j_equal(input, 0, m2 as nat, b, start);
                        if let Some(after) = super::spec::encode_inner(input, 0, m2 as nat, b, start) {
                            lemma_encode_while_equal(
                                input,
                                m2 as nat + 1,
                                b,
                                super::spec::EncodeState {
                                    delta: after.delta + 1,
                                    bias: after.bias,
                                    h: after.h,
                                    output: after.output,
                                },
                            );
                        }
                    }
                },
                None => {
                    // No code point is >= n: the C loop finds m = maxint,
                    // handles nothing, and stops when n passes maxint.
                    assert(m == c_maxint());
                    lemma_no_code_point_at_least(input, n);
                    let delta = st.delta + (m - n) * (st.h + 1);
                    if 0 <= delta <= c_maxint() {
                        let start = super::spec::EncodeState { delta: delta as nat, bias: st.bias, h: st.h, output: st.output };
                        lemma_encode_j_equal(input, 0, m as nat, b, start);
                        lemma_inner_handles_nothing(input, 0, m as nat, b, start);
                        if let Some(after) = super::spec::encode_inner(input, 0, m as nat, b, start) {
                            let next = CEncode { delta: (after.delta + 1) as int, bias: after.bias as int, h: after.h, output: after.output };
                            assert(c_encode_while(input, m + 1, b, next) is None);
                        }
                    }
                    assert(super::spec::encode_outer(input, n, b, st) is None);
                    assert(c_encode_while(input, n as int, b, as_c(st)) is None);
                },
            }
        } else {
            lemma_no_code_point_above_maxint(input, n);
        }
    }
}

/// With no code point `>= n`, none equals `n` or more.
proof fn lemma_no_code_point_at_least(input: Seq<u32>, n: nat)
    requires
        super::spec::min_at_least(input, n) is None,
    ensures
        forall|x: int| 0 <= x < input.len() ==> (#[trigger] input[x] as nat) < n,
    decreases input.len()
{
    if input.len() > 0 {
        lemma_no_code_point_at_least(input.drop_last(), n);
        assert forall|x: int| 0 <= x < input.len() implies (#[trigger] input[x] as nat) < n by {
            if x < input.len() - 1 {
                assert(input[x] == input.drop_last()[x]);
            }
        }
    }
}

/// No `u32` reaches `2^32`.
proof fn lemma_no_code_point_above_maxint(input: Seq<u32>, n: nat)
    requires
        n > 0xFFFF_FFFF,
    ensures
        super::spec::min_at_least(input, n) is None,
    decreases input.len()
{
    if input.len() > 0 {
        lemma_no_code_point_above_maxint(input.drop_last(), n);
    }
}

/// A pass for an `m` above every code point handles nothing.
proof fn lemma_inner_handles_nothing(input: Seq<u32>, j: nat, m: nat, b: nat, st: super::spec::EncodeState)
    requires
        forall|x: int| 0 <= x < input.len() ==> (#[trigger] input[x] as nat) < m,
    ensures
        super::spec::encode_inner(input, j, m, b, st) matches Some(after) ==> after.h == st.h,
    decreases input.len() - j
{
    if j < input.len() {
        let c = input[j as int];
        if !(c < m && st.delta + 1 > super::spec::maxint()) {
            lemma_inner_handles_nothing(
                input,
                j + 1,
                m,
                b,
                super::spec::EncodeState { delta: st.delta + 1, bias: st.bias, h: st.h, output: st.output },
            );
        }
    }
}

/// The two encoders agree on every input.
pub proof fn lemma_encode_equal(input: Seq<u32>)
    ensures
        c_punycode_encode(input) == super::spec::punycode_encode(input),
{
    assert(input.subrange(0, 0) =~= Seq::<u32>::empty());
    lemma_copy_basics_equal(input, 0);
    let basic = super::spec::basic_code_points(input);
    let b = basic.len();
    let output = if b > 0 {
        basic.push(0x2D)
    } else {
        basic
    };
    lemma_encode_while_equal(input, 0x80, b, super::spec::EncodeState { delta: 0, bias: 72, h: b, output });
}

} // verus!
