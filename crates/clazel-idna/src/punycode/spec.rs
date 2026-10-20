//! Executable-style specification of Punycode, transcribed from RFC 3492,
//! "Punycode: A Bootstring encoding of Unicode for Internationalized Domain
//! Names in Applications (IDNA)" (A. Costello, March 2003,
//! <https://www.rfc-editor.org/rfc/rfc3492>; no errata affect §5 or §6).
//! Nothing here runs; it defines what "correct" means. Each `//` comment
//! quotes the pseudocode line of §6.1, §6.2 or §6.3 it transcribes.
//!
//! Modelling choices (each one is a deliberate, reviewable deviation in form,
//! never in meaning):
//! - Strings are `Seq<u32>`, one element per code point. §6 says "code
//!   points are integers"; the RFC's only restriction on them is that they
//!   be nonnegative (§5), and a `u32` holds every value `maxint` allows.
//! - The pseudocode's integer variables (`n`, `i`, `w`, `delta`, `bias`,
//!   `q`, `t`, `k`, `h`, `b`) are `nat`: unbounded. "Fail on overflow"
//!   (§6.2, §6.3) is a check that the new value exceeds [`maxint`], made
//!   exactly where the pseudocode says "fail on overflow". §6.4: "maxint is
//!   the greatest integer for which maxint + 1 cannot be represented". The
//!   RFC leaves the width to the implementation (§6.4: 26 bits suffice for
//!   valid IDNA labels); we use 32 bits, the width of the sample
//!   implementation's `punycode_uint` (Appendix C) on every platform we
//!   build for, and of a `u32` code point, so every value `n` can take is a
//!   code point the output can hold.
//! - "Fail" is `None`.
//! - The parts in {braces} are omitted, as §6.2 and §6.3 allow for
//!   Punycode: `+ tmin` in the clamping of `t`, "{if n is a basic code
//!   point then fail}", "{if the input contains a non-basic code point < n
//!   then fail}", "{non-basic}" and "{or c is basic}". The RFC's notes after
//!   each procedure give the argument (`initial_n` = 0x80 exceeds every
//!   basic code point; code points are unsigned).
//! - Mixed-case annotation (Appendix A) is not modelled: the decoder
//!   ignores the case of basic code points and the encoder takes no case
//!   flags. §5: "An encoder SHOULD output only uppercase forms or only
//!   lowercase forms": [`digit_code_point`] outputs lowercase, the form IDNA
//!   and the URL Standard's tests use.
//! - The loops are recursive functions over the loop state: §6.2's outer
//!   loop is [`decode_loop`] and its inner loop over `k` is [`decode_vli`]
//!   (generalized variable-length integer, §3.3); §6.3's outer loop is
//!   [`encode_outer`], its loop over the input is [`encode_inner`], and its
//!   loop over `k` is [`encode_vli`]. "consume a code point" is advancing a
//!   position into the input; "the input is exhausted" is the position
//!   reaching its length. Output accumulates in a sequence as in the RFC.
//! - §6.3 "let m = the minimum code point >= n in the input": such a code
//!   point always exists while `h < length(input)`, because the code points
//!   less than `n` are exactly the `h` handled ones. [`encode_outer`] fails
//!   if there is none; that branch is unreachable.
//! - §6.1's `adapt` may change `delta` and `k` in place; it is a function
//!   of its arguments here. The RFC's note after §6.1 says why this is the
//!   same.

#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------
// §5 Parameter values for Punycode.
// ---------------------------------------------------------------------------

/// "base = 36"
pub open spec fn base() -> nat {
    36
}

/// "tmin = 1"
pub open spec fn tmin() -> nat {
    1
}

/// "tmax = 26"
pub open spec fn tmax() -> nat {
    26
}

/// "skew = 38"
pub open spec fn skew() -> nat {
    38
}

/// "damp = 700"
pub open spec fn damp() -> nat {
    700
}

/// "initial_bias = 72"
pub open spec fn initial_bias() -> nat {
    72
}

/// "initial_n = 128 = 0x80"
pub open spec fn initial_n() -> nat {
    128
}

/// §6.4: "the greatest integer for which maxint + 1 cannot be represented"
/// (32-bit unsigned; see the modelling choices).
pub open spec fn maxint() -> nat {
    0xFFFF_FFFF
}

/// §5: "The basic code points are the ASCII code points (0..7F)".
pub open spec fn is_basic(c: u32) -> bool {
    c < 0x80
}

/// §5: "of which U+002D (-) is the delimiter".
pub open spec fn delimiter() -> u32 {
    0x2D
}

/// §5's digit-values: "41..5A (A-Z) = 0 to 25, respectively; 61..7A (a-z)
/// = 0 to 25, respectively; 30..39 (0-9) = 26 to 35, respectively". A code
/// point with no digit-value gives `None`. ("A decoder MUST recognize the
/// letters in both uppercase and lowercase forms".)
pub open spec fn digit_value(c: u32) -> Option<nat> {
    if 0x41 <= c <= 0x5A {
        Some((c - 0x41) as nat)
    } else if 0x61 <= c <= 0x7A {
        Some((c - 0x61) as nat)
    } else if 0x30 <= c <= 0x39 {
        Some((c - 0x30 + 26) as nat)
    } else {
        None
    }
}

/// §6.3 "output the code point for digit d", for `d` from 0 to 35: the
/// lowercase form of §5's table (see the modelling choices).
pub open spec fn digit_code_point(d: nat) -> u32 {
    if d < 26 {
        (0x61 + d) as u32
    } else {
        (0x30 + (d - 26)) as u32
    }
}

/// §6.2 and §6.3: "let t = tmin if k <= bias {+ tmin}, or tmax if k >= bias
/// + tmax, or k - bias otherwise".
pub open spec fn threshold(k: nat, bias: nat) -> nat {
    if k <= bias {
        tmin()
    } else if k >= bias + tmax() {
        tmax()
    } else {
        (k - bias) as nat
    }
}

// ---------------------------------------------------------------------------
// §6.1 Bias adaptation function.
// ---------------------------------------------------------------------------

/// §6.1's loop: "while delta > ((base - tmin) * tmax) div 2 do begin let
/// delta = delta div (base - tmin); let k = k + base end; return k + (((base
/// - tmin + 1) * delta) div (delta + skew))".
pub open spec fn adapt_loop(delta: nat, k: nat) -> nat
    decreases delta via adapt_loop_decreases
{
    if delta > ((base() - tmin()) * tmax()) as nat / 2 {
        adapt_loop(delta / (base() - tmin()) as nat, k + base())
    } else {
        k + ((base() - tmin() + 1) * delta) as nat / (delta + skew())
    }
}

/// Termination of [`adapt_loop`]: `delta div (base - tmin)` is smaller.
#[via_fn]
pub proof fn adapt_loop_decreases(delta: nat, k: nat) {
    super::termination::lemma_adapt_loop_shrinks(delta);
}

/// §6.1 "function adapt(delta,numpoints,firsttime)". Every caller passes
/// `numpoints >= 1` (a length plus one).
pub open spec fn adapt(delta: nat, numpoints: nat, firsttime: bool) -> nat {
    // "if firsttime then let delta = delta div damp
    //  else let delta = delta div 2"
    let delta = if firsttime {
        delta / damp()
    } else {
        delta / 2
    };
    // "let delta = delta + (delta div numpoints)"
    let delta = delta + delta / numpoints;
    // "let k = 0", then the loop.
    adapt_loop(delta, 0)
}

// ---------------------------------------------------------------------------
// §6.2 Decoding procedure.
// ---------------------------------------------------------------------------

/// The position of the last delimiter among `input[0..end]`, searching
/// from the end; `None` if there is none.
pub open spec fn last_delimiter(input: Seq<u32>, end: nat) -> Option<nat>
    decreases end
{
    if end == 0 || end > input.len() {
        None
    } else if input[end - 1] == delimiter() {
        Some((end - 1) as nat)
    } else {
        last_delimiter(input, (end - 1) as nat)
    }
}

/// Whether `s` contains a non-basic code point. Recursion from the end.
pub open spec fn contains_non_basic(s: Seq<u32>) -> bool
    decreases s.len()
{
    if s.len() == 0 {
        false
    } else {
        !is_basic(s.last()) || contains_non_basic(s.drop_last())
    }
}

/// §6.2's inner loop, "for k = base to infinity in steps of base", from the
/// code point at `position`, with `i`, `w` and `k` as they are at the top of
/// this iteration. Returns `i` and the position after the last code point
/// consumed, or `None` for failure.
pub open spec fn decode_vli(input: Seq<u32>, position: nat, i: nat, w: nat, k: nat, bias: nat) -> Option<(nat, nat)>
    decreases input.len() - position
{
    if position >= input.len() {
        // "consume a code point, or fail if there was none to consume"
        None
    } else {
        match digit_value(input[position as int]) {
            // "let digit = the code point's digit-value, fail if it has none"
            None => None,
            Some(digit) => {
                // "let i = i + digit * w, fail on overflow"
                let i = i + digit * w;
                if i > maxint() {
                    None
                } else {
                    // "let t = tmin if k <= bias {+ tmin}, or tmax if k >= bias
                    //  + tmax, or k - bias otherwise"
                    let t = threshold(k, bias);
                    if digit < t {
                        // "if digit < t then break"
                        Some((i, position + 1))
                    } else {
                        // "let w = w * (base - t), fail on overflow"
                        let w = w * (base() - t) as nat;
                        if w > maxint() {
                            None
                        } else {
                            decode_vli(input, position + 1, i, w, k + base(), bias)
                        }
                    }
                }
            }
        }
    }
}

/// §6.2's outer loop, "while the input is not exhausted do begin ... end",
/// from `position`, with `n`, `i`, `bias` and `output` as they are at the
/// top of this iteration.
pub open spec fn decode_loop(input: Seq<u32>, position: nat, n: nat, i: nat, bias: nat, output: Seq<u32>) -> Option<Seq<u32>>
    decreases input.len() - position via decode_loop_decreases
{
    if position >= input.len() {
        // The input is exhausted: the result is output.
        Some(output)
    } else {
        // "let oldi = i"
        let oldi = i;
        // "let w = 1", then the inner loop from k = base.
        match decode_vli(input, position, i, 1, base(), bias) {
            None => None,
            Some((i, position)) => {
                // "let bias = adapt(i - oldi, length(output) + 1, test oldi is 0?)"
                let bias = adapt((i - oldi) as nat, output.len() + 1, oldi == 0);
                // "let n = n + i div (length(output) + 1), fail on overflow"
                let n = n + i / (output.len() + 1);
                if n > maxint() {
                    None
                } else {
                    // "let i = i mod (length(output) + 1)"
                    let i = i % (output.len() + 1);
                    // "{if n is a basic code point then fail}": omitted.
                    // "insert n into output at position i"
                    let output = output.insert(i as int, n as u32);
                    // "increment i"
                    decode_loop(input, position, n, i + 1, bias, output)
                }
            }
        }
    }
}

/// Termination of [`decode_loop`]: each generalized variable-length
/// integer consumes at least one code point.
#[via_fn]
pub proof fn decode_loop_decreases(input: Seq<u32>, position: nat, n: nat, i: nat, bias: nat, output: Seq<u32>) {
    super::termination::lemma_decode_vli_advances(input, position, i, 1, base(), bias);
}

/// §6.2 Decoding procedure, given the input string. `None` is failure.
pub open spec fn punycode_decode(input: Seq<u32>) -> Option<Seq<u32>> {
    // "let n = initial_n", "let i = 0", "let bias = initial_bias",
    // "let output = an empty string indexed from 0"
    // "consume all code points before the last delimiter (if there is one)
    //  and copy them to output, fail on any non-basic code point"
    // "if more than zero code points were consumed then consume one more
    //  (which will be the last delimiter)"
    let (output, position) = match last_delimiter(input, input.len()) {
        None => (Seq::<u32>::empty(), 0nat),
        Some(d) => (input.subrange(0, d as int), if d > 0 { d + 1 } else { 0nat }),
    };
    if contains_non_basic(output) {
        None
    } else {
        decode_loop(input, position, initial_n(), 0, initial_bias(), output)
    }
}

// ---------------------------------------------------------------------------
// §6.3 Encoding procedure.
// ---------------------------------------------------------------------------

/// §6.3 "the number of basic code points in the input ... copy them to the
/// output in order": the basic code points of `input`, in order.
pub open spec fn basic_code_points(input: Seq<u32>) -> Seq<u32>
    decreases input.len()
{
    if input.len() == 0 {
        seq![]
    } else if is_basic(input.last()) {
        basic_code_points(input.drop_last()).push(input.last())
    } else {
        basic_code_points(input.drop_last())
    }
}

/// §6.3 "let m = the minimum {non-basic} code point >= n in the input", or
/// `None` if the input has no code point `>= n`. Recursion from the end.
pub open spec fn min_at_least(input: Seq<u32>, n: nat) -> Option<u32>
    decreases input.len()
{
    if input.len() == 0 {
        None
    } else {
        let rest = min_at_least(input.drop_last(), n);
        let c = input.last();
        if c >= n {
            match rest {
                Some(r) if r < c => Some(r),
                _ => Some(c),
            }
        } else {
            rest
        }
    }
}

/// §6.3's innermost loop, "for k = base to infinity in steps of base", with
/// `q` and `k` as they are at the top of this iteration. Returns the code
/// points it outputs, including the final "output the code point for digit
/// q" after the loop.
pub open spec fn encode_vli(q: nat, k: nat, bias: nat) -> Seq<u32>
    decreases q via encode_vli_decreases
{
    // "let t = tmin if k <= bias {+ tmin}, or tmax if k >= bias + tmax, or
    //  k - bias otherwise"
    let t = threshold(k, bias);
    if q < t {
        // "if q < t then break", then after the loop: "output the code
        // point for digit q"
        seq![digit_code_point(q)]
    } else {
        // "output the code point for digit t + ((q - t) mod (base - t))"
        // "let q = (q - t) div (base - t)"
        seq![digit_code_point(t + (q - t) as nat % (base() - t) as nat)]
            + encode_vli((q - t) as nat / (base() - t) as nat, k + base(), bias)
    }
}

/// Termination of [`encode_vli`]: `q` shrinks while `q >= t >= 1`.
#[via_fn]
pub proof fn encode_vli_decreases(q: nat, k: nat, bias: nat) {
    super::termination::lemma_encode_vli_shrinks(q, k, bias);
}

/// The encoder's variables that change inside its loops.
pub struct EncodeState {
    /// `delta`
    pub delta: nat,
    /// `bias`
    pub bias: nat,
    /// `h`: the number of code points handled so far.
    pub h: nat,
    /// The output so far.
    pub output: Seq<u32>,
}

/// §6.3 "for each code point c in the input (in order) do begin ... end",
/// from the code point at `j`, with `n` and `b` fixed during the loop.
pub open spec fn encode_inner(input: Seq<u32>, j: nat, n: nat, b: nat, state: EncodeState) -> Option<EncodeState>
    decreases input.len() - j
{
    if j >= input.len() {
        Some(state)
    } else {
        let c = input[j as int];
        if c < n && state.delta + 1 > maxint() {
            // "if c < n {or c is basic} then increment delta, fail on
            //  overflow": the overflow.
            None
        } else {
            let delta = if c < n {
                state.delta + 1
            } else {
                state.delta
            };
            let state = if c == n {
                // "if c == n then begin"
                // "let q = delta", then the loop over k and the final digit.
                let output = state.output + encode_vli(delta, base(), state.bias);
                // "let bias = adapt(delta, h + 1, test h equals b?)"
                let bias = adapt(delta, state.h + 1, state.h == b);
                // "let delta = 0", "increment h"
                EncodeState { delta: 0, bias, h: state.h + 1, output }
            } else {
                EncodeState { delta, bias: state.bias, h: state.h, output: state.output }
            };
            encode_inner(input, j + 1, n, b, state)
        }
    }
}

/// §6.3's outer loop, "while h < length(input) do begin ... end", with `n`
/// and the state as they are at the top of this iteration.
pub open spec fn encode_outer(input: Seq<u32>, n: nat, b: nat, state: EncodeState) -> Option<Seq<u32>>
    decreases 0x1_0000_0001 - n via encode_outer_decreases
{
    if state.h >= input.len() {
        // h = length(input): the loop is done, and the output is the result.
        Some(state.output)
    } else {
        // "let m = the minimum {non-basic} code point >= n in the input"
        match min_at_least(input, n) {
            // Unreachable (see the modelling choices).
            None => None,
            Some(m) => {
                // "let delta = delta + (m - n) * (h + 1), fail on overflow"
                let delta = state.delta + (m - n) as nat * (state.h + 1);
                if delta > maxint() {
                    None
                } else {
                    // "let n = m"
                    let n = m as nat;
                    // "for each code point c in the input (in order)"
                    let state = EncodeState { delta, bias: state.bias, h: state.h, output: state.output };
                    match encode_inner(input, 0, n, b, state) {
                        None => None,
                        Some(state) => {
                            // "increment delta and n"
                            let state = EncodeState {
                                delta: state.delta + 1,
                                bias: state.bias,
                                h: state.h,
                                output: state.output,
                            };
                            encode_outer(input, n + 1, b, state)
                        }
                    }
                }
            }
        }
    }
}

/// Termination of [`encode_outer`]: `n` grows to `m + 1 > n`, and stays at
/// most 2^32 because `m` is a `u32`.
#[via_fn]
pub proof fn encode_outer_decreases(input: Seq<u32>, n: nat, b: nat, state: EncodeState) {
    super::termination::lemma_min_at_least(input, n);
}

/// §6.3 Encoding procedure, given the input string. `None` is failure.
pub open spec fn punycode_encode(input: Seq<u32>) -> Option<Seq<u32>> {
    // "let n = initial_n", "let delta = 0", "let bias = initial_bias"
    // "let h = b = the number of basic code points in the input"
    let basic = basic_code_points(input);
    let b = basic.len();
    // "copy them to the output in order, followed by a delimiter if b > 0"
    let output = if b > 0 {
        basic.push(delimiter())
    } else {
        basic
    };
    // "{if the input contains a non-basic code point < n then fail}": omitted.
    encode_outer(input, initial_n(), b, EncodeState { delta: 0, bias: initial_bias(), h: b, output })
}

} // verus!
