//! The executable basic URL parser's variables, viewed as the spec's
//! [`Machine`], and how one exec run is related to one spec run.
//!
//! An exec state function mirrors its spec function: it updates the
//! machine in place and returns a [`Flow`]. The pointer field holds the
//! pointer *for the next run*: when the spec run ends with pointer at `p`
//! and `p` is not at the EOF code point, step 9 increases it, so the exec
//! machine's pointer is `p + 1` (never negative, even after "decrease
//! pointer by 1" at the start of input). When `p` is at the EOF code
//! point, the exec run returns [`Flow::Stop`] and the spec's step 10
//! returns url. [`flow_ok`] states this relation exactly.

use super::record::ParsedUrl;
#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The basic URL parser's variables (URL §4.4 steps 4 to 8, and url).
pub struct ExecMachine {
    /// url
    pub url: ParsedUrl,
    /// state
    pub state: State,
    /// buffer
    pub buffer: Vec<u32>,
    /// atSignSeen
    pub at_sign_seen: bool,
    /// insideBrackets
    pub inside_brackets: bool,
    /// passwordTokenSeen
    pub password_token_seen: bool,
    /// pointer, for the run about to happen
    pub pointer: usize,
}

impl View for ExecMachine {
    type V = Machine;

    open spec fn view(&self) -> Machine {
        Machine {
            url: self.url@,
            state: self.state,
            buffer: self.buffer@,
            at_sign_seen: self.at_sign_seen,
            inside_brackets: self.inside_brackets,
            password_token_seen: self.password_token_seen,
            pointer: self.pointer as int,
        }
    }
}

/// What an exec run tells the loop.
pub enum Flow {
    /// "return failure"
    Failure,
    /// The run ended with pointer at the EOF code point: step 10 returns
    /// url.
    Stop,
    /// Run again (the machine's pointer has been increased by step 9).
    Next,
}

/// The parser's inputs as the exec parser runs it: no state override, and
/// `clazel-idna`'s domain parser.
pub open spec fn ctx_of(input: Seq<u32>, base: Option<Url>) -> Ctx {
    Ctx {
        input: input,
        base: base,
        state_override: None,
        domain_parser: super::contract::url_domain_parser(),
    }
}

/// What holds of the machine before every run: pointer is within input
/// (or at the EOF code point), buffer holds scalar values (outside the
/// path state, where it holds percent-encoded output), and, in the states
/// before the host state, buffer is no longer than pointer (it holds code
/// points read since the last reset, at most one per run). The last fact
/// is what keeps the authority state's "decrease pointer by buffer's code
/// point length + 1" from going below −1. In the port state, buffer holds
/// ASCII digits.
pub open spec fn wf(ctx: Ctx, m: Machine) -> bool {
    clazel_encoding::utf8::spec::all_scalar_values(ctx.input) && ctx.state_override is None && ctx.domain_parser
        == super::contract::url_domain_parser() && 0 <= m.pointer <= ctx.input.len() && (!(m.state is Path)
        ==> clazel_encoding::utf8::spec::all_scalar_values(m.buffer)) && (super::termination::phase(m.state) >= 1
        ==> m.buffer.len() <= m.pointer) && (m.state is Port ==> all_ascii_digits(m.buffer))
}

/// Every code point of `s` is an ASCII digit (the port state's buffer).
pub open spec fn all_ascii_digits(s: Seq<u32>) -> bool {
    forall|k: int| 0 <= k < s.len() ==> crate::host::spec::is_ascii_digit(#[trigger] s[k])
}

/// The exec run that returned `flow` and left the machine as `after` did
/// what the spec run's `step` says, and the next run starts well formed.
pub open spec fn flow_ok(ctx: Ctx, step: Step, after: Machine, flow: Flow) -> bool {
    match step {
        Step::Failure => flow is Failure,
        Step::Return(_) => false,
        Step::Continue(n) => if n.pointer >= ctx.input.len() {
            flow is Stop && after.url == n.url
        } else {
            flow is Next && after == (Machine { pointer: n.pointer + 1, ..n }) && wf(ctx, after)
        },
    }
}

/// c (URL §1.2): the code point at `p`, or `None` for the EOF code point.
pub fn c_at_exec(input: &[u32], p: usize) -> (c: Option<u32>)
    ensures
        c == crate::host::spec::c_at(input@, p as int),
{
    match input.get(p) {
        Some(c) => Some(*c),
        None => None,
    }
}

/// "remaining starts with" `x`.
pub fn remaining_starts_with_exec(input: &[u32], p: usize, x: u32) -> (r: bool)
    requires
        p <= input.len(),
    ensures
        r == remaining_starts_with(input@, p as int, x),
{
    p < input.len() && match input.get(p + 1) {
        Some(c) => *c == x,
        None => false,
    }
}

/// An ASCII alpha (Infra §4.6).
pub fn is_ascii_alpha_exec(c: u32) -> (r: bool)
    ensures
        r == is_ascii_alpha(c),
{
    (0x41 <= c && c <= 0x5A) || (0x61 <= c && c <= 0x7A)
}

/// ASCII lowercase a code point (Infra §4.6).
pub fn ascii_lowercase_exec(c: u32) -> (r: u32)
    ensures
        r == ascii_lowercase(c),
        clazel_encoding::utf8::spec::is_scalar_value(c) ==> clazel_encoding::utf8::spec::is_scalar_value(r),
{
    if 0x41 <= c && c <= 0x5A {
        c + 0x20
    } else {
        c
    }
}

/// End a run in which pointer did not move: stop at the EOF code point,
/// otherwise increase pointer by 1 (step 9).
pub fn advance(m: &mut ExecMachine, len: usize) -> (flow: Flow)
    ensures
        old(m).pointer >= len ==> flow is Stop && final(m)@ == old(m)@,
        old(m).pointer < len ==> flow is Next && final(m)@ == (Machine { pointer: old(m)@.pointer + 1, ..old(m)@ }),
{
    if m.pointer >= len {
        Flow::Stop
    } else {
        m.pointer = m.pointer + 1;
        Flow::Next
    }
}

/// End a run that decreased pointer by 1: step 9 increases it again, so
/// the next run reads the same code point.
pub fn back(m: &mut ExecMachine) -> (flow: Flow)
    ensures
        flow is Next && final(m)@ == old(m)@,
{
    Flow::Next
}

/// End a run that increased pointer by 1 ("remaining starts with" made
/// sure there is a code point there): step 9 increases it once more.
pub fn skip(m: &mut ExecMachine, len: usize) -> (flow: Flow)
    requires
        old(m).pointer + 1 < len,
    ensures
        flow is Next && final(m)@ == (Machine { pointer: old(m)@.pointer + 2, ..old(m)@ }),
{
    m.pointer = m.pointer + 2;
    Flow::Next
}

} // verus!
