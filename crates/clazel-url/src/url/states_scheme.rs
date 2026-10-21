//! The executable scheme start, scheme and no scheme states (URL §4.4),
//! each proven to do what its spec function does ([`super::machine::flow_ok`]).
//! The step comments live in [`super::spec`].

use super::machine::{ExecMachine, Flow, advance, back, skip, c_at_exec, ctx_of, flow_ok, wf};
use super::record::{ParsedPath, ParsedUrl, clone_opt_str, clone_path, eq_str, is_file, is_special_scheme_exec, opt_ref_url_view};
use crate::host::record::copy;
#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// "scheme start state"
pub fn scheme_start_state(input: &[u32], base: Option<&ParsedUrl>, m: &mut ExecMachine) -> (flow: Flow)
    requires
        wf(ctx_of(input@, opt_ref_url_view(base)), old(m)@),
        old(m).state is SchemeStart,
    ensures
        flow_ok(ctx_of(input@, opt_ref_url_view(base)), super::spec::scheme_start_state(ctx_of(input@, opt_ref_url_view(base)), old(m)@), final(m)@, flow),
{
    let ghost ctx = ctx_of(input@, opt_ref_url_view(base));
    if let Some(c) = c_at_exec(input, m.pointer) {
        if super::machine::is_ascii_alpha_exec(c) {
            let lower = super::machine::ascii_lowercase_exec(c);
            m.buffer.push(lower);
            m.state = State::Scheme;
            return advance(m, input.len());
        }
    }
    m.state = State::NoScheme;
    back(m)
}

/// "scheme state", step 1's condition.
fn is_scheme_code_point(c: u32) -> (r: bool)
    ensures
        r == (is_ascii_alphanumeric(c) || c == 0x2B || c == 0x2D || c == 0x2E),
{
    (0x30 <= c && c <= 0x39) || super::machine::is_ascii_alpha_exec(c) || c == 0x2B || c == 0x2D || c == 0x2E
}

/// "scheme state"
pub fn scheme_state(input: &[u32], base: Option<&ParsedUrl>, m: &mut ExecMachine) -> (flow: Flow)
    requires
        wf(ctx_of(input@, opt_ref_url_view(base)), old(m)@),
        old(m).state is Scheme,
    ensures
        flow_ok(ctx_of(input@, opt_ref_url_view(base)), super::spec::scheme_state(ctx_of(input@, opt_ref_url_view(base)), old(m)@), final(m)@, flow),
{
    let ghost ctx = ctx_of(input@, opt_ref_url_view(base));
    let c = c_at_exec(input, m.pointer);
    if let Some(c) = c {
        if is_scheme_code_point(c) {
            // 1.
            let lower = super::machine::ascii_lowercase_exec(c);
            m.buffer.push(lower);
            return advance(m, input.len());
        }
        if c == 0x3A {
            // 2.
            return scheme_state_colon(input, base, m);
        }
    }
    // 3. "start over": the next run is at the first code point.
    m.buffer = Vec::new();
    m.state = State::NoScheme;
    m.pointer = 0;
    assert(m.buffer@ =~= seq![]);
    Flow::Next
}

/// Scheme state step 2 (no state override).
fn scheme_state_colon(input: &[u32], base: Option<&ParsedUrl>, m: &mut ExecMachine) -> (flow: Flow)
    requires
        wf(ctx_of(input@, opt_ref_url_view(base)), old(m)@),
        old(m).state is Scheme,
        crate::host::spec::c_at(input@, old(m)@.pointer) == Some(0x3Au32),
    ensures
        flow_ok(ctx_of(input@, opt_ref_url_view(base)), super::spec::scheme_state_colon(ctx_of(input@, opt_ref_url_view(base)), old(m)@), final(m)@, flow),
{
    let ghost ctx = ctx_of(input@, opt_ref_url_view(base));
    // 2.2
    m.url.scheme = copy(m.buffer.as_slice());
    // 2.4
    m.buffer = Vec::new();
    assert(m.buffer@ =~= seq![]);
    let special = is_special_scheme_exec(m.url.scheme.as_slice());
    if is_file(m.url.scheme.as_slice()) {
        // 2.5
        m.state = State::File;
        advance(m, input.len())
    } else if special && match base {
        Some(b) => eq_str(b.scheme.as_slice(), m.url.scheme.as_slice()),
        None => false,
    } {
        // 2.6
        m.state = State::SpecialRelativeOrAuthority;
        advance(m, input.len())
    } else if special {
        // 2.7
        m.state = State::SpecialAuthoritySlashes;
        advance(m, input.len())
    } else if super::machine::remaining_starts_with_exec(input, m.pointer, 0x2F) {
        // 2.8
        m.state = State::PathOrAuthority;
        skip(m, input.len())
    } else {
        // 2.9
        m.url.path = ParsedPath::Opaque(Vec::new());
        assert(m.url.path@ == UrlPath::Opaque(seq![]));
        m.state = State::OpaquePath;
        advance(m, input.len())
    }
}

/// "no scheme state"
pub fn no_scheme_state(input: &[u32], base: Option<&ParsedUrl>, m: &mut ExecMachine) -> (flow: Flow)
    requires
        wf(ctx_of(input@, opt_ref_url_view(base)), old(m)@),
        old(m).state is NoScheme,
    ensures
        flow_ok(ctx_of(input@, opt_ref_url_view(base)), super::spec::no_scheme_state(ctx_of(input@, opt_ref_url_view(base)), old(m)@), final(m)@, flow),
{
    let ghost ctx = ctx_of(input@, opt_ref_url_view(base));
    let c = c_at_exec(input, m.pointer);
    let is_hash = c == Some(0x23u32);
    match base {
        None => Flow::Failure,
        Some(b) => {
            let opaque = matches!(b.path, ParsedPath::Opaque(_));
            if opaque && !is_hash {
                // 1.
                Flow::Failure
            } else if opaque && is_hash {
                // 2.
                m.url.scheme = copy(b.scheme.as_slice());
                m.url.path = clone_path(&b.path);
                m.url.query = clone_opt_str(&b.query);
                m.url.fragment = Some(Vec::new());
                assert(crate::host::record::opt_seq(m.url.fragment) == Some(Seq::<u32>::empty()));
                m.state = State::Fragment;
                advance(m, input.len())
            } else if !is_file(b.scheme.as_slice()) {
                // 3.
                m.state = State::Relative;
                back(m)
            } else {
                // 4.
                m.state = State::File;
                back(m)
            }
        },
    }
}

} // verus!
