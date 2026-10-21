//! The executable scheme start, scheme and no scheme states (URL §4.4),
//! each proven to do what its spec function does ([`super::machine::flow_ok`]).
//! The step comments live in [`super::spec`].

use super::machine::{ExecMachine, Flow, advance, back, c_at_exec, skip};
use super::record::{
    ParsedPath, ParsedUrl, clone_opt_str, clone_path, default_port_exec, eq_str, is_file,
    is_special_scheme_exec,
};
#[allow(unused_imports)]
use super::spec::*;
use crate::host::record::ParsedHost;
use crate::host::record::copy;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// "scheme start state"
pub fn scheme_start_state(input: &[u32], Ghost(base): Ghost<Option<Url>>, so: &Option<State>, m: &mut ExecMachine) -> (flow: Flow)
    requires
        super::machine::wf(super::machine::ctx_of(input@, base, *so), old(m)@),
        old(m).state is SchemeStart,
    ensures
        super::machine::flow_ok(super::machine::ctx_of(input@, base, *so), super::spec::scheme_start_state(super::machine::ctx_of(input@, base, *so), old(m)@), old(m)@, final(m)@, flow),
{
    let ghost ctx = super::machine::ctx_of(input@, base, *so);
    match c_at_exec(input, m.pointer) {
        Some(c) if super::machine::is_ascii_alpha_exec(c) => {
            let lower = super::machine::ascii_lowercase_exec(c);
            m.buffer.push(lower);
            m.state = State::Scheme;
            return advance(m, input.len());
        },
        _ => {},
    }
    if so.is_some() {
        // 3.
        return Flow::Failure;
    }
    // 2.
    m.state = State::NoScheme;
    back()
}

/// "scheme state", step 1's condition.
fn is_scheme_code_point(c: u32) -> (r: bool)
    ensures
        r == (is_ascii_alphanumeric(c) || c == 0x2B || c == 0x2D || c == 0x2E),
{
    (0x30..=0x39).contains(&c) || super::machine::is_ascii_alpha_exec(c) || c == 0x2B || c == 0x2D || c == 0x2E
}

/// "scheme state"
pub fn scheme_state(input: &[u32], base: Option<&ParsedUrl>, so: &Option<State>, m: &mut ExecMachine) -> (flow: Flow)
    requires
        super::machine::wf(super::machine::ctx_of(input@, super::record::opt_ref_url_view(base), *so), old(m)@),
        old(m).state is Scheme,
    ensures
        super::machine::flow_ok(super::machine::ctx_of(input@, super::record::opt_ref_url_view(base), *so), super::spec::scheme_state(super::machine::ctx_of(input@, super::record::opt_ref_url_view(base), *so), old(m)@), old(m)@, final(m)@, flow),
{
    let ghost ctx = super::machine::ctx_of(input@, super::record::opt_ref_url_view(base), *so);
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
            return scheme_state_colon(input, base, so, m);
        }
    }
    if so.is_some() {
        // 4.
        return Flow::Failure;
    }
    // 3. "start over": the next run is at the first code point.
    m.buffer = Vec::new();
    m.state = State::NoScheme;
    m.pointer = 0;
    assert(m.buffer@ =~= seq![]);
    Flow::Next
}

/// Scheme state step 2.
fn scheme_state_colon(input: &[u32], base: Option<&ParsedUrl>, so: &Option<State>, m: &mut ExecMachine) -> (flow: Flow)
    requires
        super::machine::wf(super::machine::ctx_of(input@, super::record::opt_ref_url_view(base), *so), old(m)@),
        old(m).state is Scheme,
        crate::host::spec::c_at(input@, old(m)@.pointer) == Some(0x3Au32),
    ensures
        super::machine::flow_ok(super::machine::ctx_of(input@, super::record::opt_ref_url_view(base), *so), super::spec::scheme_state_colon(super::machine::ctx_of(input@, super::record::opt_ref_url_view(base), *so), old(m)@), old(m)@, final(m)@, flow),
{
    let ghost ctx = super::machine::ctx_of(input@, super::record::opt_ref_url_view(base), *so);
    if so.is_some() {
        // 2.1
        let url_special = is_special_scheme_exec(m.url.scheme.as_slice());
        let buffer_special = is_special_scheme_exec(m.buffer.as_slice());
        if url_special && !buffer_special {
            // 2.1.1
            return Flow::Return;
        }
        if !url_special && buffer_special {
            // 2.1.2
            return Flow::Return;
        }
        if (!m.url.username.is_empty() || !m.url.password.is_empty() || m.url.port.is_some()) && is_file(
            m.buffer.as_slice(),
        ) {
            // 2.1.3
            return Flow::Return;
        }
        if is_file(m.url.scheme.as_slice()) && matches!(m.url.host, Some(ParsedHost::Empty)) {
            // 2.1.4
            return Flow::Return;
        }
        // 2.2
        m.url.scheme = copy(m.buffer.as_slice());
        // 2.3.1
        let default = default_port_exec(m.url.scheme.as_slice());
        let is_default = match (m.url.port, default) {
            (Some(p), Some(d)) => p == d,
            (None, None) => true,
            _ => false,
        };
        if is_default {
            m.url.port = None;
        }
        // 2.3.2
        return Flow::Return;
    }
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
        skip(m, Ghost(input.len() as nat))
    } else {
        // 2.9
        m.url.path = ParsedPath::Opaque(Vec::new());
        assert(m.url.path@ == UrlPath::Opaque(seq![]));
        m.state = State::OpaquePath;
        advance(m, input.len())
    }
}

/// "no scheme state"
pub fn no_scheme_state(input: &[u32], base: Option<&ParsedUrl>, Ghost(so): Ghost<Option<State>>, m: &mut ExecMachine) -> (flow: Flow)
    requires
        super::machine::wf(super::machine::ctx_of(input@, super::record::opt_ref_url_view(base), so), old(m)@),
        old(m).state is NoScheme,
    ensures
        super::machine::flow_ok(super::machine::ctx_of(input@, super::record::opt_ref_url_view(base), so), super::spec::no_scheme_state(super::machine::ctx_of(input@, super::record::opt_ref_url_view(base), so), old(m)@), old(m)@, final(m)@, flow),
{
    let ghost ctx = super::machine::ctx_of(input@, super::record::opt_ref_url_view(base), so);
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
                back()
            } else {
                // 4.
                m.state = State::File;
                back()
            }
        },
    }
}

} // verus!
