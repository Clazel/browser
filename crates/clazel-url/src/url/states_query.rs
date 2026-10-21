//! The executable query and fragment states (URL §4.4), each proven to do
//! what its spec function does ([`super::machine::flow_ok`]). The step
//! comments live in [`super::spec`].

use super::machine::{ExecMachine, Flow, advance, c_at_exec};
use super::path_ops::opt_append_exec;
use super::record::is_special_scheme_exec;
#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// "query state" (no state override; the encoding is UTF-8)
pub fn query_state(input: &[u32], Ghost(base): Ghost<Option<Url>>, m: &mut ExecMachine) -> (flow: Flow)
    requires
        super::machine::wf(super::machine::ctx_of(input@, base), old(m)@),
        old(m).state is Query,
    ensures
        super::machine::flow_ok(super::machine::ctx_of(input@, base), super::spec::query_state(super::machine::ctx_of(input@, base), old(m)@), final(m)@, flow),
{
    let c = c_at_exec(input, m.pointer);
    match c {
        Some(c) if c != 0x23 => {
            // 3.3
            m.buffer.push(c);
            advance(m, input.len())
        },
        _ => {
            // 2.1
            let set = if is_special_scheme_exec(m.url.scheme.as_slice()) {
                clazel_percent::spec::PercentEncodeSet::SpecialQuery
            } else {
                clazel_percent::spec::PercentEncodeSet::Query
            };
            // 2.2
            let encoded = clazel_percent::encode::utf8_percent_encode(m.buffer.as_slice(), set);
            opt_append_exec(&mut m.url.query, encoded.as_slice());
            // 2.3
            m.buffer = Vec::new();
            assert(m.buffer@ =~= seq![]);
            if c == Some(0x23u32) {
                // 2.4
                m.url.fragment = Some(Vec::new());
                assert(crate::host::record::opt_seq(m.url.fragment) == Some(Seq::<u32>::empty()));
                m.state = State::Fragment;
            }
            advance(m, input.len())
        },
    }
}

/// "fragment state"
pub fn fragment_state(input: &[u32], Ghost(base): Ghost<Option<Url>>, m: &mut ExecMachine) -> (flow: Flow)
    requires
        super::machine::wf(super::machine::ctx_of(input@, base), old(m)@),
        old(m).state is Fragment,
    ensures
        super::machine::flow_ok(super::machine::ctx_of(input@, base), super::spec::fragment_state(super::machine::ctx_of(input@, base), old(m)@), final(m)@, flow),
{
    if let Some(c) = c_at_exec(input, m.pointer) {
        // 1.3
        assert(clazel_encoding::utf8::spec::is_scalar_value(input@[m.pointer as int]));
        let encoded = clazel_percent::encode::utf8_percent_encode_code_point(c, clazel_percent::spec::PercentEncodeSet::Fragment);
        opt_append_exec(&mut m.url.fragment, encoded.as_slice());
    }
    advance(m, input.len())
}

} // verus!
