//! The executable basic URL parser (URL §4.4), proven to meet
//! [`super::contract`]: steps 1 to 3 prepare the input, then a loop runs
//! one proven state function per iteration (step 9), with the loop
//! invariant that the spec's [`run`] from the current machine is the
//! spec's result. The step comments live in [`super::spec`].

use super::machine::{ExecMachine, Flow};
use super::record::{ParsedUrl, new_url_exec};
#[allow(unused_imports)]
use super::spec::*;
use crate::host::record::at32;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Basic URL parser steps 1.3 and 3: remove leading and trailing C0
/// control or space, then all ASCII tab or newline.
fn prepare(input: &[u32]) -> (out: Vec<u32>)
    requires
        clazel_encoding::utf8::spec::all_scalar_values(input@),
    ensures
        out@ == remove_ascii_tab_or_newline(strip_trailing_c0_control_or_space(strip_leading_c0_control_or_space(input@))),
        clazel_encoding::utf8::spec::all_scalar_values(out@),
{
    let n = input.len();
    // Leading C0 control or space.
    let mut i: usize = 0;
    assert(input@.subrange(0, n as int) =~= input@);
    while i < n && at32(input, i) <= 0x20
        invariant
            i <= n,
            n == input.len(),
            strip_leading_c0_control_or_space(input@) == strip_leading_c0_control_or_space(input@.subrange(i as int, n as int)),
        decreases n - i,
    {
        assert(input@.subrange(i as int, n as int).subrange(1, (n - i) as int) =~= input@.subrange(i + 1, n as int));
        // Never saturates: i is below a length.
        i = i.saturating_add(1);
    }
    let ghost lead = input@.subrange(i as int, n as int);
    assert(strip_leading_c0_control_or_space(input@) == lead);
    // Trailing C0 control or space.
    let mut j: usize = n;
    while j > i && at32(input, j.saturating_sub(1)) <= 0x20
        invariant
            i <= j <= n,
            n == input.len(),
            lead == input@.subrange(i as int, n as int),
            strip_trailing_c0_control_or_space(lead) == strip_trailing_c0_control_or_space(input@.subrange(i as int, j as int)),
        decreases j - i,
    {
        assert(input@.subrange(i as int, j as int).drop_last() =~= input@.subrange(i as int, j - 1));
        // Never saturates: j > 0.
        j = j.saturating_sub(1);
    }
    let ghost trimmed = input@.subrange(i as int, j as int);
    assert(strip_trailing_c0_control_or_space(lead) == trimmed);
    // ASCII tab or newline.
    let mut out: Vec<u32> = Vec::new();
    let mut k: usize = i;
    assert(trimmed.subrange(0, 0) =~= seq![]);
    while k < j
        invariant
            i <= k <= j,
            j <= n,
            n == input.len(),
            trimmed == input@.subrange(i as int, j as int),
            clazel_encoding::utf8::spec::all_scalar_values(input@),
            clazel_encoding::utf8::spec::all_scalar_values(out@),
            out@ == remove_ascii_tab_or_newline(trimmed.subrange(0, k - i)),
        decreases j - k,
    {
        let c = at32(input, k);
        assert(trimmed.subrange(0, k + 1 - i).drop_last() =~= trimmed.subrange(0, k - i));
        assert(trimmed.subrange(0, k + 1 - i).last() == c);
        if !(c == 0x09 || c == 0x0A || c == 0x0D) {
            out.push(c);
            assert(clazel_encoding::utf8::spec::is_scalar_value(input@[k as int]));
        }
        // Never saturates: k is below a length.
        k = k.saturating_add(1);
    }
    assert(trimmed.subrange(0, j - i) =~= trimmed);
    out
}

/// One run of the state machine: "switching on state".
fn state_step_exec(input: &[u32], base: Option<&ParsedUrl>, m: &mut ExecMachine) -> (flow: Flow)
    requires
        super::machine::wf(super::machine::ctx_of(input@, super::record::opt_ref_url_view(base)), old(m)@),
    ensures
        super::machine::flow_ok(super::machine::ctx_of(input@, super::record::opt_ref_url_view(base)), state_step(super::machine::ctx_of(input@, super::record::opt_ref_url_view(base)), old(m)@), final(m)@, flow),
{
    proof {
        reveal(state_step);
    }
    match m.state {
        State::SchemeStart => super::states_scheme::scheme_start_state(input, Ghost(super::record::opt_ref_url_view(base)), m),
        State::Scheme => super::states_scheme::scheme_state(input, base, m),
        State::NoScheme => super::states_scheme::no_scheme_state(input, base, m),
        State::SpecialRelativeOrAuthority => super::states_authority::special_relative_or_authority_state(input, Ghost(super::record::opt_ref_url_view(base)), m),
        State::PathOrAuthority => super::states_authority::path_or_authority_state(input, Ghost(super::record::opt_ref_url_view(base)), m),
        State::Relative => super::states_authority::relative_state(input, base, m),
        State::RelativeSlash => super::states_authority::relative_slash_state(input, base, m),
        State::SpecialAuthoritySlashes => super::states_authority::special_authority_slashes_state(input, Ghost(super::record::opt_ref_url_view(base)), m),
        State::SpecialAuthorityIgnoreSlashes => super::states_authority::special_authority_ignore_slashes_state(input, Ghost(super::record::opt_ref_url_view(base)), m),
        State::Authority => super::states_authority::authority_state(input, Ghost(super::record::opt_ref_url_view(base)), m),
        State::Host => super::states_authority::host_state(input, Ghost(super::record::opt_ref_url_view(base)), m),
        State::Hostname => super::states_authority::host_state(input, Ghost(super::record::opt_ref_url_view(base)), m),
        State::Port => super::states_authority::port_state(input, Ghost(super::record::opt_ref_url_view(base)), m),
        State::File => super::states_authority::file_state(input, base, m),
        State::FileSlash => super::states_authority::file_slash_state(input, base, m),
        State::FileHost => super::states_authority::file_host_state(input, Ghost(super::record::opt_ref_url_view(base)), m),
        State::PathStart => super::states_path::path_start_state(input, Ghost(super::record::opt_ref_url_view(base)), m),
        State::Path => super::states_path::path_state(input, Ghost(super::record::opt_ref_url_view(base)), m),
        State::OpaquePath => super::states_path::opaque_path_state(input, Ghost(super::record::opt_ref_url_view(base)), m),
        State::Query => super::states_query::query_state(input, Ghost(super::record::opt_ref_url_view(base)), m),
        State::Fragment => super::states_query::fragment_state(input, Ghost(super::record::opt_ref_url_view(base)), m),
    }
}

/// What a run that [`flow_ok`] relates to `flow` and `after` means for the
/// result of the state machine.
proof fn lemma_run_flow(ctx: Ctx, m: Machine, after: Machine, flow: Flow)
    requires
        super::machine::flow_ok(ctx, state_step(ctx, m), after, flow),
    ensures
        flow is Failure ==> run(ctx, m) is None,
        flow is Stop ==> run(ctx, m) == Some(after.url),
        flow is Next ==> run(ctx, m) == run(ctx, after),
{
}

/// The basic URL parser (URL §4.4) on `input` with `base` (`None` is
/// null), with no url and no state override; `None` is failure.
pub fn basic_url_parser(input: &[u32], base: Option<&ParsedUrl>) -> (output: Option<ParsedUrl>)
    requires
        super::contract::basic_url_parser_requires(input@),
    ensures
        super::contract::basic_url_parser_ensures(input@, super::record::opt_ref_url_view(base), super::record::opt_url_view(output)),
{
    // 1. to 3.
    let prepared = prepare(input);
    let ghost ctx = super::machine::ctx_of(prepared@, super::record::opt_ref_url_view(base));
    let ghost target = super::spec::basic_url_parser(input@, super::record::opt_ref_url_view(base), super::contract::url_domain_parser());
    // 4. to 8.
    let mut m = ExecMachine {
        url: new_url_exec(),
        state: State::SchemeStart,
        buffer: Vec::new(),
        at_sign_seen: false,
        inside_brackets: false,
        password_token_seen: false,
        pointer: 0,
    };
    assert(m.buffer@ =~= seq![]);
    assert(run(ctx, m@) == target);
    // 9.
    loop
        invariant
            super::machine::wf(ctx, m@),
            ctx == super::machine::ctx_of(prepared@, super::record::opt_ref_url_view(base)),
            run(ctx, m@) == target,
            target == super::spec::basic_url_parser(input@, super::record::opt_ref_url_view(base), super::contract::url_domain_parser()),
        decreases super::termination::phase(m@.state), super::termination::pointer_measure(prepared@.len(), m@.pointer), super::termination::rank(m@.state),
    {
        let ghost before = m@;
        proof {
            super::termination::lemma_state_step_measure(ctx, before);
        }
        let flow = state_step_exec(prepared.as_slice(), base, &mut m);
        proof {
            lemma_run_flow(ctx, before, m@, flow);
        }
        match flow {
            Flow::Failure => return None,
            // 10.
            Flow::Stop => return Some(m.url),
            Flow::Next => {},
        }
    }
}

} // verus!

#[cfg(test)]
mod tests {
    use super::basic_url_parser;

    fn scalars(s: &str) -> Vec<u32> {
        s.chars().map(u32::from).collect()
    }

    fn string(v: &[u32]) -> String {
        v.iter().filter_map(|&c| char::from_u32(c)).collect()
    }

    fn href(input: &str, base: Option<&str>) -> Option<String> {
        let base = match base {
            Some(b) => Some(basic_url_parser(&scalars(b), None)?),
            None => None,
        };
        basic_url_parser(&scalars(input), base.as_ref()).map(|u| string(&u.serialize(false)))
    }

    #[test]
    fn standard_examples() {
        // URL §4.1, the components example table.
        assert_eq!(
            href("https://example.com/", None).as_deref(),
            Some("https://example.com/")
        );
        assert_eq!(
            href("https://localhost:8000/search?q=text#hello", None).as_deref(),
            Some("https://localhost:8000/search?q=text#hello")
        );
        assert_eq!(
            href("urn:isbn:9780307476463", None).as_deref(),
            Some("urn:isbn:9780307476463")
        );
        assert_eq!(
            href("file:///ada/Analytical%20Engine/README.md", None).as_deref(),
            Some("file:///ada/Analytical%20Engine/README.md")
        );
        // URL §4.5's note on "/.".
        assert_eq!(
            href("web+demo:/.//not-a-host/", None).as_deref(),
            Some("web+demo:/.//not-a-host/")
        );
        assert_eq!(
            href("web+demo:/path/..//not-a-host/", None).as_deref(),
            Some("web+demo:/.//not-a-host/")
        );
        // Relative references.
        assert_eq!(
            href("../c?d#e", Some("http://h/a/b/")).as_deref(),
            Some("http://h/a/c?d#e")
        );
        assert_eq!(
            href("  HTTP://EXAMPLE.com:80/a\t/./b/../c ", None).as_deref(),
            Some("http://example.com/a/c")
        );
        assert_eq!(href("http://", None), None);
        assert_eq!(
            href("http://user:pa:ss@h/", None).as_deref(),
            Some("http://user:pa%3Ass@h/")
        );
    }
}
