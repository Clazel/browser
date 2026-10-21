//! Why the basic URL parser's state machine terminates ([`super::spec::run`]).
//!
//! Most runs consume c: pointer goes up. The others hand c to the next
//! state ("decrease pointer by 1", undone by step 9's increase), and those
//! hand-offs never form a cycle: [`rank`] goes down along every one. Two
//! runs move pointer further back: the scheme state's "start over" (into
//! the no scheme state) and the authority state's "decrease pointer by
//! buffer's code point length + 1" (into the host state). Neither can
//! happen twice, because no state after them leads back to them: [`phase`]
//! goes down along both and never goes up. So the triple (phase, code
//! points left after pointer, rank) goes down lexicographically on every
//! run that does not stop.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// 2 for the scheme states, 1 for the states up to the authority state,
/// 0 for the host state and every state after it.
pub open spec fn phase(s: State) -> nat {
    match s {
        State::SchemeStart | State::Scheme => 2,
        State::NoScheme | State::SpecialRelativeOrAuthority | State::PathOrAuthority | State::Relative
        | State::RelativeSlash | State::SpecialAuthoritySlashes | State::SpecialAuthorityIgnoreSlashes
        | State::Authority | State::File | State::FileSlash => 1,
        State::Host | State::Hostname | State::Port | State::FileHost | State::PathStart | State::Path
        | State::OpaquePath | State::Query | State::Fragment => 0,
    }
}

/// A rank that every hand-off of c within a phase lowers.
pub open spec fn rank(s: State) -> nat {
    match s {
        State::SchemeStart => 1,
        State::Scheme => 0,
        State::NoScheme => 2,
        State::SpecialRelativeOrAuthority => 2,
        State::SpecialAuthoritySlashes => 2,
        State::SpecialAuthorityIgnoreSlashes => 1,
        State::Authority => 0,
        State::Relative => 1,
        State::RelativeSlash => 0,
        State::PathOrAuthority => 0,
        State::File => 1,
        State::FileSlash => 0,
        State::Host => 3,
        State::Hostname => 3,
        State::Port => 2,
        State::FileHost => 2,
        State::PathStart => 1,
        State::Path => 0,
        State::OpaquePath => 0,
        State::Query => 0,
        State::Fragment => 0,
    }
}

/// The code points left from pointer on (0 once pointer is at or past
/// the end).
pub open spec fn pointer_measure(len: nat, pointer: int) -> nat {
    if pointer < len {
        (len - pointer) as nat
    } else {
        0
    }
}

/// The shape of one run: it lowers the phase, or keeps it and does not
/// move pointer back, or keeps it, moves pointer back by exactly 1 and
/// lowers the rank.
pub open spec fn step_shape(m: Machine, next: Machine) -> bool {
    phase(next.state) < phase(m.state) || (phase(next.state) == phase(m.state) && (next.pointer >= m.pointer || (
    next.pointer == m.pointer - 1 && rank(next.state) < rank(m.state))))
}

/// A run's result has [`step_shape`].
pub open spec fn step_ok(m: Machine, step: Step) -> bool {
    step matches Step::Continue(next) ==> step_shape(m, next)
}

/// The scheme start state has [`step_shape`].
proof fn lemma_shape_scheme_start_state(ctx: Ctx, m: Machine)
    requires
        m.state is SchemeStart,
    ensures
        step_ok(m, scheme_start_state(ctx, m)),
{
}

/// The scheme state has [`step_shape`].
proof fn lemma_shape_scheme_state(ctx: Ctx, m: Machine)
    requires
        m.state is Scheme,
    ensures
        step_ok(m, scheme_state(ctx, m)),
{
}

/// The no scheme state has [`step_shape`].
proof fn lemma_shape_no_scheme_state(ctx: Ctx, m: Machine)
    requires
        m.state is NoScheme,
    ensures
        step_ok(m, no_scheme_state(ctx, m)),
{
}

/// The special relative or authority state has [`step_shape`].
proof fn lemma_shape_special_relative_or_authority_state(ctx: Ctx, m: Machine)
    requires
        m.state is SpecialRelativeOrAuthority,
    ensures
        step_ok(m, special_relative_or_authority_state(ctx, m)),
{
}

/// The path or authority state has [`step_shape`].
proof fn lemma_shape_path_or_authority_state(ctx: Ctx, m: Machine)
    requires
        m.state is PathOrAuthority,
    ensures
        step_ok(m, path_or_authority_state(ctx, m)),
{
}

/// The relative state has [`step_shape`].
proof fn lemma_shape_relative_state(ctx: Ctx, m: Machine)
    requires
        m.state is Relative,
    ensures
        step_ok(m, relative_state(ctx, m)),
{
}

/// The relative slash state has [`step_shape`].
proof fn lemma_shape_relative_slash_state(ctx: Ctx, m: Machine)
    requires
        m.state is RelativeSlash,
    ensures
        step_ok(m, relative_slash_state(ctx, m)),
{
}

/// The special authority slashes state has [`step_shape`].
proof fn lemma_shape_special_authority_slashes_state(ctx: Ctx, m: Machine)
    requires
        m.state is SpecialAuthoritySlashes,
    ensures
        step_ok(m, special_authority_slashes_state(ctx, m)),
{
}

/// The special authority ignore slashes state has [`step_shape`].
proof fn lemma_shape_special_authority_ignore_slashes_state(ctx: Ctx, m: Machine)
    requires
        m.state is SpecialAuthorityIgnoreSlashes,
    ensures
        step_ok(m, special_authority_ignore_slashes_state(ctx, m)),
{
}

/// The authority state has [`step_shape`].
proof fn lemma_shape_authority_state(ctx: Ctx, m: Machine)
    requires
        m.state is Authority,
    ensures
        step_ok(m, authority_state(ctx, m)),
{
}

/// The host state has [`step_shape`].
proof fn lemma_shape_host_state(ctx: Ctx, m: Machine)
    requires
        (m.state is Host || m.state is Hostname),
    ensures
        step_ok(m, host_state(ctx, m)),
{
}

/// The port state has [`step_shape`].
proof fn lemma_shape_port_state(ctx: Ctx, m: Machine)
    requires
        m.state is Port,
    ensures
        step_ok(m, port_state(ctx, m)),
{
}

/// The file state has [`step_shape`].
proof fn lemma_shape_file_state(ctx: Ctx, m: Machine)
    requires
        m.state is File,
    ensures
        step_ok(m, file_state(ctx, m)),
{
}

/// The file slash state has [`step_shape`].
proof fn lemma_shape_file_slash_state(ctx: Ctx, m: Machine)
    requires
        m.state is FileSlash,
    ensures
        step_ok(m, file_slash_state(ctx, m)),
{
}

/// The file host state has [`step_shape`].
proof fn lemma_shape_file_host_state(ctx: Ctx, m: Machine)
    requires
        m.state is FileHost,
    ensures
        step_ok(m, file_host_state(ctx, m)),
{
}

/// The path start state has [`step_shape`].
proof fn lemma_shape_path_start_state(ctx: Ctx, m: Machine)
    requires
        m.state is PathStart,
    ensures
        step_ok(m, path_start_state(ctx, m)),
{
}

/// The path state has [`step_shape`].
proof fn lemma_shape_path_state(ctx: Ctx, m: Machine)
    requires
        m.state is Path,
    ensures
        step_ok(m, path_state(ctx, m)),
{
}

/// The opaque path state has [`step_shape`].
proof fn lemma_shape_opaque_path_state(ctx: Ctx, m: Machine)
    requires
        m.state is OpaquePath,
    ensures
        step_ok(m, opaque_path_state(ctx, m)),
{
}

/// The query state has [`step_shape`].
proof fn lemma_shape_query_state(ctx: Ctx, m: Machine)
    requires
        m.state is Query,
    ensures
        step_ok(m, query_state(ctx, m)),
{
}

/// The fragment state has [`step_shape`].
proof fn lemma_shape_fragment_state(ctx: Ctx, m: Machine)
    requires
        m.state is Fragment,
    ensures
        step_ok(m, fragment_state(ctx, m)),
{
}

/// Every run has [`step_shape`].
pub proof fn lemma_state_step_shape(ctx: Ctx, m: Machine)
    ensures
        step_ok(m, state_step(ctx, m)),
{
    reveal(state_step);
    match m.state {
        State::SchemeStart => lemma_shape_scheme_start_state(ctx, m),
        State::Scheme => lemma_shape_scheme_state(ctx, m),
        State::NoScheme => lemma_shape_no_scheme_state(ctx, m),
        State::SpecialRelativeOrAuthority => lemma_shape_special_relative_or_authority_state(ctx, m),
        State::PathOrAuthority => lemma_shape_path_or_authority_state(ctx, m),
        State::Relative => lemma_shape_relative_state(ctx, m),
        State::RelativeSlash => lemma_shape_relative_slash_state(ctx, m),
        State::SpecialAuthoritySlashes => lemma_shape_special_authority_slashes_state(ctx, m),
        State::SpecialAuthorityIgnoreSlashes => lemma_shape_special_authority_ignore_slashes_state(ctx, m),
        State::Authority => lemma_shape_authority_state(ctx, m),
        State::Host => lemma_shape_host_state(ctx, m),
        State::Hostname => lemma_shape_host_state(ctx, m),
        State::Port => lemma_shape_port_state(ctx, m),
        State::File => lemma_shape_file_state(ctx, m),
        State::FileSlash => lemma_shape_file_slash_state(ctx, m),
        State::FileHost => lemma_shape_file_host_state(ctx, m),
        State::PathStart => lemma_shape_path_start_state(ctx, m),
        State::Path => lemma_shape_path_state(ctx, m),
        State::OpaquePath => lemma_shape_opaque_path_state(ctx, m),
        State::Query => lemma_shape_query_state(ctx, m),
        State::Fragment => lemma_shape_fragment_state(ctx, m),
    }
}

/// Every run that does not stop lowers (phase, pointer_measure, rank)
/// lexicographically.
pub proof fn lemma_state_step_measure(ctx: Ctx, m: Machine)
    ensures
        state_step(ctx, m) matches Step::Continue(next) ==> (next.pointer < ctx.input.len() ==> ({
            let n = Machine { pointer: next.pointer + 1, ..next };
            phase(n.state) < phase(m.state) || (phase(n.state) == phase(m.state) && (pointer_measure(
                ctx.input.len(),
                n.pointer,
            ) < pointer_measure(ctx.input.len(), m.pointer) || (pointer_measure(ctx.input.len(), n.pointer)
                == pointer_measure(ctx.input.len(), m.pointer) && rank(n.state) < rank(m.state))))
        })),
{
    lemma_state_step_shape(ctx, m);
}

} // verus!
