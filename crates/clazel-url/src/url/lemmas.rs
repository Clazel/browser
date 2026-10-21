//! Facts proven about the URL spec. They are evidence that the
//! transcription is right, not part of what the implementation must meet.
//!
//! - **The parser is total.** [`run`] is a total spec function: Verus
//!   checks its `decreases` measure (`termination.rs`). On top of that,
//!   [`lemma_basic_url_parser_total`] bounds the work: the state machine
//!   decides every input within 12·(n + 1) runs, n being the length of the
//!   input after steps 1 to 3, for every base and every domain parser; and
//!   without a state override no run ends in a valueless "return"
//!   ([`lemma_no_return_without_override`]), so the result is always
//!   failure or step 10's url.
//! - **The URL record's invariants (§4.1).** "A special URL's path is
//!   always a list, i.e., it is never opaque", and a URL's port is "a
//!   16-bit unsigned integer": [`lemma_basic_url_parser_record`], for every
//!   input and domain parser, given a base that satisfies them.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------
// Totality.
// ---------------------------------------------------------------------

/// What holds before every run: pointer is within the input or at its
/// end, and before the host state buffer is no longer than pointer (it
/// holds code points read since it was last emptied).
pub open spec fn run_inv(ctx: Ctx, m: Machine) -> bool {
    0 <= m.pointer <= ctx.input.len() && (super::termination::phase(m.state) >= 1 ==> m.buffer.len() <= m.pointer)
}

/// The number of runs the state machine makes from `m` until it stops.
pub open spec fn runs(ctx: Ctx, m: Machine) -> nat
    decreases super::termination::phase(m.state), super::termination::pointer_measure(ctx.input.len(), m.pointer), super::termination::rank(m.state) via runs_decreases
{
    match state_step(ctx, m) {
        Step::Continue(next) => if next.pointer >= ctx.input.len() {
            1
        } else {
            1 + runs(ctx, Machine { pointer: next.pointer + 1, ..next })
        },
        _ => 1,
    }
}

/// Termination of [`runs`]: the same measure as [`run`].
#[via_fn]
proof fn runs_decreases(ctx: Ctx, m: Machine) {
    super::termination::lemma_state_step_measure(ctx, m);
}

/// A run keeps [`run_inv`]: it moves pointer back by at most 1, except
/// for the scheme state's start over (to −1) and the authority state's
/// rewind (by buffer's length + 1, which [`run_inv`] bounds).
pub open spec fn step_keeps_inv(ctx: Ctx, m: Machine, step: Step) -> bool {
    step matches Step::Continue(next) ==> (next.pointer < ctx.input.len() ==> run_inv(
        ctx,
        Machine { pointer: next.pointer + 1, ..next },
    ))
}

proof fn lemma_inv_scheme_start(ctx: Ctx, m: Machine)
    requires run_inv(ctx, m), m.state is SchemeStart,
    ensures step_keeps_inv(ctx, m, scheme_start_state(ctx, m)),
{
}

proof fn lemma_inv_scheme(ctx: Ctx, m: Machine)
    requires run_inv(ctx, m), m.state is Scheme,
    ensures step_keeps_inv(ctx, m, scheme_state(ctx, m)),
{
}

proof fn lemma_inv_no_scheme(ctx: Ctx, m: Machine)
    requires run_inv(ctx, m), m.state is NoScheme,
    ensures step_keeps_inv(ctx, m, no_scheme_state(ctx, m)),
{
}

proof fn lemma_inv_special_relative_or_authority(ctx: Ctx, m: Machine)
    requires run_inv(ctx, m), m.state is SpecialRelativeOrAuthority,
    ensures step_keeps_inv(ctx, m, special_relative_or_authority_state(ctx, m)),
{
}

proof fn lemma_inv_path_or_authority(ctx: Ctx, m: Machine)
    requires run_inv(ctx, m), m.state is PathOrAuthority,
    ensures step_keeps_inv(ctx, m, path_or_authority_state(ctx, m)),
{
}

proof fn lemma_inv_relative(ctx: Ctx, m: Machine)
    requires run_inv(ctx, m), m.state is Relative,
    ensures step_keeps_inv(ctx, m, relative_state(ctx, m)),
{
}

proof fn lemma_inv_relative_slash(ctx: Ctx, m: Machine)
    requires run_inv(ctx, m), m.state is RelativeSlash,
    ensures step_keeps_inv(ctx, m, relative_slash_state(ctx, m)),
{
}

proof fn lemma_inv_special_authority_slashes(ctx: Ctx, m: Machine)
    requires run_inv(ctx, m), m.state is SpecialAuthoritySlashes,
    ensures step_keeps_inv(ctx, m, special_authority_slashes_state(ctx, m)),
{
}

proof fn lemma_inv_special_authority_ignore_slashes(ctx: Ctx, m: Machine)
    requires run_inv(ctx, m), m.state is SpecialAuthorityIgnoreSlashes,
    ensures step_keeps_inv(ctx, m, special_authority_ignore_slashes_state(ctx, m)),
{
}

proof fn lemma_inv_authority(ctx: Ctx, m: Machine)
    requires run_inv(ctx, m), m.state is Authority,
    ensures step_keeps_inv(ctx, m, authority_state(ctx, m)),
{
}

proof fn lemma_inv_host(ctx: Ctx, m: Machine)
    requires run_inv(ctx, m), m.state is Host || m.state is Hostname,
    ensures step_keeps_inv(ctx, m, host_state(ctx, m)),
{
}

proof fn lemma_inv_port(ctx: Ctx, m: Machine)
    requires run_inv(ctx, m), m.state is Port,
    ensures step_keeps_inv(ctx, m, port_state(ctx, m)),
{
}

proof fn lemma_inv_file(ctx: Ctx, m: Machine)
    requires run_inv(ctx, m), m.state is File,
    ensures step_keeps_inv(ctx, m, file_state(ctx, m)),
{
}

proof fn lemma_inv_file_slash(ctx: Ctx, m: Machine)
    requires run_inv(ctx, m), m.state is FileSlash,
    ensures step_keeps_inv(ctx, m, file_slash_state(ctx, m)),
{
}

proof fn lemma_inv_file_host(ctx: Ctx, m: Machine)
    requires run_inv(ctx, m), m.state is FileHost,
    ensures step_keeps_inv(ctx, m, file_host_state(ctx, m)),
{
}

proof fn lemma_inv_path_start(ctx: Ctx, m: Machine)
    requires run_inv(ctx, m), m.state is PathStart,
    ensures step_keeps_inv(ctx, m, path_start_state(ctx, m)),
{
}

proof fn lemma_inv_path(ctx: Ctx, m: Machine)
    requires run_inv(ctx, m), m.state is Path,
    ensures step_keeps_inv(ctx, m, path_state(ctx, m)),
{
}

proof fn lemma_inv_opaque_path(ctx: Ctx, m: Machine)
    requires run_inv(ctx, m), m.state is OpaquePath,
    ensures step_keeps_inv(ctx, m, opaque_path_state(ctx, m)),
{
}

proof fn lemma_inv_query(ctx: Ctx, m: Machine)
    requires run_inv(ctx, m), m.state is Query,
    ensures step_keeps_inv(ctx, m, query_state(ctx, m)),
{
}

proof fn lemma_inv_fragment(ctx: Ctx, m: Machine)
    requires run_inv(ctx, m), m.state is Fragment,
    ensures step_keeps_inv(ctx, m, fragment_state(ctx, m)),
{
}

/// Every run keeps [`run_inv`].
pub proof fn lemma_step_inv(ctx: Ctx, m: Machine)
    requires
        run_inv(ctx, m),
    ensures
        step_keeps_inv(ctx, m, state_step(ctx, m)),
{
    reveal(state_step);
    match m.state {
        State::SchemeStart => lemma_inv_scheme_start(ctx, m),
        State::Scheme => lemma_inv_scheme(ctx, m),
        State::NoScheme => lemma_inv_no_scheme(ctx, m),
        State::SpecialRelativeOrAuthority => lemma_inv_special_relative_or_authority(ctx, m),
        State::PathOrAuthority => lemma_inv_path_or_authority(ctx, m),
        State::Relative => lemma_inv_relative(ctx, m),
        State::RelativeSlash => lemma_inv_relative_slash(ctx, m),
        State::SpecialAuthoritySlashes => lemma_inv_special_authority_slashes(ctx, m),
        State::SpecialAuthorityIgnoreSlashes => lemma_inv_special_authority_ignore_slashes(ctx, m),
        State::Authority => lemma_inv_authority(ctx, m),
        State::Host => lemma_inv_host(ctx, m),
        State::Hostname => lemma_inv_host(ctx, m),
        State::Port => lemma_inv_port(ctx, m),
        State::File => lemma_inv_file(ctx, m),
        State::FileSlash => lemma_inv_file_slash(ctx, m),
        State::FileHost => lemma_inv_file_host(ctx, m),
        State::PathStart => lemma_inv_path_start(ctx, m),
        State::Path => lemma_inv_path(ctx, m),
        State::OpaquePath => lemma_inv_opaque_path(ctx, m),
        State::Query => lemma_inv_query(ctx, m),
        State::Fragment => lemma_inv_fragment(ctx, m),
    }
}

/// The measure of `termination.rs` as one number: phase, then the code
/// points left, then rank, each below the next one's weight.
pub open spec fn potential(len: nat, m: Machine) -> nat {
    super::termination::phase(m.state) * (4 * (len + 1)) + super::termination::pointer_measure(len, m.pointer) * 4 + super::termination::rank(m.state)
}

/// A rank is below 4.
proof fn lemma_rank_bound(s: State)
    ensures
        super::termination::rank(s) <= 3,
        super::termination::phase(s) <= 2,
{
}

/// The number of runs from a machine is at most its potential plus one.
pub proof fn lemma_runs_bound(ctx: Ctx, m: Machine)
    requires
        run_inv(ctx, m),
    ensures
        runs(ctx, m) <= potential(ctx.input.len(), m) + 1,
    decreases super::termination::phase(m.state), super::termination::pointer_measure(ctx.input.len(), m.pointer), super::termination::rank(m.state),
{
    let len = ctx.input.len();
    super::termination::lemma_state_step_measure(ctx, m);
    lemma_step_inv(ctx, m);
    if let Step::Continue(next) = state_step(ctx, m) {
        if next.pointer < len {
            let n = Machine { pointer: next.pointer + 1, ..next };
            lemma_runs_bound(ctx, n);
            lemma_rank_bound(m.state);
            lemma_rank_bound(n.state);
            let pm = super::termination::pointer_measure(len, m.pointer);
            let pn = super::termination::pointer_measure(len, n.pointer);
            assert(pn <= len);
            assert(potential(len, n) < potential(len, m)) by (nonlinear_arith)
                requires
                    super::termination::phase(n.state) < super::termination::phase(m.state) || (super::termination::phase(n.state) == super::termination::phase(m.state) && (pn < pm || (pn == pm
                        && super::termination::rank(n.state) < super::termination::rank(m.state)))),
                    pn <= len,
                    pm <= len,
                    super::termination::rank(m.state) <= 3,
                    super::termination::rank(n.state) <= 3,
                    potential(len, n) == super::termination::phase(n.state) * (4 * (len + 1)) + pn * 4 + super::termination::rank(n.state),
                    potential(len, m) == super::termination::phase(m.state) * (4 * (len + 1)) + pm * 4 + super::termination::rank(m.state),
            ;
        }
    }
}

/// The machine the basic URL parser starts with (steps 4 to 8), with no
/// url and no state override.
pub open spec fn initial_machine() -> Machine {
    Machine {
        url: new_url(),
        state: State::SchemeStart,
        buffer: seq![],
        at_sign_seen: false,
        inside_brackets: false,
        password_token_seen: false,
        pointer: 0,
    }
}

/// The input after basic URL parser steps 1 to 3 (no url given).
pub open spec fn prepared_input(input: Seq<u32>) -> Seq<u32> {
    remove_ascii_tab_or_newline(strip_trailing_c0_control_or_space(strip_leading_c0_control_or_space(input)))
}

/// The basic URL parser's context, with no state override.
pub open spec fn parser_ctx(input: Seq<u32>, base: Option<Url>, dp: crate::host::spec::DomainParser) -> Ctx {
    Ctx { input: prepared_input(input), base: base, state_override: None, domain_parser: dp }
}

/// Without a state override, no run ends in "return".
pub proof fn lemma_no_return_without_override(ctx: Ctx, m: Machine)
    requires
        ctx.state_override is None,
    ensures
        !(state_step(ctx, m) is Return),
{
    reveal(state_step);
    // One state at a time (the host, port and file host states each hold
    // a host parser call).
    match m.state {
        State::Scheme => assert(!(scheme_state(ctx, m) is Return)),
        State::Host | State::Hostname => assert(!(host_state(ctx, m) is Return)),
        State::Port => assert(!(port_state(ctx, m) is Return)),
        State::FileHost => assert(!(file_host_state(ctx, m) is Return)),
        _ => {},
    }
}

/// The basic URL parser is total: it is [`run`] from the initial machine,
/// which decides the input within 12·(n + 1) runs (n the length of the
/// prepared input), for every base and domain parser.
pub proof fn lemma_basic_url_parser_total(input: Seq<u32>, base: Option<Url>, dp: crate::host::spec::DomainParser)
    ensures
        basic_url_parser(input, base, dp) == run(parser_ctx(input, base, dp), initial_machine()),
        runs(parser_ctx(input, base, dp), initial_machine()) <= 12 * (prepared_input(input).len() + 1),
{
    let ctx = parser_ctx(input, base, dp);
    let m = initial_machine();
    lemma_runs_bound(ctx, m);
    let len = ctx.input.len();
    assert(potential(len, m) <= 8 * (len + 1) + 4 * len + 1) by (nonlinear_arith)
        requires
            potential(len, m) == 2 * (4 * (len + 1)) + super::termination::pointer_measure(len, 0) * 4 + 1,
            super::termination::pointer_measure(len, 0) <= len,
    ;
}

// ---------------------------------------------------------------------
// The URL record's invariants.
// ---------------------------------------------------------------------

/// §4.1: "A special URL's path is always a list, i.e., it is never
/// opaque", and a port is "a 16-bit unsigned integer".
pub open spec fn url_ok(url: Url) -> bool {
    (is_special(url) ==> url.path is List) && (url.port matches Some(p) ==> p <= 0xFFFF)
}

/// What holds of the machine between runs, for [`url_ok`] to hold of the
/// result: the url's port is 16-bit; its path is opaque only in the
/// opaque path, query and fragment states of a non-special url; a
/// relative state runs only against a base with a list path, and the
/// special relative or authority state only against a special base.
pub open spec fn record_inv(ctx: Ctx, m: Machine) -> bool {
    url_ok(base_of(ctx)) && (m.url.port matches Some(p) ==> p <= 0xFFFF) && (m.url.path is Opaque ==> (
    !is_special(m.url) && (m.state is OpaquePath || m.state is Query || m.state is Fragment))) && ((m.state is Relative
        || m.state is RelativeSlash) ==> base_of(ctx).path is List) && (m.state is SpecialRelativeOrAuthority
        ==> is_special(base_of(ctx)))
}

/// A run keeps [`record_inv`], and its url is [`url_ok`] if the run ends
/// the parser.
pub open spec fn step_keeps_record(ctx: Ctx, step: Step) -> bool {
    match step {
        Step::Continue(next) => record_inv(ctx, Machine { pointer: next.pointer + 1, ..next }) && (next.pointer
            >= ctx.input.len() ==> url_ok(next.url)),
        _ => true,
    }
}

proof fn lemma_rec_scheme_start(ctx: Ctx, m: Machine)
    requires record_inv(ctx, m), m.state is SchemeStart, ctx.state_override is None,
    ensures step_keeps_record(ctx, scheme_start_state(ctx, m)),
{
}

proof fn lemma_rec_scheme(ctx: Ctx, m: Machine)
    requires record_inv(ctx, m), m.state is Scheme, ctx.state_override is None,
    ensures step_keeps_record(ctx, scheme_state(ctx, m)),
{
}

proof fn lemma_rec_no_scheme(ctx: Ctx, m: Machine)
    requires record_inv(ctx, m), m.state is NoScheme, ctx.state_override is None,
    ensures step_keeps_record(ctx, no_scheme_state(ctx, m)),
{
}

proof fn lemma_rec_special_relative_or_authority(ctx: Ctx, m: Machine)
    requires record_inv(ctx, m), m.state is SpecialRelativeOrAuthority, ctx.state_override is None,
    ensures step_keeps_record(ctx, special_relative_or_authority_state(ctx, m)),
{
}

proof fn lemma_rec_path_or_authority(ctx: Ctx, m: Machine)
    requires record_inv(ctx, m), m.state is PathOrAuthority, ctx.state_override is None,
    ensures step_keeps_record(ctx, path_or_authority_state(ctx, m)),
{
}

proof fn lemma_rec_relative(ctx: Ctx, m: Machine)
    requires record_inv(ctx, m), m.state is Relative, ctx.state_override is None,
    ensures step_keeps_record(ctx, relative_state(ctx, m)),
{
}

proof fn lemma_rec_relative_slash(ctx: Ctx, m: Machine)
    requires record_inv(ctx, m), m.state is RelativeSlash, ctx.state_override is None,
    ensures step_keeps_record(ctx, relative_slash_state(ctx, m)),
{
}

proof fn lemma_rec_special_authority_slashes(ctx: Ctx, m: Machine)
    requires record_inv(ctx, m), m.state is SpecialAuthoritySlashes, ctx.state_override is None,
    ensures step_keeps_record(ctx, special_authority_slashes_state(ctx, m)),
{
}

proof fn lemma_rec_special_authority_ignore_slashes(ctx: Ctx, m: Machine)
    requires record_inv(ctx, m), m.state is SpecialAuthorityIgnoreSlashes, ctx.state_override is None,
    ensures step_keeps_record(ctx, special_authority_ignore_slashes_state(ctx, m)),
{
}

/// The authority state's userinfo loop changes only the username and
/// password.
proof fn lemma_authority_code_points_fields(buffer: Seq<u32>, i: nat, url: Url, pts: bool)
    ensures
        ({
            let u = authority_code_points(buffer, i, url, pts).0;
            u.scheme == url.scheme && u.host == url.host && u.port == url.port && u.path == url.path && u.query
                == url.query && u.fragment == url.fragment
        }),
    decreases buffer.len() - i,
{
    if i < buffer.len() {
        let cp = buffer[i as int];
        let enc = clazel_percent::spec::utf8_percent_encode_code_point(cp, clazel_percent::spec::PercentEncodeSet::Userinfo);
        lemma_authority_code_points_fields(buffer, i + 1, url, true);
        lemma_authority_code_points_fields(buffer, i + 1, Url { password: url.password + enc, ..url }, pts);
        lemma_authority_code_points_fields(buffer, i + 1, Url { username: url.username + enc, ..url }, pts);
    }
}

proof fn lemma_rec_authority(ctx: Ctx, m: Machine)
    requires record_inv(ctx, m), m.state is Authority, ctx.state_override is None,
    ensures step_keeps_record(ctx, authority_state(ctx, m)),
{
    let buffer = if m.at_sign_seen {
        seq![0x25u32, 0x34, 0x30] + m.buffer
    } else {
        m.buffer
    };
    lemma_authority_code_points_fields(buffer, 0, m.url, m.password_token_seen);
}

proof fn lemma_rec_host(ctx: Ctx, m: Machine)
    requires record_inv(ctx, m), m.state is Host || m.state is Hostname, ctx.state_override is None,
    ensures step_keeps_record(ctx, host_state(ctx, m)),
{
}

proof fn lemma_rec_port(ctx: Ctx, m: Machine)
    requires record_inv(ctx, m), m.state is Port, ctx.state_override is None,
    ensures step_keeps_record(ctx, port_state(ctx, m)),
{
}

proof fn lemma_rec_file(ctx: Ctx, m: Machine)
    requires record_inv(ctx, m), m.state is File, ctx.state_override is None,
    ensures step_keeps_record(ctx, file_state(ctx, m)),
{
    assert(is_special_scheme(file_str()));
}

proof fn lemma_rec_file_slash(ctx: Ctx, m: Machine)
    requires record_inv(ctx, m), m.state is FileSlash, ctx.state_override is None,
    ensures step_keeps_record(ctx, file_slash_state(ctx, m)),
{
}

proof fn lemma_rec_file_host(ctx: Ctx, m: Machine)
    requires record_inv(ctx, m), m.state is FileHost, ctx.state_override is None,
    ensures step_keeps_record(ctx, file_host_state(ctx, m)),
{
}

proof fn lemma_rec_path_start(ctx: Ctx, m: Machine)
    requires record_inv(ctx, m), m.state is PathStart, ctx.state_override is None,
    ensures step_keeps_record(ctx, path_start_state(ctx, m)),
{
}

proof fn lemma_rec_path(ctx: Ctx, m: Machine)
    requires record_inv(ctx, m), m.state is Path, ctx.state_override is None,
    ensures step_keeps_record(ctx, path_state(ctx, m)),
{
}

proof fn lemma_rec_opaque_path(ctx: Ctx, m: Machine)
    requires record_inv(ctx, m), m.state is OpaquePath, ctx.state_override is None,
    ensures step_keeps_record(ctx, opaque_path_state(ctx, m)),
{
}

proof fn lemma_rec_query(ctx: Ctx, m: Machine)
    requires record_inv(ctx, m), m.state is Query, ctx.state_override is None,
    ensures step_keeps_record(ctx, query_state(ctx, m)),
{
}

proof fn lemma_rec_fragment(ctx: Ctx, m: Machine)
    requires record_inv(ctx, m), m.state is Fragment, ctx.state_override is None,
    ensures step_keeps_record(ctx, fragment_state(ctx, m)),
{
}

/// Every run keeps [`record_inv`].
pub proof fn lemma_step_record(ctx: Ctx, m: Machine)
    requires
        record_inv(ctx, m),
        ctx.state_override is None,
    ensures
        step_keeps_record(ctx, state_step(ctx, m)),
{
    reveal(state_step);
    match m.state {
        State::SchemeStart => lemma_rec_scheme_start(ctx, m),
        State::Scheme => lemma_rec_scheme(ctx, m),
        State::NoScheme => lemma_rec_no_scheme(ctx, m),
        State::SpecialRelativeOrAuthority => lemma_rec_special_relative_or_authority(ctx, m),
        State::PathOrAuthority => lemma_rec_path_or_authority(ctx, m),
        State::Relative => lemma_rec_relative(ctx, m),
        State::RelativeSlash => lemma_rec_relative_slash(ctx, m),
        State::SpecialAuthoritySlashes => lemma_rec_special_authority_slashes(ctx, m),
        State::SpecialAuthorityIgnoreSlashes => lemma_rec_special_authority_ignore_slashes(ctx, m),
        State::Authority => lemma_rec_authority(ctx, m),
        State::Host => lemma_rec_host(ctx, m),
        State::Hostname => lemma_rec_host(ctx, m),
        State::Port => lemma_rec_port(ctx, m),
        State::File => lemma_rec_file(ctx, m),
        State::FileSlash => lemma_rec_file_slash(ctx, m),
        State::FileHost => lemma_rec_file_host(ctx, m),
        State::PathStart => lemma_rec_path_start(ctx, m),
        State::Path => lemma_rec_path(ctx, m),
        State::OpaquePath => lemma_rec_opaque_path(ctx, m),
        State::Query => lemma_rec_query(ctx, m),
        State::Fragment => lemma_rec_fragment(ctx, m),
    }
}

/// [`run`] from a machine with [`record_inv`] returns a [`url_ok`] url.
pub proof fn lemma_run_record(ctx: Ctx, m: Machine)
    requires
        record_inv(ctx, m),
        ctx.state_override is None,
    ensures
        run(ctx, m) matches Some(u) ==> url_ok(u),
    decreases super::termination::phase(m.state), super::termination::pointer_measure(ctx.input.len(), m.pointer), super::termination::rank(m.state),
{
    super::termination::lemma_state_step_measure(ctx, m);
    lemma_step_record(ctx, m);
    lemma_no_return_without_override(ctx, m);
    if let Step::Continue(next) = state_step(ctx, m) {
        if next.pointer < ctx.input.len() {
            lemma_run_record(ctx, Machine { pointer: next.pointer + 1, ..next });
        }
    }
}

/// §4.1's invariants hold of every URL the basic URL parser returns: a
/// special URL's path is a list, and the port is 16-bit, for every input
/// and domain parser, if they hold of base.
pub proof fn lemma_basic_url_parser_record(input: Seq<u32>, base: Option<Url>, dp: crate::host::spec::DomainParser)
    requires
        base matches Some(b) ==> url_ok(b),
    ensures
        basic_url_parser(input, base, dp) matches Some(u) ==> url_ok(u),
{
    let ctx = parser_ctx(input, base, dp);
    assert(url_ok(new_url()));
    lemma_run_record(ctx, initial_machine());
}

} // verus!
