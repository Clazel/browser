//! Facts proven about the setters and the basic URL parser with a state
//! override. They are evidence that the transcription is right, not part
//! of what the implementation must meet.
//!
//! - **The parser is total with a state override, too.**
//!   [`lemma_in_place_total`]: with url given and any state override, the
//!   state machine decides every input within 12·(n + 1) runs, n being
//!   the input's length after step 3, as without one (`url/lemmas.rs`).
//!   [`lemma_run_in_place_agrees`]: when the parser returns a url, the url
//!   it leaves in place is that url.
//! - **No setter breaks the URL record's invariants (§4.1)**, "a special
//!   URL's path is always a list" and the port is "a 16-bit unsigned
//!   integer" (`url::lemmas::url_ok`): [`lemma_setters_keep_record`], for
//!   every value and domain parser. No setter changes whether a URL is
//!   special ([`lemma_setters_keep_special`]): the protocol setter
//!   refuses to (scheme state steps 2.1.1 and 2.1.2), and no other setter
//!   changes the scheme.
//! - **Idempotence.** Setting the same value twice gives the URL setting
//!   it once gives, for `username`, `password`, `port`, `pathname`,
//!   `search`, `hash` and `protocol`, for every URL, value and domain
//!   parser ([`lemma_idempotent`]). Not proven for `host` and `hostname`, whose
//!   runs go through the host, port and file host states; nor for `href`,
//!   which is item 1.10's parse-then-serialize question (proven there for
//!   a class of URLs).

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------
// The parser with url and a state override given.
// ---------------------------------------------------------------------

/// The context [`crate::url::spec::basic_url_parse_in_place`] runs in.
pub open spec fn in_place_ctx(input: Seq<u32>, so: crate::url::spec::State, dp: crate::host::spec::DomainParser) -> crate::url::spec::Ctx {
    crate::url::spec::Ctx {
        input: crate::url::spec::remove_ascii_tab_or_newline(input),
        base: None,
        state_override: Some(so),
        domain_parser: dp,
    }
}

/// The machine [`crate::url::spec::basic_url_parse_in_place`] starts with.
pub open spec fn in_place_machine(url: crate::url::spec::Url, so: crate::url::spec::State) -> crate::url::spec::Machine {
    crate::url::spec::Machine {
        url: url,
        state: so,
        buffer: seq![],
        at_sign_seen: false,
        inside_brackets: false,
        password_token_seen: false,
        pointer: 0,
    }
}

/// [`crate::url::spec::basic_url_parse_in_place`] is
/// [`crate::url::spec::run_in_place`] from [`in_place_machine`], which
/// decides the input within 12·(n + 1) runs.
pub proof fn lemma_in_place_total(input: Seq<u32>, url: crate::url::spec::Url, so: crate::url::spec::State, dp: crate::host::spec::DomainParser)
    ensures
        crate::url::spec::basic_url_parse_in_place(input, url, so, dp) == crate::url::spec::run_in_place(in_place_ctx(input, so, dp), in_place_machine(url, so)),
        crate::url::lemmas::runs(in_place_ctx(input, so, dp), in_place_machine(url, so)) <= 12 * (crate::url::spec::remove_ascii_tab_or_newline(input).len() + 1),
{
    let ctx = in_place_ctx(input, so, dp);
    let m = in_place_machine(url, so);
    crate::url::lemmas::lemma_runs_bound(ctx, m);
    let len = ctx.input.len();
    let ph = crate::url::termination::phase(so);
    let rk = crate::url::termination::rank(so);
    assert(ph <= 2 && rk <= 3);
    assert(crate::url::lemmas::potential(len, m) <= 8 * (len + 1) + 4 * len + 3) by (nonlinear_arith)
        requires
            crate::url::lemmas::potential(len, m) == ph * (4 * (len + 1)) + crate::url::termination::pointer_measure(len, 0) * 4 + rk,
            crate::url::termination::pointer_measure(len, 0) <= len,
            ph <= 2,
            rk <= 3,
    ;
}

/// When [`crate::url::spec::run`] returns a url, it is the url left in
/// place.
pub proof fn lemma_run_in_place_agrees(ctx: crate::url::spec::Ctx, m: crate::url::spec::Machine)
    ensures
        crate::url::spec::run(ctx, m) matches Some(u) ==> crate::url::spec::run_in_place(ctx, m) == u,
    decreases crate::url::termination::phase(m.state), crate::url::termination::pointer_measure(ctx.input.len(), m.pointer), crate::url::termination::rank(m.state),
{
    crate::url::termination::lemma_state_step_measure(ctx, m);
    if let crate::url::spec::Step::Continue(next) = crate::url::spec::state_step(ctx, m) {
        if next.pointer < ctx.input.len() {
            lemma_run_in_place_agrees(ctx, crate::url::spec::Machine { pointer: next.pointer + 1, ..next });
        }
    }
}

/// The basic URL parser with url and state override given returns, when
/// it returns a url, the url [`crate::url::spec::basic_url_parse_in_place`]
/// leaves in place.
pub proof fn lemma_in_place_agrees(input: Seq<u32>, url: crate::url::spec::Url, so: crate::url::spec::State, dp: crate::host::spec::DomainParser)
    ensures
        crate::url::spec::basic_url_parser_with(input, None, Some(url), Some(so), dp) matches Some(u) ==> crate::url::spec::basic_url_parse_in_place(input, url, so, dp) == u,
{
    lemma_run_in_place_agrees(in_place_ctx(input, so, dp), in_place_machine(url, so));
}

// ---------------------------------------------------------------------
// The URL record's invariants.
// ---------------------------------------------------------------------

/// The states a setter's run can be in: the state overrides the setters
/// pass, and the states they lead to.
pub open spec fn setter_state(s: crate::url::spec::State) -> bool {
    s is SchemeStart || s is Scheme || s is Host || s is Hostname || s is Port || s is FileHost || s is PathStart
        || s is Path || s is Query || s is Fragment
}

/// What holds between the runs of a setter: a state override is given,
/// the state is a [`setter_state`], url has §4.1's invariants, and
/// whether it is special is `special`.
pub open spec fn override_inv(ctx: crate::url::spec::Ctx, m: crate::url::spec::Machine, special: bool) -> bool {
    ctx.state_override is Some && setter_state(m.state) && crate::url::lemmas::url_ok(m.url)
        && crate::url::spec::is_special(m.url) == special
}

/// What one run keeps: a url it gives back has the invariants and the
/// same specialness, and a run that goes on keeps [`override_inv`].
pub open spec fn step_keeps_override(ctx: crate::url::spec::Ctx, step: crate::url::spec::Step, special: bool) -> bool {
    match step {
        crate::url::spec::Step::Failure => true,
        crate::url::spec::Step::Return(u) => crate::url::lemmas::url_ok(u) && crate::url::spec::is_special(u) == special,
        crate::url::spec::Step::Continue(next) => override_inv(ctx, crate::url::spec::Machine { pointer: next.pointer + 1, ..next }, special)
            && (next.pointer >= ctx.input.len() ==> crate::url::lemmas::url_ok(next.url) && crate::url::spec::is_special(next.url) == special),
    }
}

proof fn lemma_ov_scheme_start(ctx: crate::url::spec::Ctx, m: crate::url::spec::Machine, special: bool)
    requires override_inv(ctx, m, special), m.state is SchemeStart,
    ensures step_keeps_override(ctx, crate::url::spec::scheme_start_state(ctx, m), special),
{
}

proof fn lemma_ov_scheme(ctx: crate::url::spec::Ctx, m: crate::url::spec::Machine, special: bool)
    requires override_inv(ctx, m, special), m.state is Scheme,
    ensures step_keeps_override(ctx, crate::url::spec::scheme_state(ctx, m), special),
{
}

proof fn lemma_ov_host(ctx: crate::url::spec::Ctx, m: crate::url::spec::Machine, special: bool)
    requires override_inv(ctx, m, special), m.state is Host || m.state is Hostname,
    ensures step_keeps_override(ctx, crate::url::spec::host_state(ctx, m), special),
{
}

proof fn lemma_ov_port(ctx: crate::url::spec::Ctx, m: crate::url::spec::Machine, special: bool)
    requires override_inv(ctx, m, special), m.state is Port,
    ensures step_keeps_override(ctx, crate::url::spec::port_state(ctx, m), special),
{
}

proof fn lemma_ov_file_host(ctx: crate::url::spec::Ctx, m: crate::url::spec::Machine, special: bool)
    requires override_inv(ctx, m, special), m.state is FileHost,
    ensures step_keeps_override(ctx, crate::url::spec::file_host_state(ctx, m), special),
{
}

proof fn lemma_ov_path_start(ctx: crate::url::spec::Ctx, m: crate::url::spec::Machine, special: bool)
    requires override_inv(ctx, m, special), m.state is PathStart,
    ensures step_keeps_override(ctx, crate::url::spec::path_start_state(ctx, m), special),
{
}

proof fn lemma_ov_path(ctx: crate::url::spec::Ctx, m: crate::url::spec::Machine, special: bool)
    requires override_inv(ctx, m, special), m.state is Path,
    ensures step_keeps_override(ctx, crate::url::spec::path_state(ctx, m), special),
{
}

proof fn lemma_ov_query(ctx: crate::url::spec::Ctx, m: crate::url::spec::Machine, special: bool)
    requires override_inv(ctx, m, special), m.state is Query,
    ensures step_keeps_override(ctx, crate::url::spec::query_state(ctx, m), special),
{
}

proof fn lemma_ov_fragment(ctx: crate::url::spec::Ctx, m: crate::url::spec::Machine, special: bool)
    requires override_inv(ctx, m, special), m.state is Fragment,
    ensures step_keeps_override(ctx, crate::url::spec::fragment_state(ctx, m), special),
{
}

/// Every run of a setter keeps [`override_inv`].
pub proof fn lemma_step_override(ctx: crate::url::spec::Ctx, m: crate::url::spec::Machine, special: bool)
    requires
        override_inv(ctx, m, special),
    ensures
        step_keeps_override(ctx, crate::url::spec::state_step(ctx, m), special),
{
    reveal(crate::url::spec::state_step);
    match m.state {
        crate::url::spec::State::SchemeStart => lemma_ov_scheme_start(ctx, m, special),
        crate::url::spec::State::Scheme => lemma_ov_scheme(ctx, m, special),
        crate::url::spec::State::Host => lemma_ov_host(ctx, m, special),
        crate::url::spec::State::Hostname => lemma_ov_host(ctx, m, special),
        crate::url::spec::State::Port => lemma_ov_port(ctx, m, special),
        crate::url::spec::State::FileHost => lemma_ov_file_host(ctx, m, special),
        crate::url::spec::State::PathStart => lemma_ov_path_start(ctx, m, special),
        crate::url::spec::State::Path => lemma_ov_path(ctx, m, special),
        crate::url::spec::State::Query => lemma_ov_query(ctx, m, special),
        crate::url::spec::State::Fragment => lemma_ov_fragment(ctx, m, special),
        _ => {},
    }
}

/// The url a setter's run leaves in place has §4.1's invariants and the
/// specialness it started with.
pub proof fn lemma_run_in_place_record(ctx: crate::url::spec::Ctx, m: crate::url::spec::Machine, special: bool)
    requires
        override_inv(ctx, m, special),
    ensures
        crate::url::lemmas::url_ok(crate::url::spec::run_in_place(ctx, m)),
        crate::url::spec::is_special(crate::url::spec::run_in_place(ctx, m)) == special,
    decreases crate::url::termination::phase(m.state), crate::url::termination::pointer_measure(ctx.input.len(), m.pointer), crate::url::termination::rank(m.state),
{
    crate::url::termination::lemma_state_step_measure(ctx, m);
    lemma_step_override(ctx, m, special);
    if let crate::url::spec::Step::Continue(next) = crate::url::spec::state_step(ctx, m) {
        if next.pointer < ctx.input.len() {
            lemma_run_in_place_record(ctx, crate::url::spec::Machine { pointer: next.pointer + 1, ..next }, special);
        }
    }
}

/// [`crate::url::spec::basic_url_parse_in_place`] with a setter's state
/// override keeps §4.1's invariants and specialness.
pub proof fn lemma_in_place_record(input: Seq<u32>, url: crate::url::spec::Url, so: crate::url::spec::State, dp: crate::host::spec::DomainParser)
    requires
        crate::url::lemmas::url_ok(url),
        setter_state(so),
    ensures
        crate::url::lemmas::url_ok(crate::url::spec::basic_url_parse_in_place(input, url, so, dp)),
        crate::url::spec::is_special(crate::url::spec::basic_url_parse_in_place(input, url, so, dp)) == crate::url::spec::is_special(url),
{
    lemma_run_in_place_record(in_place_ctx(input, so, dp), in_place_machine(url, so), crate::url::spec::is_special(url));
}

/// No setter breaks §4.1's invariants: given a URL that has them, every
/// setter gives one that has them, for every value and domain parser.
pub proof fn lemma_setters_keep_record(url: crate::url::spec::Url, value: Seq<u32>, dp: crate::host::spec::DomainParser)
    requires
        crate::url::lemmas::url_ok(url),
    ensures
        href_setter(url, value, dp) matches Some(u) ==> crate::url::lemmas::url_ok(u),
        crate::url::lemmas::url_ok(protocol_setter(url, value, dp)),
        crate::url::lemmas::url_ok(username_setter(url, value)),
        crate::url::lemmas::url_ok(password_setter(url, value)),
        crate::url::lemmas::url_ok(host_setter(url, value, dp)),
        crate::url::lemmas::url_ok(hostname_setter(url, value, dp)),
        crate::url::lemmas::url_ok(port_setter(url, value, dp)),
        crate::url::lemmas::url_ok(pathname_setter(url, value, dp)),
        crate::url::lemmas::url_ok(search_setter(url, value, dp)),
        crate::url::lemmas::url_ok(hash_setter(url, value, dp)),
{
    crate::url::lemmas::lemma_basic_url_parser_record(value, None, dp);
    lemma_in_place_record(value.push(0x3Au32), url, crate::url::spec::State::SchemeStart, dp);
    lemma_in_place_record(value, url, crate::url::spec::State::Host, dp);
    lemma_in_place_record(value, url, crate::url::spec::State::Hostname, dp);
    lemma_in_place_record(value, url, crate::url::spec::State::Port, dp);
    let emptied = crate::url::spec::Url { path: crate::url::spec::UrlPath::List(seq![]), ..url };
    lemma_in_place_record(value, emptied, crate::url::spec::State::PathStart, dp);
    let q = crate::url::spec::Url { query: Some(seq![]), ..url };
    lemma_in_place_record(remove_single_leading(value, 0x3F), q, crate::url::spec::State::Query, dp);
    let f = crate::url::spec::Url { fragment: Some(seq![]), ..url };
    lemma_in_place_record(remove_single_leading(value, 0x23), f, crate::url::spec::State::Fragment, dp);
}

/// No setter but `href` changes whether a URL is special.
pub proof fn lemma_setters_keep_special(url: crate::url::spec::Url, value: Seq<u32>, dp: crate::host::spec::DomainParser)
    requires
        crate::url::lemmas::url_ok(url),
    ensures
        crate::url::spec::is_special(protocol_setter(url, value, dp)) == crate::url::spec::is_special(url),
        crate::url::spec::is_special(username_setter(url, value)) == crate::url::spec::is_special(url),
        crate::url::spec::is_special(password_setter(url, value)) == crate::url::spec::is_special(url),
        crate::url::spec::is_special(host_setter(url, value, dp)) == crate::url::spec::is_special(url),
        crate::url::spec::is_special(hostname_setter(url, value, dp)) == crate::url::spec::is_special(url),
        crate::url::spec::is_special(port_setter(url, value, dp)) == crate::url::spec::is_special(url),
        crate::url::spec::is_special(pathname_setter(url, value, dp)) == crate::url::spec::is_special(url),
        crate::url::spec::is_special(search_setter(url, value, dp)) == crate::url::spec::is_special(url),
        crate::url::spec::is_special(hash_setter(url, value, dp)) == crate::url::spec::is_special(url),
{
    lemma_setters_keep_record(url, value, dp);
    lemma_in_place_record(value.push(0x3Au32), url, crate::url::spec::State::SchemeStart, dp);
    lemma_in_place_record(value, url, crate::url::spec::State::Host, dp);
    lemma_in_place_record(value, url, crate::url::spec::State::Hostname, dp);
    lemma_in_place_record(value, url, crate::url::spec::State::Port, dp);
    let emptied = crate::url::spec::Url { path: crate::url::spec::UrlPath::List(seq![]), ..url };
    lemma_in_place_record(value, emptied, crate::url::spec::State::PathStart, dp);
    let q = crate::url::spec::Url { query: Some(seq![]), ..url };
    lemma_in_place_record(remove_single_leading(value, 0x3F), q, crate::url::spec::State::Query, dp);
    let f = crate::url::spec::Url { fragment: Some(seq![]), ..url };
    lemma_in_place_record(remove_single_leading(value, 0x23), f, crate::url::spec::State::Fragment, dp);
}

// ---------------------------------------------------------------------
// Idempotence.
// ---------------------------------------------------------------------

/// The query state with a state override changes only url's query.
pub proof fn lemma_query_frame(ctx: crate::url::spec::Ctx, m: crate::url::spec::Machine)
    requires
        ctx.state_override is Some,
        m.state is Query,
    ensures
        crate::url::spec::run_in_place(ctx, m) == (crate::url::spec::Url { query: crate::url::spec::run_in_place(ctx, m).query, ..m.url }),
    decreases crate::url::termination::phase(m.state), crate::url::termination::pointer_measure(ctx.input.len(), m.pointer), crate::url::termination::rank(m.state),
{
    reveal(crate::url::spec::state_step);
    crate::url::termination::lemma_state_step_measure(ctx, m);
    if let crate::url::spec::Step::Continue(next) = crate::url::spec::state_step(ctx, m) {
        if next.pointer < ctx.input.len() {
            lemma_query_frame(ctx, crate::url::spec::Machine { pointer: next.pointer + 1, ..next });
        }
    }
}

/// The fragment state changes only url's fragment.
proof fn lemma_fragment_frame(ctx: crate::url::spec::Ctx, m: crate::url::spec::Machine)
    requires
        m.state is Fragment,
    ensures
        crate::url::spec::run_in_place(ctx, m) == (crate::url::spec::Url { fragment: crate::url::spec::run_in_place(ctx, m).fragment, ..m.url }),
    decreases crate::url::termination::phase(m.state), crate::url::termination::pointer_measure(ctx.input.len(), m.pointer), crate::url::termination::rank(m.state),
{
    reveal(crate::url::spec::state_step);
    crate::url::termination::lemma_state_step_measure(ctx, m);
    if let crate::url::spec::Step::Continue(next) = crate::url::spec::state_step(ctx, m) {
        if next.pointer < ctx.input.len() {
            lemma_fragment_frame(ctx, crate::url::spec::Machine { pointer: next.pointer + 1, ..next });
        }
    }
}

/// The path start and path states with a state override change only
/// url's path, and keep it a list.
proof fn lemma_path_frame(ctx: crate::url::spec::Ctx, m: crate::url::spec::Machine)
    requires
        ctx.state_override is Some,
        m.state is PathStart || m.state is Path,
        m.url.path is List,
    ensures
        crate::url::spec::run_in_place(ctx, m) == (crate::url::spec::Url { path: crate::url::spec::run_in_place(ctx, m).path, ..m.url }),
        crate::url::spec::run_in_place(ctx, m).path is List,
    decreases crate::url::termination::phase(m.state), crate::url::termination::pointer_measure(ctx.input.len(), m.pointer), crate::url::termination::rank(m.state),
{
    reveal(crate::url::spec::state_step);
    crate::url::termination::lemma_state_step_measure(ctx, m);
    if let crate::url::spec::Step::Continue(next) = crate::url::spec::state_step(ctx, m) {
        if next.pointer < ctx.input.len() {
            lemma_path_frame(ctx, crate::url::spec::Machine { pointer: next.pointer + 1, ..next });
        }
    }
}

/// The port state with a state override changes only url's port.
proof fn lemma_port_frame(ctx: crate::url::spec::Ctx, m: crate::url::spec::Machine)
    requires
        ctx.state_override is Some,
        m.state is Port,
    ensures
        crate::url::spec::run_in_place(ctx, m) == (crate::url::spec::Url { port: crate::url::spec::run_in_place(ctx, m).port, ..m.url }),
    decreases crate::url::termination::phase(m.state), crate::url::termination::pointer_measure(ctx.input.len(), m.pointer), crate::url::termination::rank(m.state),
{
    reveal(crate::url::spec::state_step);
    crate::url::termination::lemma_state_step_measure(ctx, m);
    if let crate::url::spec::Step::Continue(next) = crate::url::spec::state_step(ctx, m) {
        if next.pointer < ctx.input.len() {
            lemma_port_frame(ctx, crate::url::spec::Machine { pointer: next.pointer + 1, ..next });
        }
    }
}

/// The port state with a state override does not read url's port: from
/// two machines that differ only there, both runs set the same url, or
/// both return failure.
proof fn lemma_port_pair(ctx: crate::url::spec::Ctx, m1: crate::url::spec::Machine, m2: crate::url::spec::Machine)
    requires
        ctx.state_override is Some,
        m1.state is Port,
        m2 == (crate::url::spec::Machine { url: crate::url::spec::Url { port: m2.url.port, ..m1.url }, ..m1 }),
    ensures
        crate::url::spec::run_in_place(ctx, m1) == crate::url::spec::run_in_place(ctx, m2) || (crate::url::spec::run_in_place(ctx, m1) == m1.url
            && crate::url::spec::run_in_place(ctx, m2) == m2.url),
    decreases crate::url::termination::phase(m1.state), crate::url::termination::pointer_measure(ctx.input.len(), m1.pointer), crate::url::termination::rank(m1.state),
{
    reveal(crate::url::spec::state_step);
    crate::url::termination::lemma_state_step_measure(ctx, m1);
    if let crate::url::spec::Step::Continue(n1) = crate::url::spec::state_step(ctx, m1) {
        if let crate::url::spec::Step::Continue(n2) = crate::url::spec::state_step(ctx, m2) {
            if n1.pointer < ctx.input.len() {
                lemma_port_pair(
                    ctx,
                    crate::url::spec::Machine { pointer: n1.pointer + 1, ..n1 },
                    crate::url::spec::Machine { pointer: n2.pointer + 1, ..n2 },
                );
            }
        }
    }
}

/// The buffer the scheme state with a state override holds when it
/// reaches a U+003A (:) from `pointer` with `buffer`, or `None` if it
/// returns failure first (steps 1, 2 and 4).
pub open spec fn scheme_buffer(input: Seq<u32>, pointer: int, buffer: Seq<u32>) -> Option<Seq<u32>>
    decreases input.len() - pointer
{
    if 0 <= pointer < input.len() {
        let c = input[pointer];
        if crate::url::spec::is_ascii_alphanumeric(c) || c == 0x2B || c == 0x2D || c == 0x2E {
            scheme_buffer(input, pointer + 1, buffer.push(crate::url::spec::ascii_lowercase(c)))
        } else if c == 0x3A {
            Some(buffer)
        } else {
            None
        }
    } else {
        None
    }
}

/// What scheme state step 2 with a state override leaves url as, given
/// buffer.
pub open spec fn colon_url(url: crate::url::spec::Url, buffer: Seq<u32>) -> crate::url::spec::Url {
    if (crate::url::spec::is_special_scheme(url.scheme) && !crate::url::spec::is_special_scheme(buffer))
        || (!crate::url::spec::is_special_scheme(url.scheme) && crate::url::spec::is_special_scheme(buffer))
        || ((crate::url::spec::includes_credentials(url) || url.port is Some) && buffer == crate::url::spec::file_str())
        || (url.scheme == crate::url::spec::file_str() && url.host == Some(crate::host::spec::Host::Empty)) {
        url
    } else {
        let u = crate::url::spec::Url { scheme: buffer, ..url };
        if u.port == crate::url::spec::default_port(u.scheme) {
            crate::url::spec::Url { port: None, ..u }
        } else {
            u
        }
    }
}

/// The scheme state with a state override: failure, or step 2 with the
/// buffer [`scheme_buffer`] gives.
pub proof fn lemma_scheme_run(ctx: crate::url::spec::Ctx, m: crate::url::spec::Machine)
    requires
        ctx.state_override is Some,
        m.state is Scheme,
    ensures
        crate::url::spec::run_in_place(ctx, m) == match scheme_buffer(ctx.input, m.pointer, m.buffer) {
            None => m.url,
            Some(b) => colon_url(m.url, b),
        },
    decreases ctx.input.len() - m.pointer
{
    reveal(crate::url::spec::state_step);
    if 0 <= m.pointer < ctx.input.len() {
        let c = ctx.input[m.pointer];
        if crate::url::spec::is_ascii_alphanumeric(c) || c == 0x2B || c == 0x2D || c == 0x2E {
            lemma_scheme_run(ctx, crate::url::spec::Machine { buffer: m.buffer.push(crate::url::spec::ascii_lowercase(c)), pointer: m.pointer + 1, ..m });
        }
    }
}

/// [`colon_url`] is idempotent.
proof fn lemma_colon_url_idempotent(url: crate::url::spec::Url, b: Seq<u32>)
    ensures
        colon_url(colon_url(url, b), b) == colon_url(url, b),
{
}

/// Setting the same value twice gives what setting it once gives, for
/// the `username`, `password`, `port`, `pathname`, `search`, `hash` and
/// `protocol` setters, for every URL, value and domain parser.
pub proof fn lemma_idempotent(url: crate::url::spec::Url, value: Seq<u32>, dp: crate::host::spec::DomainParser)
    ensures
        username_setter(username_setter(url, value), value) == username_setter(url, value),
        password_setter(password_setter(url, value), value) == password_setter(url, value),
        port_setter(port_setter(url, value, dp), value, dp) == port_setter(url, value, dp),
        pathname_setter(pathname_setter(url, value, dp), value, dp) == pathname_setter(url, value, dp),
        search_setter(search_setter(url, value, dp), value, dp) == search_setter(url, value, dp),
        hash_setter(hash_setter(url, value, dp), value, dp) == hash_setter(url, value, dp),
        protocol_setter(protocol_setter(url, value, dp), value, dp) == protocol_setter(url, value, dp),
{
    // port
    if !crate::url::spec::cannot_have_username_password_port(url) && value.len() > 0 {
        let ctx = in_place_ctx(value, crate::url::spec::State::Port, dp);
        let u1 = port_setter(url, value, dp);
        lemma_port_frame(ctx, in_place_machine(url, crate::url::spec::State::Port));
        lemma_port_pair(ctx, in_place_machine(u1, crate::url::spec::State::Port), in_place_machine(url, crate::url::spec::State::Port));
    }
    // pathname
    if !crate::url::spec::has_opaque_path(url) {
        let e = crate::url::spec::Url { path: crate::url::spec::UrlPath::List(seq![]), ..url };
        lemma_path_frame(in_place_ctx(value, crate::url::spec::State::PathStart, dp), in_place_machine(e, crate::url::spec::State::PathStart));
        let u1 = pathname_setter(url, value, dp);
        assert(crate::url::spec::Url { path: crate::url::spec::UrlPath::List(seq![]), ..u1 } == e);
    }
    // search
    if value.len() > 0 {
        let q = crate::url::spec::Url { query: Some(seq![]), ..url };
        let input = remove_single_leading(value, 0x3F);
        lemma_query_frame(in_place_ctx(input, crate::url::spec::State::Query, dp), in_place_machine(q, crate::url::spec::State::Query));
        let u1 = search_setter(url, value, dp);
        assert(crate::url::spec::Url { query: Some(seq![]), ..u1 } == q);
    }
    // hash
    if value.len() > 0 {
        let f = crate::url::spec::Url { fragment: Some(seq![]), ..url };
        let input = remove_single_leading(value, 0x23);
        lemma_fragment_frame(in_place_ctx(input, crate::url::spec::State::Fragment, dp), in_place_machine(f, crate::url::spec::State::Fragment));
        let u1 = hash_setter(url, value, dp);
        assert(crate::url::spec::Url { fragment: Some(seq![]), ..u1 } == f);
    }
    // protocol
    {
        reveal(crate::url::spec::state_step);
        let ctx = in_place_ctx(value.push(0x3Au32), crate::url::spec::State::SchemeStart, dp);
        let u1 = protocol_setter(url, value, dp);
        if ctx.input.len() > 0 && crate::url::spec::is_ascii_alpha(ctx.input[0]) {
            let b0 = seq![crate::url::spec::ascii_lowercase(ctx.input[0])];
            assert(seq![].push(crate::url::spec::ascii_lowercase(ctx.input[0])) == b0);
            let next = |u: crate::url::spec::Url| crate::url::spec::Machine { buffer: b0, state: crate::url::spec::State::Scheme, pointer: 1, ..in_place_machine(u, crate::url::spec::State::SchemeStart) };
            lemma_scheme_run(ctx, next(url));
            lemma_scheme_run(ctx, next(u1));
            if let Some(b) = scheme_buffer(ctx.input, 1, b0) {
                lemma_colon_url_idempotent(url, b);
            }
        }
    }
}

} // verus!
