//! Serialize then parse (URL Goals: "a non-failure result of a
//! parse-then-serialize operation will not change with any further
//! parse-then-serialize operations applied to it"), proven for a class of
//! URL records.
//!
//! [`lemma_serialize_parse`]: for every URL in [`round_trip_url`] and every
//! domain parser, the basic URL parser on its serialization (with no base)
//! returns exactly that URL. [`lemma_idempotent`] is the Goals sentence as
//! a corollary: if parsing any input gives a URL in the class, a further
//! parse-then-serialize does not change its serialization.
//!
//! **The class** is the URLs whose scheme is not special, with an opaque
//! host, and whose every component is already in the form the parser
//! writes it in: a scheme of an ASCII lower alpha then lower alphas,
//! digits, "+", "-", "."; an empty username and password; a non-empty
//! opaque host of ASCII code points that are neither forbidden host code
//! points nor in the C0 control percent-encode set; any port (below
//! 2^16); a path that is a list of segments of ASCII code points outside
//! the path percent-encode set, without "/", none a single-dot or
//! double-dot segment; a query of ASCII code points outside the query
//! percent-encode set; a fragment outside the fragment percent-encode set.
//! Percent-encoded bytes ("%41") are allowed everywhere: "%" is in no set.
//!
//! **Not covered** (a gap, recorded in docs/phases/phase-1.md): special
//! schemes (their hosts go through the domain parser, which is a parameter
//! here), credentials, an empty or null host, opaque paths, and "file"
//! URLs. `tests/conformance_url.rs` checks the property on every WPT row
//! and 200,000 random inputs, through the proven parser.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// A scheme of the class: an ASCII lower alpha, then ASCII lower alphas,
/// digits, "+", "-" and ".".
pub open spec fn scheme_ok(s: Seq<u32>) -> bool {
    &&& s.len() > 0 && 0x61 <= s[0] <= 0x7A
    &&& forall|k: int| 0 <= k < s.len() ==> ((0x61 <= #[trigger] s[k] <= 0x7A) || crate::host::spec::is_ascii_digit(s[k])
        || s[k] == 0x2B || s[k] == 0x2D || s[k] == 0x2E)
}

/// An opaque host of the class: non-empty, ASCII, no forbidden host code
/// point, nothing in the C0 control percent-encode set.
pub open spec fn opaque_host_ok(h: Seq<u32>) -> bool {
    h.len() > 0 && forall|k: int| 0 <= k < h.len() ==> (super::runs::outside(
        #[trigger] h[k],
        clazel_percent::spec::PercentEncodeSet::C0Control,
    ) && !crate::host::spec::is_forbidden_host_code_point(h[k]))
}

/// A path segment of the class.
pub open spec fn round_trip_segment(s: Seq<u32>) -> bool {
    super::runs::path_segment_ok(s) && !is_single_dot_segment(s) && !is_double_dot_segment(s)
}

/// The URLs this module proves the round trip for (see the module
/// comment).
pub open spec fn round_trip_url(u: Url) -> bool {
    &&& scheme_ok(u.scheme) && !is_special_scheme(u.scheme)
    &&& u.username.len() == 0 && u.password.len() == 0
    &&& u.host matches Some(crate::host::spec::Host::Opaque(h)) && opaque_host_ok(h)
    &&& u.port matches Some(p) ==> p <= 0xFFFF
    &&& u.path matches UrlPath::List(segs) && forall|i: int| 0 <= i < segs.len() ==> round_trip_segment(#[trigger] segs[i])
    &&& u.query matches Some(q) ==> super::runs::outside_all(q, clazel_percent::spec::PercentEncodeSet::Query)
    &&& u.fragment matches Some(f) ==> super::runs::outside_all(f, clazel_percent::spec::PercentEncodeSet::Fragment)
}

// ---------------------------------------------------------------------
// The serialization.
// ---------------------------------------------------------------------

/// ":" and the port, serialized, if there is one.
pub open spec fn port_part(port: Option<nat>) -> Seq<u32> {
    match port {
        Some(p) => seq![0x3Au32] + crate::host::spec::serialize_integer(p),
        None => seq![],
    }
}

/// The serialization's authority-and-path head: scheme "://" host
/// [":" port] path.
pub open spec fn head(u: Url) -> Seq<u32> {
    let h = u.host->Some_0->Opaque_0;
    let segs = u.path->List_0;
    u.scheme + seq![0x3Au32, 0x2F, 0x2F] + h + port_part(u.port) + serialize_segments(segs)
}

/// The URL serializer on a URL of the class.
proof fn lemma_serialization(u: Url)
    requires
        round_trip_url(u),
    ensures
        url_serializer(u, false) == super::independent::with_fragment(super::independent::with_query(head(u), u.query), u.fragment),
{
    let h = u.host->Some_0->Opaque_0;
    assert(crate::host::spec::host_serializer(crate::host::spec::Host::Opaque(h)) == h);
    assert(u.scheme + seq![0x3Au32] + seq![0x2Fu32, 0x2F] + h =~= u.scheme + seq![0x3Au32, 0x2F, 0x2F] + h);
    match u.port {
        Some(p) => {
            assert(u.scheme + seq![0x3Au32, 0x2F, 0x2F] + h + seq![0x3Au32] + crate::host::spec::serialize_integer(p)
                =~= u.scheme + seq![0x3Au32, 0x2F, 0x2F] + h + port_part(u.port));
        },
        None => {
            assert(u.scheme + seq![0x3Au32, 0x2F, 0x2F] + h =~= u.scheme + seq![0x3Au32, 0x2F, 0x2F] + h + port_part(
                u.port,
            ));
        },
    }
}

// ---------------------------------------------------------------------
// Integers.
// ---------------------------------------------------------------------

/// A serialized integer is ASCII digits, and reads back as itself.
proof fn lemma_serialize_integer(n: nat)
    ensures
        crate::host::spec::serialize_integer(n).len() > 0,
        super::machine::all_ascii_digits(crate::host::spec::serialize_integer(n)),
        decimal_value(crate::host::spec::serialize_integer(n)) == n,
    decreases n,
{
    let s = crate::host::spec::serialize_integer(n);
    if n >= 10 {
        lemma_serialize_integer(n / 10);
        let t = crate::host::spec::serialize_integer(n / 10);
        assert(s == t + seq![(0x30 + n % 10) as u32]);
        assert(s.drop_last() =~= t);
        assert forall|k: int| 0 <= k < s.len() implies crate::host::spec::is_ascii_digit(#[trigger] s[k]) by {
            if k < t.len() {
                assert(s[k] == t[k]);
            }
        }
        assert(s.last() == (0x30 + n % 10) as u32);
        assert((s.last() - 0x30) as nat == n % 10);
        assert((n / 10) * 10 + n % 10 == n) by (nonlinear_arith);
        assert(decimal_value(s) == decimal_value(s.drop_last()) * 10 + (s.last() - 0x30) as nat);
    } else {
        assert(s.drop_last() =~= Seq::<u32>::empty());
        assert(s.last() == (0x30 + n) as u32);
        assert(decimal_value(Seq::<u32>::empty()) == 0);
        assert(decimal_value(s) == decimal_value(s.drop_last()) * 10 + (s.last() - 0x30) as nat);
    }
}

// ---------------------------------------------------------------------
// Strings of the class.
// ---------------------------------------------------------------------

/// A path serialization is "/" and the segments joined with "/".
proof fn lemma_serialize_join(l: Seq<Seq<u32>>)
    requires
        l.len() > 0,
    ensures
        serialize_segments(l) == seq![0x2Fu32] + super::runs::join(l),
    decreases l.len(),
{
    super::independent::lemma_serialize_front(l);
    let rest = l.subrange(1, l.len() as int);
    if l.len() == 1 {
        assert(rest =~= Seq::<Seq<u32>>::empty());
        assert(seq![0x2Fu32] + l[0] + Seq::<u32>::empty() =~= seq![0x2Fu32] + l[0]);
    } else {
        lemma_serialize_join(rest);
        assert(super::runs::join(l) == l[0] + seq![0x2Fu32] + super::runs::join(rest));
        assert(seq![0x2Fu32] + l[0] + (seq![0x2Fu32] + super::runs::join(rest)) =~= seq![0x2Fu32] + (l[0] + seq![0x2Fu32]
            + super::runs::join(rest)));
    }
}

/// The path state appends segments that are not dot segments as they
/// are.
proof fn lemma_path_model_plain(l: Seq<Seq<u32>>, segs: Seq<Seq<u32>>)
    requires
        forall|i: int| 0 <= i < segs.len() ==> round_trip_segment(#[trigger] segs[i]),
    ensures
        super::runs::path_model(l, segs) == l + segs,
    decreases segs.len(),
{
    if segs.len() == 0 {
        assert(l + segs =~= l);
    } else if segs.len() == 1 {
        assert(round_trip_segment(segs[0]));
        assert(l.push(segs[0]) =~= l + segs);
    } else {
        let rest = segs.subrange(1, segs.len() as int);
        assert(round_trip_segment(segs[0]));
        assert forall|i: int| 0 <= i < rest.len() implies round_trip_segment(#[trigger] rest[i]) by {
            assert(rest[i] == segs[i + 1]);
        }
        lemma_path_model_plain(l.push(segs[0]), rest);
        assert(l.push(segs[0]) + rest =~= l + segs);
    }
}

/// `join(segs)` holds no "?", "#", ":" or "@", and no code point at or
/// below U+0020 SPACE.
proof fn lemma_join_plain(segs: Seq<Seq<u32>>)
    requires
        forall|i: int| 0 <= i < segs.len() ==> super::runs::path_segment_ok(#[trigger] segs[i]),
    ensures
        forall|k: int| 0 <= k < super::runs::join(segs).len() ==> (super::runs::outside(
            #[trigger] super::runs::join(segs)[k],
            clazel_percent::spec::PercentEncodeSet::Path,
        ) || super::runs::join(segs)[k] == 0x2F),
    decreases segs.len(),
{
    if segs.len() > 1 {
        let rest = segs.subrange(1, segs.len() as int);
        assert forall|i: int| 0 <= i < rest.len() implies super::runs::path_segment_ok(#[trigger] rest[i]) by {
            assert(rest[i] == segs[i + 1]);
        }
        lemma_join_plain(rest);
        let j = super::runs::join(segs);
        assert(j == segs[0] + seq![0x2Fu32] + super::runs::join(rest));
        assert(super::runs::path_segment_ok(segs[0]));
        assert forall|k: int| 0 <= k < j.len() implies (super::runs::outside(
            #[trigger] j[k],
            clazel_percent::spec::PercentEncodeSet::Path,
        ) || j[k] == 0x2F) by {
            if k < segs[0].len() {
                assert(j[k] == segs[0][k]);
            } else if k > segs[0].len() {
                assert(j[k] == super::runs::join(rest)[k - segs[0].len() - 1]);
            }
        }
    } else if segs.len() == 1 {
        assert(super::runs::path_segment_ok(segs[0]));
    }
}

/// The host parser on an opaque host of the class, with isOpaque true,
/// gives it back, for every domain parser.
proof fn lemma_opaque_host(h: Seq<u32>, dp: crate::host::spec::DomainParser)
    requires
        opaque_host_ok(h),
    ensures
        crate::host::spec::host_parser(h, true, dp) == Some(crate::host::spec::Host::Opaque(h)),
{
    assert(!crate::host::spec::contains_forbidden_host_code_point_from(h, 0)) by {
        lemma_no_forbidden_from(h, 0);
    }
    super::runs::lemma_encode_identity(h, clazel_percent::spec::PercentEncodeSet::C0Control);
    assert(!crate::host::spec::is_forbidden_host_code_point(h[0]));
}

/// No forbidden host code point from `i` on.
proof fn lemma_no_forbidden_from(h: Seq<u32>, i: nat)
    requires
        opaque_host_ok(h),
        i <= h.len(),
    ensures
        !crate::host::spec::contains_forbidden_host_code_point_from(h, i),
    decreases h.len() - i,
{
    if i < h.len() {
        lemma_no_forbidden_from(h, i + 1);
    }
}

// ---------------------------------------------------------------------
// Runs of the parser over a serialization of the class.
// ---------------------------------------------------------------------

/// The path or authority state at "/" goes to the authority state at the
/// next code point.
proof fn lemma_path_or_authority_step(ctx: Ctx, m: Machine)
    requires
        m.state is PathOrAuthority,
        0 <= m.pointer < ctx.input.len(),
        ctx.input[m.pointer] == 0x2F,
    ensures
        run(ctx, m) == run(ctx, Machine { state: State::Authority, pointer: m.pointer + 1, ..m }),
{
    reveal(state_step);
}

/// The scheme state over the rest of a scheme of the class and its ":",
/// followed by "//", goes to the authority state after the "//".
proof fn lemma_scheme_run(ctx: Ctx, m: Machine, n: int)
    requires
        m.state is Scheme,
        ctx.state_override is None,
        ctx.base is None,
        1 <= m.pointer <= n,
        n + 2 < ctx.input.len(),
        scheme_ok(ctx.input.subrange(0, n)),
        !is_special_scheme(ctx.input.subrange(0, n)),
        m.buffer == ctx.input.subrange(0, m.pointer),
        ctx.input[n] == 0x3A && ctx.input[n + 1] == 0x2F && ctx.input[n + 2] == 0x2F,
    ensures
        run(ctx, m) == run(
            ctx,
            Machine {
                url: Url { scheme: ctx.input.subrange(0, n), ..m.url },
                buffer: seq![],
                state: State::Authority,
                pointer: n + 3,
                ..m
            },
        ),
    decreases n - m.pointer,
{
    reveal(state_step);
    let p = m.pointer;
    let scheme = ctx.input.subrange(0, n);
    if p < n {
        let c = ctx.input[p];
        assert(c == scheme[p]);
        assert(ascii_lowercase(c) == c);
        assert(m.buffer.push(c) =~= ctx.input.subrange(0, p + 1));
        lemma_scheme_run(ctx, Machine { buffer: m.buffer.push(ascii_lowercase(c)), pointer: p + 1, ..m }, n);
    } else {
        assert(scheme != file_str()) by {
            assert(is_special_scheme(file_str()));
        }
        let m3 = Machine {
            url: Url { scheme: scheme, ..m.url },
            buffer: seq![],
            state: State::PathOrAuthority,
            pointer: n + 2,
            ..m
        };
        assert(run(ctx, m) == run(ctx, m3));
        lemma_path_or_authority_step(ctx, m3);
    }
}

/// The authority state over an authority with no "@", up to its end `t`
/// ("/", "?", "#" or the end), goes back to its start `a` in the host
/// state.
proof fn lemma_authority_run(ctx: Ctx, m: Machine, a: int, t: int)
    requires
        m.state is Authority,
        !is_special(m.url),
        !m.at_sign_seen,
        1 <= a <= m.pointer <= t <= ctx.input.len(),
        m.buffer == ctx.input.subrange(a, m.pointer),
        forall|j: int| a <= j < t ==> (#[trigger] ctx.input[j] != 0x40 && !super::independent::is_slash_question_hash(
            ctx.input[j],
        )),
        t == ctx.input.len() || super::independent::is_slash_question_hash(ctx.input[t]),
    ensures
        run(ctx, m) == run(ctx, Machine { buffer: seq![], state: State::Host, pointer: a, ..m }),
    decreases t - m.pointer,
{
    reveal(state_step);
    let p = m.pointer;
    if p < t {
        let c = ctx.input[p];
        assert(m.buffer.push(c) =~= ctx.input.subrange(a, p + 1));
        lemma_authority_run(ctx, Machine { buffer: m.buffer.push(c), pointer: p + 1, ..m }, a, t);
    }
}

/// The host state over an opaque host of the class, up to `k` (":" for a
/// port, or the authority's end): the host is set.
proof fn lemma_host_run(ctx: Ctx, m: Machine, a: int, k: int)
    requires
        m.state is Host,
        !is_special(m.url),
        ctx.state_override is None,
        !m.inside_brackets,
        0 <= a <= m.pointer <= k <= ctx.input.len(),
        a < k,
        m.buffer == ctx.input.subrange(a, m.pointer),
        opaque_host_ok(ctx.input.subrange(a, k)),
        k == ctx.input.len() || ctx.input[k] == 0x3A || super::independent::is_slash_question_hash(ctx.input[k]),
    ensures
        ({
            let url = Url { host: Some(crate::host::spec::Host::Opaque(ctx.input.subrange(a, k))), ..m.url };
            &&& (k < ctx.input.len() && ctx.input[k] == 0x3A) ==> run(ctx, m) == run(
                ctx,
                Machine { url: url, buffer: seq![], state: State::Port, pointer: k + 1, ..m },
            )
            &&& !(k < ctx.input.len() && ctx.input[k] == 0x3A) ==> run(ctx, m) == run(
                ctx,
                Machine { url: url, buffer: seq![], state: State::PathStart, pointer: k, ..m },
            )
        }),
    decreases k - m.pointer,
{
    reveal(state_step);
    let p = m.pointer;
    let h = ctx.input.subrange(a, k);
    if p < k {
        let c = ctx.input[p];
        assert(c == h[p - a]);
        assert(!crate::host::spec::is_forbidden_host_code_point(c));
        assert(m.buffer.push(c) =~= ctx.input.subrange(a, p + 1));
        lemma_host_run(ctx, Machine { buffer: m.buffer.push(c), pointer: p + 1, ..m }, a, k);
    } else {
        assert(m.buffer =~= h);
        lemma_opaque_host(h, ctx.domain_parser);
    }
}

/// The port state over a serialized port up to `t` (the authority's
/// end): the port is set (a non-special scheme has no default port).
proof fn lemma_port_run(ctx: Ctx, m: Machine, port: nat, t: int)
    requires
        m.state is Port,
        !is_special(m.url),
        ctx.state_override is None,
        port <= 0xFFFF,
        0 <= m.pointer <= t <= ctx.input.len(),
        m.buffer + ctx.input.subrange(m.pointer, t) == crate::host::spec::serialize_integer(port),
        super::machine::all_ascii_digits(ctx.input.subrange(m.pointer, t)),
        t == ctx.input.len() || super::independent::is_slash_question_hash(ctx.input[t]),
    ensures
        run(ctx, m) == run(
            ctx,
            Machine { url: Url { port: Some(port), ..m.url }, buffer: seq![], state: State::PathStart, pointer: t, ..m },
        ),
    decreases t - m.pointer,
{
    reveal(state_step);
    let p = m.pointer;
    if p < t {
        let c = ctx.input[p];
        assert(ctx.input.subrange(p, t)[0] == c);
        assert(m.buffer.push(c) + ctx.input.subrange(p + 1, t) =~= m.buffer + ctx.input.subrange(p, t));
        assert(super::machine::all_ascii_digits(ctx.input.subrange(p + 1, t))) by {
            assert forall|j: int| 0 <= j < ctx.input.subrange(p + 1, t).len() implies crate::host::spec::is_ascii_digit(
                #[trigger] ctx.input.subrange(p + 1, t)[j],
            ) by {
                assert(ctx.input.subrange(p + 1, t)[j] == ctx.input.subrange(p, t)[j + 1]);
            }
        }
        lemma_port_run(ctx, Machine { buffer: m.buffer.push(c), pointer: p + 1, ..m }, port, t);
    } else {
        assert(m.buffer =~= crate::host::spec::serialize_integer(port));
        lemma_serialize_integer(port);
        assert(default_port(m.url.scheme) is None);
    }
}

/// The path start state of a non-special URL.
proof fn lemma_path_start_run(ctx: Ctx, m: Machine)
    requires
        m.state is PathStart,
        !is_special(m.url),
        ctx.state_override is None,
        0 <= m.pointer <= ctx.input.len(),
    ensures
        ({
            let p = m.pointer;
            let len = ctx.input.len() as int;
            &&& p == len ==> run(ctx, m) == Some(m.url)
            &&& (p < len && ctx.input[p] == 0x2F) ==> run(ctx, m) == run(ctx, Machine { state: State::Path, pointer: p + 1, ..m })
            &&& (p < len && ctx.input[p] == 0x3F) ==> run(ctx, m) == run(
                ctx,
                Machine { url: Url { query: Some(seq![]), ..m.url }, state: State::Query, pointer: p + 1, ..m },
            )
            &&& (p < len && ctx.input[p] == 0x23) ==> run(ctx, m) == run(
                ctx,
                Machine { url: Url { fragment: Some(seq![]), ..m.url }, state: State::Fragment, pointer: p + 1, ..m },
            )
        }),
{
    reveal(state_step);
}

/// The query and fragment after the path, from `e` (where the path state
/// or path start state left them) to the end.
proof fn lemma_round_trip_tail(ctx: Ctx, url: Url, m: Machine, e: int, query: Option<Seq<u32>>, fragment: Option<Seq<u32>>)
    requires
        ctx.state_override is None,
        !is_special(url),
        url.query is None && url.fragment is None,
        0 <= e <= ctx.input.len(),
        ctx.input == super::independent::with_fragment(super::independent::with_query(ctx.input.subrange(0, e), query), fragment),
        query matches Some(q) ==> super::runs::outside_all(q, clazel_percent::spec::PercentEncodeSet::Query),
        fragment matches Some(f) ==> super::runs::outside_all(f, clazel_percent::spec::PercentEncodeSet::Fragment),
    ensures
        e == ctx.input.len() ==> query is None && fragment is None,
        (e < ctx.input.len() && ctx.input[e] == 0x3F) ==> run(
            ctx,
            Machine { url: Url { query: Some(seq![]), ..url }, buffer: seq![], state: State::Query, pointer: e + 1, ..m },
        ) == Some(Url { query: query, fragment: fragment, ..url }),
        (e < ctx.input.len() && ctx.input[e] == 0x23) ==> run(
            ctx,
            Machine { url: Url { fragment: Some(seq![]), ..url }, buffer: seq![], state: State::Fragment, pointer: e + 1, ..m },
        ) == Some(Url { query: query, fragment: fragment, ..url }),
        e < ctx.input.len() ==> (ctx.input[e] == 0x3F || ctx.input[e] == 0x23),
{
    let input = ctx.input;
    let len = input.len() as int;
    let head = input.subrange(0, e);
    if e < len {
        super::independent::lemma_tail_delimiter(input, e, query, fragment);
    }
    match (query, fragment) {
        (None, None) => {
            assert(input =~= head);
        },
        (Some(q), None) => {
            assert(input =~= head + seq![0x3Fu32] + q);
            assert(input.len() == e + 1 + q.len());
            let mq = Machine { url: Url { query: Some(seq![]), ..url }, buffer: seq![], state: State::Query, pointer: e + 1, ..m };
            assert(super::runs::outside_between(input, e + 1, len, super::runs::query_set(mq.url))) by {
                assert forall|k: int| e + 1 <= k < len implies super::runs::outside(#[trigger] input[k], super::runs::query_set(mq.url)) by {
                    assert(input[k] == q[k - e - 1]);
                }
            }
            assert(super::runs::outside_all(Seq::<u32>::empty(), super::runs::query_set(mq.url)));
            super::runs::lemma_query_run(ctx, mq, seq![], len);
            assert(input.subrange(e + 1, len) =~= q);
            assert(Seq::<u32>::empty() + Seq::<u32>::empty() + q =~= q);
        },
        (Some(q), Some(f)) => {
            let ql = e + 1 + q.len();
            assert(input =~= head + seq![0x3Fu32] + q + seq![0x23u32] + f);
            assert(input.len() == ql + 1 + f.len());
            assert(input[ql] == 0x23);
            let mq = Machine { url: Url { query: Some(seq![]), ..url }, buffer: seq![], state: State::Query, pointer: e + 1, ..m };
            assert(super::runs::outside_between(input, e + 1, ql, super::runs::query_set(mq.url))) by {
                assert forall|k: int| e + 1 <= k < ql implies super::runs::outside(#[trigger] input[k], super::runs::query_set(mq.url)) by {
                    assert(input[k] == q[k - e - 1]);
                }
            }
            assert(super::runs::outside_between(input, ql + 1, len, clazel_percent::spec::PercentEncodeSet::Fragment)) by {
                assert forall|k: int| ql + 1 <= k < len implies super::runs::outside(#[trigger] input[k], clazel_percent::spec::PercentEncodeSet::Fragment) by {
                    assert(input[k] == f[k - ql - 1]);
                }
            }
            assert(super::runs::outside_all(Seq::<u32>::empty(), super::runs::query_set(mq.url)));
            super::runs::lemma_query_run(ctx, mq, seq![], ql);
            assert(input.subrange(e + 1, ql) =~= q);
            assert(input.subrange(ql + 1, len) =~= f);
            assert(Seq::<u32>::empty() + Seq::<u32>::empty() + q =~= q);
        },
        (None, Some(f)) => {
            assert(input =~= head + seq![0x23u32] + f);
            assert(input.len() == e + 1 + f.len());
            let mf = Machine { url: Url { fragment: Some(seq![]), ..url }, buffer: seq![], state: State::Fragment, pointer: e + 1, ..m };
            assert(super::runs::outside_between(input, e + 1, len, clazel_percent::spec::PercentEncodeSet::Fragment)) by {
                assert forall|k: int| e + 1 <= k < len implies super::runs::outside(#[trigger] input[k], clazel_percent::spec::PercentEncodeSet::Fragment) by {
                    assert(input[k] == f[k - e - 1]);
                }
            }
            super::runs::lemma_fragment_run(ctx, mf, seq![]);
            assert(Seq::<u32>::empty() + input.subrange(e + 1, len) =~= f);
        },
    }
}

// ---------------------------------------------------------------------
// The theorem.
// ---------------------------------------------------------------------

/// The code points of a serialization of the class are above U+0020
/// SPACE, and its parts sit where [`head`] says.
proof fn lemma_serialization_chars(u: Url)
    requires
        round_trip_url(u),
    ensures
        super::runs::no_c0_or_space(url_serializer(u, false)),
{
    let s = url_serializer(u, false);
    lemma_serialization(u);
    let h = u.host->Some_0->Opaque_0;
    let segs = u.path->List_0;
    let sp = serialize_segments(segs);
    let pp = port_part(u.port);
    let hd = head(u);
    let n = u.scheme.len() as int;
    let a = n + 3;
    let k = a + h.len();
    let t = k + pp.len();
    assert forall|i: int| 0 <= i < pp.len() implies #[trigger] pp[i] > 0x20 by {
        if let Some(port) = u.port {
            lemma_serialize_integer(port);
            if i > 0 {
                assert(pp[i] == crate::host::spec::serialize_integer(port)[i - 1]);
            }
        }
    }
    assert forall|i: int| 0 <= i < sp.len() implies #[trigger] sp[i] > 0x20 by {
        if segs.len() > 0 {
            lemma_serialize_join(segs);
            lemma_join_plain(segs);
            if i > 0 {
                assert(sp[i] == super::runs::join(segs)[i - 1]);
            }
        } else {
            assert(sp.len() == 0);
        }
    }
    assert(super::runs::no_c0_or_space(hd)) by {
        assert forall|i: int| 0 <= i < hd.len() implies #[trigger] hd[i] > 0x20 by {
            if i < n {
                assert(hd[i] == u.scheme[i]);
            } else if a <= i < k {
                assert(hd[i] == h[i - a]);
            } else if k <= i < t {
                assert(hd[i] == pp[i - k]);
            } else if i >= t {
                assert(hd[i] == sp[i - t]);
            }
        }
    }
    let hq = super::independent::with_query(hd, u.query);
    assert(super::runs::no_c0_or_space(hq)) by {
        if let Some(q) = u.query {
            assert forall|i: int| 0 <= i < hq.len() implies #[trigger] hq[i] > 0x20 by {
                if i > hd.len() {
                    assert(hq[i] == q[i - hd.len() - 1]);
                }
            }
        }
    }
    assert(super::runs::no_c0_or_space(s)) by {
        if let Some(f) = u.fragment {
            assert forall|i: int| 0 <= i < s.len() implies #[trigger] s[i] > 0x20 by {
                if i > hq.len() {
                    assert(s[i] == f[i - hq.len() - 1]);
                }
            }
        }
    }
}

/// The scheme start state at an ASCII lower alpha goes to the scheme
/// state at the next code point.
proof fn lemma_scheme_start_step(ctx: Ctx, m: Machine)
    requires
        m.state is SchemeStart,
        m.pointer == 0,
        ctx.input.len() > 1,
        0x61 <= ctx.input[0] <= 0x7A,
    ensures
        run(ctx, m) == run(ctx, Machine { buffer: m.buffer.push(ctx.input[0]), state: State::Scheme, pointer: 1, ..m }),
{
    reveal(state_step);
}

/// Where the serialization's parts start: the authority (`a`), the port
/// part (`k`), the path (`t`), and the query or fragment (`e`).
pub open spec fn pos_a(u: Url) -> int {
    u.scheme.len() as int + 3
}

/// The port part's start.
pub open spec fn pos_k(u: Url) -> int {
    pos_a(u) + u.host->Some_0->Opaque_0.len() as int
}

/// The path's start.
pub open spec fn pos_t(u: Url) -> int {
    pos_k(u) + port_part(u.port).len() as int
}

/// The path's end.
pub open spec fn pos_e(u: Url) -> int {
    pos_t(u) + serialize_segments(u.path->List_0).len() as int
}

/// The facts about the serialization's layout the runs need.
proof fn lemma_layout(u: Url)
    requires
        round_trip_url(u),
    ensures
        ({
            let s = url_serializer(u, false);
            let h = u.host->Some_0->Opaque_0;
            let segs = u.path->List_0;
            let n = u.scheme.len() as int;
            let (a, k, t, e) = (pos_a(u), pos_k(u), pos_t(u), pos_e(u));
            &&& e <= s.len()
            &&& s == super::independent::with_fragment(super::independent::with_query(s.subrange(0, e), u.query), u.fragment)
            &&& s.subrange(0, n) == u.scheme && s[n] == 0x3A && s[n + 1] == 0x2F && s[n + 2] == 0x2F
            &&& s.subrange(a, k) == h
            &&& forall|j: int| a <= j < t ==> (#[trigger] s[j] != 0x40 && !super::independent::is_slash_question_hash(s[j]))
            &&& t == s.len() || super::independent::is_slash_question_hash(s[t])
            &&& k == s.len() || s[k] == 0x3A || super::independent::is_slash_question_hash(s[k])
            &&& (u.port matches Some(port) ==> s[k] == 0x3A && s.subrange(k + 1, t) == crate::host::spec::serialize_integer(port))
            &&& (u.port is None ==> k == t)
            &&& (segs.len() > 0 ==> s[t] == 0x2F && s.subrange(t + 1, e) == super::runs::join(segs))
            &&& (segs.len() == 0 ==> e == t)
        }),
{
    let s = url_serializer(u, false);
    lemma_serialization(u);
    let h = u.host->Some_0->Opaque_0;
    let segs = u.path->List_0;
    let sp = serialize_segments(segs);
    let pp = port_part(u.port);
    let hd = head(u);
    let n = u.scheme.len() as int;
    let (a, k, t, e) = (pos_a(u), pos_k(u), pos_t(u), pos_e(u));
    assert(s.subrange(0, e) =~= hd) by {
        match (u.query, u.fragment) {
            (Some(q), Some(f)) => assert(s =~= hd + seq![0x3Fu32] + q + seq![0x23u32] + f),
            (Some(q), None) => assert(s =~= hd + seq![0x3Fu32] + q),
            (None, Some(f)) => assert(s =~= hd + seq![0x23u32] + f),
            (None, None) => {},
        }
    }
    assert(forall|i: int| 0 <= i < e ==> s[i] == hd[i]);
    assert(s.subrange(0, n) =~= u.scheme);
    assert(s.subrange(a, k) =~= h);
    if segs.len() > 0 {
        lemma_serialize_join(segs);
        lemma_join_plain(segs);
        assert(s.subrange(t + 1, e) =~= super::runs::join(segs)) by {
            assert forall|i: int| 0 <= i < e - t - 1 implies s.subrange(t + 1, e)[i] == super::runs::join(segs)[i] by {
                assert(hd[t + 1 + i] == sp[i + 1]);
            }
        }
    }
    assert(t == s.len() || super::independent::is_slash_question_hash(s[t])) by {
        if t < s.len() {
            if segs.len() > 0 {
                assert(hd[t] == sp[0]);
            } else {
                super::independent::lemma_tail_delimiter(s, e, u.query, u.fragment);
            }
        }
    }
    if let Some(port) = u.port {
        lemma_serialize_integer(port);
        assert(hd[k] == pp[0]);
        assert(s.subrange(k + 1, t) =~= crate::host::spec::serialize_integer(port)) by {
            assert forall|j: int| 0 <= j < t - k - 1 implies s.subrange(k + 1, t)[j] == crate::host::spec::serialize_integer(port)[j] by {
                assert(hd[k + 1 + j] == pp[j + 1]);
            }
        }
    }
    assert forall|j: int| a <= j < t implies (#[trigger] s[j] != 0x40 && !super::independent::is_slash_question_hash(s[j])) by {
        if j < k {
            assert(hd[j] == h[j - a]);
            assert(!crate::host::spec::is_forbidden_host_code_point(h[j - a]));
        } else {
            assert(hd[j] == pp[j - k]);
            if let Some(port) = u.port {
                lemma_serialize_integer(port);
                if j > k {
                    assert(pp[j - k] == crate::host::spec::serialize_integer(port)[j - k - 1]);
                }
            }
        }
    }
}

/// The parser's context on the serialization of `u`.
pub open spec fn rt_ctx(u: Url, dp: crate::host::spec::DomainParser) -> Ctx {
    Ctx { input: url_serializer(u, false), base: None, state_override: None, domain_parser: dp }
}

/// The machine at the path's start: scheme, host and port set.
pub open spec fn rt_path_start(u: Url) -> Machine {
    Machine {
        url: Url { scheme: u.scheme, host: u.host, port: u.port, ..new_url() },
        buffer: seq![],
        state: State::PathStart,
        pointer: pos_t(u),
        ..super::lemmas::initial_machine()
    }
}

/// From the authority's start to the path's start: the authority, host
/// and port states.
proof fn lemma_authority_part(u: Url, dp: crate::host::spec::DomainParser)
    requires
        round_trip_url(u),
    ensures
        run(
            rt_ctx(u, dp),
            Machine {
                url: Url { scheme: u.scheme, ..new_url() },
                buffer: seq![],
                state: State::Authority,
                pointer: pos_a(u),
                ..super::lemmas::initial_machine()
            },
        ) == run(rt_ctx(u, dp), rt_path_start(u)),
{
    lemma_layout(u);
    let ctx = rt_ctx(u, dp);
    let s = ctx.input;
    let h = u.host->Some_0->Opaque_0;
    let (a, k, t) = (pos_a(u), pos_k(u), pos_t(u));
    let u1 = Url { scheme: u.scheme, ..new_url() };
    let m2 = Machine { url: u1, buffer: seq![], state: State::Authority, pointer: a, ..super::lemmas::initial_machine() };
    assert(s.subrange(a, a) =~= Seq::<u32>::empty());
    lemma_authority_run(ctx, m2, a, t);
    let m3 = Machine { buffer: seq![], state: State::Host, pointer: a, ..m2 };
    lemma_host_run(ctx, m3, a, k);
    let u2 = Url { host: Some(crate::host::spec::Host::Opaque(h)), ..u1 };
    if let Some(port) = u.port {
        let m4 = Machine { url: u2, buffer: seq![], state: State::Port, pointer: k + 1, ..m3 };
        lemma_serialize_integer(port);
        assert(Seq::<u32>::empty() + s.subrange(k + 1, t) =~= s.subrange(k + 1, t));
        lemma_port_run(ctx, m4, port, t);
    }
    assert(rt_path_start(u).url == Url { port: u.port, ..u2 });
}

/// From the path's start to the end: the path start, path, query and
/// fragment states.
proof fn lemma_path_part(u: Url, dp: crate::host::spec::DomainParser)
    requires
        round_trip_url(u),
    ensures
        run(rt_ctx(u, dp), rt_path_start(u)) == Some(u),
{
    lemma_layout(u);
    let ctx = rt_ctx(u, dp);
    let s = ctx.input;
    let len = s.len() as int;
    let segs = u.path->List_0;
    let (t, e) = (pos_t(u), pos_e(u));
    let m5 = rt_path_start(u);
    let u3 = m5.url;
    lemma_path_start_run(ctx, m5);
    assert(Url { query: u.query, fragment: u.fragment, path: UrlPath::List(segs), ..u3 } =~= u) by {
        assert(u.username =~= Seq::<u32>::empty());
        assert(u.password =~= Seq::<u32>::empty());
    }
    if segs.len() > 0 {
        let m6 = Machine { state: State::Path, pointer: t + 1, ..m5 };
        assert(forall|i: int| 0 <= i < segs.len() ==> super::runs::path_segment_ok(#[trigger] segs[i])) by {
            assert forall|i: int| 0 <= i < segs.len() implies super::runs::path_segment_ok(#[trigger] segs[i]) by {
                assert(round_trip_segment(segs[i]));
            }
        }
        lemma_serialize_join(segs);
        let j = super::runs::join(segs);
        assert(e == t + 1 + j.len());
        if e < len {
            super::independent::lemma_tail_delimiter(s, e, u.query, u.fragment);
        }
        super::runs::lemma_path_run(ctx, m6, seq![], segs);
        lemma_path_model_plain(seq![], segs);
        assert(Seq::<Seq<u32>>::empty() + segs =~= segs);
        let u4 = Url { path: UrlPath::List(segs), ..u3 };
        lemma_round_trip_tail(ctx, u4, m6, e, u.query, u.fragment);
    } else {
        assert(segs =~= Seq::<Seq<u32>>::empty());
        assert(u3.path == UrlPath::List(segs));
        lemma_round_trip_tail(ctx, u3, m5, e, u.query, u.fragment);
    }
}

/// **Theorem.** For every URL of the class and every domain parser, the
/// basic URL parser on its serialization, with no base, returns it.
pub proof fn lemma_serialize_parse(u: Url, dp: crate::host::spec::DomainParser)
    requires
        round_trip_url(u),
    ensures
        basic_url_parser(url_serializer(u, false), None, dp) == Some(u),
{
    let s = url_serializer(u, false);
    lemma_layout(u);
    lemma_serialization_chars(u);
    super::runs::lemma_prepared_identity(s);
    let ctx = rt_ctx(u, dp);
    let n = u.scheme.len() as int;
    let m0 = super::lemmas::initial_machine();
    assert(basic_url_parser(s, None, dp) == run(ctx, m0));
    assert(s[0] == u.scheme[0]) by {
        assert(s.subrange(0, n)[0] == s[0]);
    }
    lemma_scheme_start_step(ctx, m0);
    let m1 = Machine { buffer: seq![s[0]], state: State::Scheme, pointer: 1, ..m0 };
    assert(m0.buffer.push(s[0]) =~= seq![s[0]]);
    assert(seq![s[0]] =~= s.subrange(0, 1));
    lemma_scheme_run(ctx, m1, n);
    lemma_authority_part(u, dp);
    lemma_path_part(u, dp);
}

/// URL Goals, for the class: if parsing an input (against any base, with
/// any domain parser) gives a URL of the class, parsing its serialization
/// again and serializing gives the same string.
pub proof fn lemma_idempotent(input: Seq<u32>, base: Option<Url>, dp: crate::host::spec::DomainParser)
    requires
        basic_url_parser(input, base, dp) matches Some(u) && round_trip_url(u),
    ensures
        ({
            let u = basic_url_parser(input, base, dp)->Some_0;
            basic_url_parser(url_serializer(u, false), None, dp) matches Some(v) && url_serializer(v, false)
                == url_serializer(u, false)
        }),
{
    lemma_serialize_parse(basic_url_parser(input, base, dp)->Some_0, dp);
}

} // verus!
