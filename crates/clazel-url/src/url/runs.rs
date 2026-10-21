//! Lemmas about runs of the basic URL parser's state machine over strings
//! of a known shape: what the fragment, query and path states do with a
//! run of ASCII alphanumerics (and dot segments), and that percent-encoding
//! and input preparation leave such strings alone. `independent.rs` builds
//! the RFC 3986 agreement theorem on them.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------
// Strings.
// ---------------------------------------------------------------------

/// Every code point of `s` is an ASCII alphanumeric.
pub open spec fn all_alphanumeric(s: Seq<u32>) -> bool {
    forall|k: int| 0 <= k < s.len() ==> is_ascii_alphanumeric(#[trigger] s[k])
}

/// `s[i..j)` holds ASCII alphanumerics.
pub open spec fn alphanumeric_between(s: Seq<u32>, i: int, j: int) -> bool {
    forall|k: int| i <= k < j ==> is_ascii_alphanumeric(#[trigger] s[k])
}

/// A path segment of the agreement class: ASCII alphanumerics, ".", or
/// "..".
pub open spec fn segment_ok(s: Seq<u32>) -> bool {
    all_alphanumeric(s) || s == seq![0x2Eu32] || s == seq![0x2Eu32, 0x2E]
}

/// `s[i..j)` holds ASCII alphanumerics and U+002E (.).
pub open spec fn segment_chars_between(s: Seq<u32>, i: int, j: int) -> bool {
    forall|k: int| i <= k < j ==> (is_ascii_alphanumeric(#[trigger] s[k]) || s[k] == 0x2E)
}

/// `c` is an ASCII code point outside `set`: what UTF-8 percent-encoding
/// with `set` leaves as it is.
pub open spec fn outside(c: u32, set: clazel_percent::spec::PercentEncodeSet) -> bool {
    c <= 0x7F && !clazel_percent::spec::contains(set, c)
}

/// `s[i..j)` holds code points [`outside`] `set`.
pub open spec fn outside_between(s: Seq<u32>, i: int, j: int, set: clazel_percent::spec::PercentEncodeSet) -> bool {
    forall|k: int| i <= k < j ==> outside(#[trigger] s[k], set)
}

/// Every code point of `s` is [`outside`] `set`.
pub open spec fn outside_all(s: Seq<u32>, set: clazel_percent::spec::PercentEncodeSet) -> bool {
    forall|k: int| 0 <= k < s.len() ==> outside(#[trigger] s[k], set)
}

/// The query state's percent-encode set for `url` (step 2.1).
pub open spec fn query_set(url: Url) -> clazel_percent::spec::PercentEncodeSet {
    if is_special(url) {
        clazel_percent::spec::PercentEncodeSet::SpecialQuery
    } else {
        clazel_percent::spec::PercentEncodeSet::Query
    }
}

/// A path segment the path state reads as it is: code points outside the
/// path percent-encode set, none of them U+002F (/). (The set holds "?"
/// and "#".)
pub open spec fn path_segment_ok(s: Seq<u32>) -> bool {
    forall|k: int| 0 <= k < s.len() ==> outside(#[trigger] s[k], clazel_percent::spec::PercentEncodeSet::Path) && s[k]
        != 0x2F
}

/// `s[i..j)` holds code points a path segment may hold.
pub open spec fn path_chars_between(s: Seq<u32>, i: int, j: int) -> bool {
    forall|k: int| i <= k < j ==> outside(#[trigger] s[k], clazel_percent::spec::PercentEncodeSet::Path) && s[k] != 0x2F
}

/// ASCII alphanumerics are outside the fragment, query, special-query and
/// path sets, and are not "/".
pub proof fn lemma_alphanumeric_outside(s: Seq<u32>, i: int, j: int)
    requires
        alphanumeric_between(s, i, j),
    ensures
        outside_between(s, i, j, clazel_percent::spec::PercentEncodeSet::Fragment),
        outside_between(s, i, j, clazel_percent::spec::PercentEncodeSet::Query),
        outside_between(s, i, j, clazel_percent::spec::PercentEncodeSet::SpecialQuery),
{
    assert forall|k: int| i <= k < j implies outside(#[trigger] s[k], clazel_percent::spec::PercentEncodeSet::Fragment)
        && outside(s[k], clazel_percent::spec::PercentEncodeSet::Query) && outside(
        s[k],
        clazel_percent::spec::PercentEncodeSet::SpecialQuery,
    ) by {
        lemma_alphanumeric_not_in_sets(s[k]);
    }
}

/// The segments of the RFC 3986 agreement class are path segments the
/// path state reads as they are.
pub proof fn lemma_segments_path_ok(segs: Seq<Seq<u32>>)
    requires
        forall|i: int| 0 <= i < segs.len() ==> segment_ok(#[trigger] segs[i]),
    ensures
        forall|i: int| 0 <= i < segs.len() ==> path_segment_ok(#[trigger] segs[i]),
{
    assert forall|i: int| 0 <= i < segs.len() implies path_segment_ok(#[trigger] segs[i]) by {
        let s = segs[i];
        assert(segment_ok(s));
        assert forall|k: int| 0 <= k < s.len() implies outside(#[trigger] s[k], clazel_percent::spec::PercentEncodeSet::Path)
            && s[k] != 0x2F by {
            if !all_alphanumeric(s) {
                assert(s == seq![0x2Eu32] || s == seq![0x2Eu32, 0x2E]);
            }
            lemma_alphanumeric_not_in_sets(s[k]);
        }
    }
}

/// The segments joined with "/", first to last.
pub open spec fn join(segs: Seq<Seq<u32>>) -> Seq<u32>
    decreases segs.len()
{
    if segs.len() == 0 {
        seq![]
    } else if segs.len() == 1 {
        segs[0]
    } else {
        segs[0] + seq![0x2Fu32] + join(segs.subrange(1, segs.len() as int))
    }
}

// ---------------------------------------------------------------------
// Percent-encoding leaves ASCII alphanumerics alone.
// ---------------------------------------------------------------------

/// The ASCII alphanumerics and U+002E (.) are in none of the
/// percent-encode sets the parser uses.
pub proof fn lemma_alphanumeric_not_in_sets(c: u32)
    requires
        is_ascii_alphanumeric(c) || c == 0x2E,
    ensures
        !clazel_percent::spec::contains(clazel_percent::spec::PercentEncodeSet::C0Control, c),
        !clazel_percent::spec::contains(clazel_percent::spec::PercentEncodeSet::Fragment, c),
        !clazel_percent::spec::contains(clazel_percent::spec::PercentEncodeSet::Query, c),
        !clazel_percent::spec::contains(clazel_percent::spec::PercentEncodeSet::SpecialQuery, c),
        !clazel_percent::spec::contains(clazel_percent::spec::PercentEncodeSet::Path, c),
{
}

/// Step 7.3 of percent-encode after encoding, from byte `i`, on the UTF-8
/// encoding of ASCII code points outside `set`: they come back unchanged.
proof fn lemma_encode_output_bytes_identity(set: clazel_percent::spec::PercentEncodeSet, s: Seq<u32>, i: nat)
    requires
        i <= s.len(),
        set != clazel_percent::spec::PercentEncodeSet::ApplicationXWwwFormUrlencoded,
        forall|k: int| 0 <= k < s.len() ==> #[trigger] s[k] <= 0x7F && !clazel_percent::spec::contains(set, s[k]),
    ensures
        clazel_percent::spec::encode_output_bytes(set, false, s.map_values(|c: u32| c as u8), i) == s.subrange(
            i as int,
            s.len() as int,
        ),
    decreases s.len() - i,
{
    let bytes = s.map_values(|c: u32| c as u8);
    if i < s.len() {
        lemma_encode_output_bytes_identity(set, s, i + 1);
        assert(bytes[i as int] as u32 == s[i as int]);
        assert(s.subrange(i as int, s.len() as int) =~= seq![s[i as int]] + s.subrange(i as int + 1, s.len() as int));
    } else {
        assert(s.subrange(i as int, s.len() as int) =~= seq![]);
    }
}

/// Percent-encode after encoding (UTF-8) is the identity on ASCII strings
/// with no code point in the set.
pub proof fn lemma_encode_identity(s: Seq<u32>, set: clazel_percent::spec::PercentEncodeSet)
    requires
        set != clazel_percent::spec::PercentEncodeSet::ApplicationXWwwFormUrlencoded,
        forall|k: int| 0 <= k < s.len() ==> #[trigger] s[k] <= 0x7F && !clazel_percent::spec::contains(set, s[k]),
    ensures
        clazel_percent::spec::percent_encode_after_encoding_utf8(s, set) == s,
{
    assert(clazel_percent::lemmas::all_ascii(s));
    clazel_percent::lemmas::lemma_utf8_encode_ascii(s);
    lemma_encode_output_bytes_identity(set, s, 0);
    assert(s.subrange(0, s.len() as int) =~= s);
}

/// UTF-8 percent-encoding a code point outside the set gives the code
/// point itself.
pub proof fn lemma_encode_code_point_identity(c: u32, set: clazel_percent::spec::PercentEncodeSet)
    requires
        outside(c, set),
        set != clazel_percent::spec::PercentEncodeSet::ApplicationXWwwFormUrlencoded,
    ensures
        clazel_percent::spec::utf8_percent_encode_code_point(c, set) == seq![c],
{
    lemma_encode_identity(seq![c], set);
}

/// Percent-encoding a string of ASCII alphanumerics with the query or
/// special-query set gives the string itself.
pub proof fn lemma_encode_alphanumeric(s: Seq<u32>, set: clazel_percent::spec::PercentEncodeSet)
    requires
        all_alphanumeric(s),
        set == clazel_percent::spec::PercentEncodeSet::Query || set == clazel_percent::spec::PercentEncodeSet::SpecialQuery,
    ensures
        clazel_percent::spec::percent_encode_after_encoding_utf8(s, set) == s,
{
    assert forall|k: int| 0 <= k < s.len() implies #[trigger] s[k] <= 0x7F && !clazel_percent::spec::contains(
        set,
        s[k],
    ) by {
        lemma_alphanumeric_not_in_sets(s[k]);
    }
    lemma_encode_identity(s, set);
}

// ---------------------------------------------------------------------
// Steps 1 to 3 leave a string with no C0 control, space, tab or newline
// alone.
// ---------------------------------------------------------------------

/// No code point of `s` is a C0 control or space (so none is an ASCII tab
/// or newline either).
pub open spec fn no_c0_or_space(s: Seq<u32>) -> bool {
    forall|k: int| 0 <= k < s.len() ==> #[trigger] s[k] > 0x20
}

/// Removing ASCII tab or newline does nothing to such a string.
proof fn lemma_remove_tab_identity(s: Seq<u32>)
    requires
        no_c0_or_space(s),
    ensures
        remove_ascii_tab_or_newline(s) == s,
    decreases s.len(),
{
    if s.len() > 0 {
        lemma_remove_tab_identity(s.drop_last());
        assert(s.drop_last().push(s.last()) =~= s);
    }
}

/// Basic URL parser steps 1.3 and 3 do nothing to such a string.
pub proof fn lemma_prepared_identity(s: Seq<u32>)
    requires
        no_c0_or_space(s),
    ensures
        remove_ascii_tab_or_newline(strip_trailing_c0_control_or_space(strip_leading_c0_control_or_space(s))) == s,
{
    lemma_remove_tab_identity(s);
}

// ---------------------------------------------------------------------
// The fragment and query states.
// ---------------------------------------------------------------------

/// The fragment state over ASCII alphanumerics to the end of the input
/// appends them to the fragment.
pub proof fn lemma_fragment_run(ctx: Ctx, m: Machine, f: Seq<u32>)
    requires
        m.state is Fragment,
        0 <= m.pointer <= ctx.input.len(),
        m.url.fragment == Some(f),
        outside_between(ctx.input, m.pointer, ctx.input.len() as int, clazel_percent::spec::PercentEncodeSet::Fragment),
    ensures
        run(ctx, m) == Some(Url { fragment: Some(f + ctx.input.subrange(m.pointer, ctx.input.len() as int)), ..m.url }),
    decreases ctx.input.len() - m.pointer,
{
    reveal(state_step);
    let len = ctx.input.len() as int;
    if m.pointer < len {
        let c = ctx.input[m.pointer];
        lemma_encode_code_point_identity(c, clazel_percent::spec::PercentEncodeSet::Fragment);
        let n = Machine { url: Url { fragment: Some(f.push(c)), ..m.url }, pointer: m.pointer + 1, ..m };
        assert(f + seq![c] =~= f.push(c));
        lemma_fragment_run(ctx, n, f.push(c));
        assert(f.push(c) + ctx.input.subrange(m.pointer + 1, len) =~= f + ctx.input.subrange(m.pointer, len));
    } else {
        assert(f + ctx.input.subrange(m.pointer, len) =~= f);
    }
}

/// The query state over ASCII alphanumerics up to `e` (the end of the
/// input, or a U+0023 (#) followed by ASCII alphanumerics): the query gets
/// buffer and them, and the fragment, if there is one, the rest.
pub proof fn lemma_query_run(ctx: Ctx, m: Machine, q: Seq<u32>, e: int)
    requires
        m.state is Query,
        ctx.state_override is None,
        0 <= m.pointer <= e <= ctx.input.len(),
        m.url.query == Some(q),
        outside_all(m.buffer, query_set(m.url)),
        outside_between(ctx.input, m.pointer, e, query_set(m.url)),
        e == ctx.input.len() || (ctx.input[e] == 0x23 && outside_between(
            ctx.input,
            e + 1,
            ctx.input.len() as int,
            clazel_percent::spec::PercentEncodeSet::Fragment,
        )),
    ensures
        run(ctx, m) == Some(
            Url {
                query: Some(q + m.buffer + ctx.input.subrange(m.pointer, e)),
                fragment: if e < ctx.input.len() {
                    Some(ctx.input.subrange(e + 1, ctx.input.len() as int))
                } else {
                    m.url.fragment
                },
                ..m.url
            },
        ),
    decreases e - m.pointer,
{
    reveal(state_step);
    let len = ctx.input.len() as int;
    if m.pointer < e {
        let c = ctx.input[m.pointer];
        let n = Machine { buffer: m.buffer.push(c), pointer: m.pointer + 1, ..m };
        assert(outside_all(m.buffer.push(c), query_set(m.url))) by {
            assert forall|k: int| 0 <= k < m.buffer.push(c).len() implies outside(
                #[trigger] m.buffer.push(c)[k],
                query_set(m.url),
            ) by {
                if k < m.buffer.len() {
                    assert(m.buffer.push(c)[k] == m.buffer[k]);
                }
            }
        }
        lemma_query_run(ctx, n, q, e);
        assert(m.buffer.push(c) + ctx.input.subrange(m.pointer + 1, e) =~= m.buffer + ctx.input.subrange(
            m.pointer,
            e,
        ));
        assert(q + m.buffer.push(c) + ctx.input.subrange(m.pointer + 1, e) =~= q + m.buffer
            + ctx.input.subrange(m.pointer, e));
    } else {
        let set = if is_special(m.url) {
            clazel_percent::spec::PercentEncodeSet::SpecialQuery
        } else {
            clazel_percent::spec::PercentEncodeSet::Query
        };
        lemma_encode_identity(m.buffer, set);
        assert(ctx.input.subrange(m.pointer, e) =~= seq![]);
        assert(q + m.buffer + ctx.input.subrange(m.pointer, e) =~= q + m.buffer);
        let url = Url { query: Some(q + m.buffer), ..m.url };
        if e < len {
            let n = Machine {
                url: Url { fragment: Some(seq![]), ..url },
                buffer: seq![],
                state: State::Fragment,
                pointer: m.pointer + 1,
                ..m
            };
            lemma_fragment_run(ctx, n, seq![]);
            assert(Seq::<u32>::empty() + ctx.input.subrange(e + 1, len) =~= ctx.input.subrange(e + 1, len));
        }
    }
}

// ---------------------------------------------------------------------
// The path state.
// ---------------------------------------------------------------------

/// Shortening a non-file URL's path that is a list removes its last item,
/// if any.
pub open spec fn shorten_list(l: Seq<Seq<u32>>) -> Seq<Seq<u32>> {
    if l.len() > 0 {
        l.drop_last()
    } else {
        l
    }
}

/// What the path state does at the end of segment `seg` of a non-file
/// URL (steps 1.2 to 1.4), `slash` being whether c is U+002F (/).
pub open spec fn seg_step(l: Seq<Seq<u32>>, seg: Seq<u32>, slash: bool) -> Seq<Seq<u32>> {
    if is_double_dot_segment(seg) {
        if slash {
            shorten_list(l)
        } else {
            shorten_list(l).push(seq![])
        }
    } else if is_single_dot_segment(seg) {
        if slash {
            l
        } else {
            l.push(seq![])
        }
    } else {
        l.push(seg)
    }
}

/// The path state over the segments `segs` (each but the last ended by
/// U+002F (/)), from the path `l`.
pub open spec fn path_model(l: Seq<Seq<u32>>, segs: Seq<Seq<u32>>) -> Seq<Seq<u32>>
    decreases segs.len()
{
    if segs.len() == 0 {
        l
    } else if segs.len() == 1 {
        seg_step(l, segs[0], false)
    } else {
        path_model(seg_step(l, segs[0], true), segs.subrange(1, segs.len() as int))
    }
}

/// A url the path lemmas apply to: not special (so U+005C (\) is not a
/// slash and its scheme is not "file") and with a list path.
pub open spec fn plain_path_url(url: Url) -> bool {
    !is_special(url) && url.path is List
}

/// The path state over the code points of one segment (ASCII
/// alphanumerics and U+002E (.)) appends them to buffer.
pub proof fn lemma_path_chars(ctx: Ctx, m: Machine, k: int)
    requires
        m.state is Path,
        ctx.state_override is None,
        plain_path_url(m.url),
        0 <= m.pointer <= k <= ctx.input.len(),
        path_chars_between(ctx.input, m.pointer, k),
    ensures
        run(ctx, m) == run(ctx, Machine { buffer: m.buffer + ctx.input.subrange(m.pointer, k), pointer: k, ..m }),
    decreases k - m.pointer,
{
    if m.pointer < k {
        reveal(state_step);
        let c = ctx.input[m.pointer];
        lemma_encode_code_point_identity(c, clazel_percent::spec::PercentEncodeSet::Path);
        let n = Machine { buffer: m.buffer + seq![c], pointer: m.pointer + 1, ..m };
        lemma_path_chars(ctx, n, k);
        assert(m.buffer + seq![c] + ctx.input.subrange(m.pointer + 1, k) =~= m.buffer + ctx.input.subrange(
            m.pointer,
            k,
        ));
    } else {
        assert(m.buffer + ctx.input.subrange(m.pointer, k) =~= m.buffer);
    }
}

/// The path state's run at the end of a segment (c is U+002F (/), U+003F
/// (?), U+0023 (#), or the EOF code point), with buffer holding it.
pub proof fn lemma_path_segment_end(ctx: Ctx, m: Machine, l: Seq<Seq<u32>>)
    requires
        m.state is Path,
        ctx.state_override is None,
        plain_path_url(m.url),
        m.url.path == UrlPath::List(l),
        0 <= m.pointer <= ctx.input.len(),
        m.pointer == ctx.input.len() || ctx.input[m.pointer] == 0x2F || ctx.input[m.pointer] == 0x3F
            || ctx.input[m.pointer] == 0x23,
    ensures
        ({
            let p = m.pointer;
            let len = ctx.input.len() as int;
            let slash = p < len && ctx.input[p] == 0x2F;
            let url = Url { path: UrlPath::List(seg_step(l, m.buffer, slash)), ..m.url };
            &&& p == len ==> run(ctx, m) == Some(url)
            &&& (p < len && ctx.input[p] == 0x2F) ==> run(ctx, m) == run(
                ctx,
                Machine { url: url, buffer: seq![], pointer: p + 1, ..m },
            )
            &&& (p < len && ctx.input[p] == 0x3F) ==> run(ctx, m) == run(
                ctx,
                Machine {
                    url: Url { query: Some(seq![]), ..url },
                    buffer: seq![],
                    state: State::Query,
                    pointer: p + 1,
                    ..m
                },
            )
            &&& (p < len && ctx.input[p] == 0x23) ==> run(ctx, m) == run(
                ctx,
                Machine {
                    url: Url { fragment: Some(seq![]), ..url },
                    buffer: seq![],
                    state: State::Fragment,
                    pointer: p + 1,
                    ..m
                },
            )
        }),
{
    reveal(state_step);
    let p = m.pointer;
    let len = ctx.input.len() as int;
    let slash = p < len && ctx.input[p] == 0x2F;
    assert(c_is_path_slash(ctx, m) == slash);
    assert(m.url.scheme != file_str());
    let url = Url { path: UrlPath::List(seg_step(l, m.buffer, slash)), ..m.url };
    let stepped = path_state(ctx, m);
    if is_double_dot_segment(m.buffer) {
        assert(shorten(m.url) == Url { path: UrlPath::List(shorten_list(l)), ..m.url });
    }
    assert(stepped matches Step::Continue(next) && next.url == if p < len && ctx.input[p] == 0x3F {
        Url { query: Some(seq![]), ..url }
    } else if p < len && ctx.input[p] == 0x23 {
        Url { fragment: Some(seq![]), ..url }
    } else {
        url
    });
}

/// The path state over `join(segs)` from `p`, from the path `l` and an
/// empty buffer, up to `e` = `p` + `join(segs)`'s length (the end of the
/// input, U+003F (?) or U+0023 (#)).
pub proof fn lemma_path_run(ctx: Ctx, m: Machine, l: Seq<Seq<u32>>, segs: Seq<Seq<u32>>)
    requires
        m.state is Path,
        ctx.state_override is None,
        plain_path_url(m.url),
        m.url.path == UrlPath::List(l),
        m.buffer == Seq::<u32>::empty(),
        segs.len() > 0,
        forall|i: int| 0 <= i < segs.len() ==> path_segment_ok(#[trigger] segs[i]),
        0 <= m.pointer,
        m.pointer + join(segs).len() <= ctx.input.len(),
        ctx.input.subrange(m.pointer, m.pointer + join(segs).len()) == join(segs),
        m.pointer + join(segs).len() == ctx.input.len() || ctx.input[m.pointer + join(segs).len()] == 0x3F
            || ctx.input[m.pointer + join(segs).len()] == 0x23,
    ensures
        ({
            let e = m.pointer + join(segs).len();
            let len = ctx.input.len() as int;
            let url = Url { path: UrlPath::List(path_model(l, segs)), ..m.url };
            &&& e == len ==> run(ctx, m) == Some(url)
            &&& (e < len && ctx.input[e] == 0x3F) ==> run(ctx, m) == run(
                ctx,
                Machine {
                    url: Url { query: Some(seq![]), ..url },
                    buffer: seq![],
                    state: State::Query,
                    pointer: e + 1,
                    ..m
                },
            )
            &&& (e < len && ctx.input[e] == 0x23) ==> run(ctx, m) == run(
                ctx,
                Machine {
                    url: Url { fragment: Some(seq![]), ..url },
                    buffer: seq![],
                    state: State::Fragment,
                    pointer: e + 1,
                    ..m
                },
            )
        }),
    decreases segs.len(),
{
    let p = m.pointer;
    let s = segs[0];
    let k = p + s.len();
    // The first segment's code points.
    assert(path_chars_between(ctx.input, p, k)) by {
        assert forall|j: int| p <= j < k implies outside(#[trigger] ctx.input[j], clazel_percent::spec::PercentEncodeSet::Path)
            && ctx.input[j] != 0x2F by {
            assert(path_segment_ok(segs[0]));
            if segs.len() == 1 {
                assert(join(segs) == s);
            } else {
                assert(join(segs) == s + seq![0x2Fu32] + join(segs.subrange(1, segs.len() as int)));
            }
            assert(ctx.input.subrange(p, p + join(segs).len())[j - p] == join(segs)[j - p]);
            assert(join(segs)[j - p] == s[j - p]);
        }
    }
    lemma_path_chars(ctx, m, k);
    assert(ctx.input.subrange(p, k) =~= s) by {
        if segs.len() == 1 {
            assert(join(segs) == s);
        } else {
            assert(join(segs) == s + seq![0x2Fu32] + join(segs.subrange(1, segs.len() as int)));
        }
        assert forall|j: int| 0 <= j < s.len() implies ctx.input.subrange(p, k)[j] == s[j] by {
            assert(ctx.input.subrange(p, p + join(segs).len())[j] == join(segs)[j]);
        }
    }
    let at_k = Machine { buffer: s, pointer: k, ..m };
    assert(Seq::<u32>::empty() + ctx.input.subrange(p, k) =~= s);
    if segs.len() == 1 {
        assert(join(segs) == s);
        lemma_path_segment_end(ctx, at_k, l);
    } else {
        let rest = segs.subrange(1, segs.len() as int);
        assert(join(segs) == s + seq![0x2Fu32] + join(rest));
        assert(ctx.input[k] == 0x2F) by {
            assert(ctx.input.subrange(p, p + join(segs).len())[s.len() as int] == join(segs)[s.len() as int]);
        }
        lemma_path_segment_end(ctx, at_k, l);
        let l2 = seg_step(l, s, true);
        let next = Machine {
            url: Url { path: UrlPath::List(l2), ..m.url },
            buffer: seq![],
            pointer: k + 1,
            ..m
        };
        assert forall|i: int| 0 <= i < rest.len() implies path_segment_ok(#[trigger] rest[i]) by {
            assert(rest[i] == segs[i + 1]);
        }
        assert(ctx.input.subrange(k + 1, k + 1 + join(rest).len()) =~= join(rest)) by {
            assert forall|j: int| 0 <= j < join(rest).len() implies ctx.input.subrange(k + 1, k + 1 + join(rest).len())[j]
                == join(rest)[j] by {
                assert(ctx.input.subrange(p, p + join(segs).len())[s.len() + 1 + j] == join(segs)[s.len() + 1 + j]);
            }
        }
        lemma_path_run(ctx, next, l2, rest);
        assert(path_model(l, segs) == path_model(l2, rest));
    }
}


// ---------------------------------------------------------------------
// The scheme start and scheme states, when input has no scheme.
// ---------------------------------------------------------------------

/// A scheme state code point (scheme state step 1).
pub open spec fn is_scheme_code_point(c: u32) -> bool {
    is_ascii_alphanumeric(c) || c == 0x2B || c == 0x2D || c == 0x2E
}

/// The machine of the no scheme state at the first code point, after the
/// scheme state's start over (or the scheme start state's hand-off).
pub open spec fn no_scheme_machine(m: Machine) -> Machine {
    Machine { buffer: seq![], state: State::NoScheme, pointer: 0, ..m }
}

/// The scheme state over scheme code points up to `k`, where there is
/// none and no U+003A (:) either, starts over in the no scheme state.
pub proof fn lemma_scheme_no_colon(ctx: Ctx, m: Machine, k: int)
    requires
        m.state is Scheme,
        ctx.state_override is None,
        1 <= k <= ctx.input.len(),
        0 <= m.pointer <= k,
        forall|j: int| m.pointer <= j < k ==> is_scheme_code_point(#[trigger] ctx.input[j]),
        k == ctx.input.len() || (ctx.input[k] != 0x3A && !is_scheme_code_point(ctx.input[k])),
    ensures
        run(ctx, m) == run(ctx, no_scheme_machine(m)),
    decreases k - m.pointer,
{
    reveal(state_step);
    if m.pointer < k {
        let c = ctx.input[m.pointer];
        let n = Machine { buffer: m.buffer.push(ascii_lowercase(c)), pointer: m.pointer + 1, ..m };
        lemma_scheme_no_colon(ctx, n, k);
        assert(no_scheme_machine(n) == no_scheme_machine(m));
    }
}

/// From the scheme start state at the first code point: if the input
/// starts with no scheme (the run of scheme code points from an ASCII
/// alpha at its start, if any, ends at `k` with neither a scheme code
/// point nor U+003A (:)), the parser goes to the no scheme state at the
/// first code point with an empty buffer.
pub proof fn lemma_no_scheme_start(ctx: Ctx, m: Machine, k: int)
    requires
        m.state is SchemeStart,
        ctx.state_override is None,
        m.pointer == 0,
        m.buffer == Seq::<u32>::empty(),
        ctx.input.len() > 0 && is_ascii_alpha(ctx.input[0]) ==> (1 <= k <= ctx.input.len() && (forall|j: int|
            0 <= j < k ==> is_scheme_code_point(#[trigger] ctx.input[j])) && (k == ctx.input.len() || (
        ctx.input[k] != 0x3A && !is_scheme_code_point(ctx.input[k])))),
    ensures
        run(ctx, m) == run(ctx, no_scheme_machine(m)),
{
    reveal(state_step);
    if ctx.input.len() > 0 && is_ascii_alpha(ctx.input[0]) {
        let n = Machine {
            buffer: m.buffer.push(ascii_lowercase(ctx.input[0])),
            state: State::Scheme,
            pointer: 1,
            ..m
        };
        if 1 < ctx.input.len() {
            lemma_scheme_no_colon(ctx, n, k);
            assert(no_scheme_machine(n) == no_scheme_machine(m));
        } else {
            // One code point: the scheme state runs at the EOF code point.
            lemma_scheme_no_colon(ctx, n, 1);
            assert(no_scheme_machine(n) == no_scheme_machine(m));
        }
    } else {
        assert(no_scheme_machine(m) == Machine { state: State::NoScheme, pointer: m.pointer - 1 + 1, ..m });
    }
}

} // verus!
