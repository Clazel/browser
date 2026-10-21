//! A second, independent transcription of reference resolution, from a
//! different standard: RFC 3986 "Uniform Resource Identifier (URI):
//! Generic Syntax" (January 2005, <https://www.rfc-editor.org/rfc/rfc3986>),
//! Appendix B (parsing a URI reference with a regular expression), §5.2.2
//! (transform references, strict), §5.2.3 (merge paths), §5.2.4 (remove dot
//! segments) and §5.3 (component recomposition). It reads only the RFC,
//! not `spec.rs` (it was written after `spec.rs`, by the same author, so
//! it is independent in source, not in authorship).
//!
//! **Where the two standards agree** ([`lemma_resolution_agrees`]): the
//! WHATWG basic URL parser, given a base URL record, and RFC 3986, given
//! that record's serialization as the base URI, produce the same string,
//! for every base and reference in this class (and every domain parser):
//! - the base ([`rfc_base`]) has a scheme of ASCII lower alphas that is
//!   not a special scheme, an empty username and password, an opaque host
//!   of ASCII lower alphas and digits, no port, a path that is a list of
//!   segments of ASCII alphanumerics (possibly empty), an optional query
//!   of ASCII alphanumerics, and no fragment;
//! - the reference ([`ref_string`]) is a path, then optionally "?" and a
//!   query, then optionally "#" and a fragment, where the path is either
//!   empty, or "/" followed by segments joined with "/", or segments joined
//!   with "/" whose first one is not empty; every segment is ASCII
//!   alphanumerics, "." or ".."; the query and fragment are ASCII
//!   alphanumerics.
//!
//! The class covers the four kinds of RFC 3986 relative reference except
//! the network-path one ("//"): same document ("", "?q", "#f"),
//! absolute-path, and relative-path with dot-segments, including more ".."
//! than the base has levels. Outside it the standards intentionally differ
//! (special schemes, U+005C (\), percent-encoding, IDNA, opaque paths,
//! Windows drive letters, schemes in references, empty hosts).
//!
//! Modelling choices (each a deviation in form, never in meaning):
//! - A string is a `Seq<u32>` of code points; a component that is
//!   "undefined" (§5.2.1) is `None`.
//! - The Appendix B regular expression is transcribed as the scan it
//!   denotes: each group is the longest run of code points not in its
//!   excluded set, and an optional group is taken exactly when its
//!   delimiter is there. For `(([^:/?#]+):)?` that is the only match: a
//!   shorter run of `[^:/?#]` is followed by a code point that is not ":".
//!   `.` (in `(#(.*))?`) matches every code point.
//! - remove_dot_segments' two string buffers are the arguments of a
//!   recursive function; "where "." is a complete path segment" is "the
//!   input buffer is "/." or begins with "/./"" (B), likewise for ".." (C).
//! - The strict parser is used (§5.2.2: "if ((not strict) ...)" is not
//!   taken).

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------
// Appendix B: parsing a URI reference with a regular expression.
// ---------------------------------------------------------------------

/// The five components of a URI reference (§3, §5.2.1).
pub struct Components {
    /// scheme (`None`: undefined)
    pub scheme: Option<Seq<u32>>,
    /// authority (`None`: undefined)
    pub authority: Option<Seq<u32>>,
    /// path (never undefined)
    pub path: Seq<u32>,
    /// query (`None`: undefined)
    pub query: Option<Seq<u32>>,
    /// fragment (`None`: undefined)
    pub fragment: Option<Seq<u32>>,
}

/// `c` is one of ":", "/", "?", "#" (`[^:/?#]` excludes them).
pub open spec fn is_colon_slash_question_hash(c: u32) -> bool {
    c == 0x3A || c == 0x2F || c == 0x3F || c == 0x23
}

/// `c` is one of "/", "?", "#".
pub open spec fn is_slash_question_hash(c: u32) -> bool {
    c == 0x2F || c == 0x3F || c == 0x23
}

/// `c` is one of "?", "#".
pub open spec fn is_question_hash(c: u32) -> bool {
    c == 0x3F || c == 0x23
}

/// The end of the longest run of `[^:/?#]` from `i`.
pub open spec fn scan_scheme(s: Seq<u32>, i: nat) -> nat
    decreases s.len() - i
{
    if i < s.len() && !is_colon_slash_question_hash(s[i as int]) {
        scan_scheme(s, i + 1)
    } else {
        i
    }
}

/// The end of the longest run of `[^/?#]` from `i`.
pub open spec fn scan_authority(s: Seq<u32>, i: nat) -> nat
    decreases s.len() - i
{
    if i < s.len() && !is_slash_question_hash(s[i as int]) {
        scan_authority(s, i + 1)
    } else {
        i
    }
}

/// The end of the longest run of `[^?#]` from `i`.
pub open spec fn scan_path(s: Seq<u32>, i: nat) -> nat
    decreases s.len() - i
{
    if i < s.len() && !is_question_hash(s[i as int]) {
        scan_path(s, i + 1)
    } else {
        i
    }
}

/// The end of the longest run of `[^#]` from `i`.
pub open spec fn scan_query(s: Seq<u32>, i: nat) -> nat
    decreases s.len() - i
{
    if i < s.len() && s[i as int] != 0x23 {
        scan_query(s, i + 1)
    } else {
        i
    }
}

/// The part of `s` from `i` to `j`, or the empty string outside it.
pub open spec fn part(s: Seq<u32>, i: nat, j: nat) -> Seq<u32> {
    if i <= j <= s.len() {
        s.subrange(i as int, j as int)
    } else {
        seq![]
    }
}

/// Appendix B: `^(([^:/?#]+):)?(//([^/?#]*))?([^?#]*)(\?([^#]*))?(#(.*))?`,
/// with scheme = $2, authority = $4, path = $5, query = $7, fragment = $9.
pub open spec fn rfc_parse(r: Seq<u32>) -> Components {
    // $1 = `(([^:/?#]+):)?`, $2 = `[^:/?#]+`
    let k = scan_scheme(r, 0);
    let (scheme, i) = if k > 0 && k < r.len() && r[k as int] == 0x3A {
        (Some(part(r, 0, k)), k + 1)
    } else {
        (None, 0nat)
    };
    // $3 = `(//([^/?#]*))?`, $4 = `[^/?#]*`
    let (authority, j) = if i + 1 < r.len() && r[i as int] == 0x2F && r[i + 1 as int] == 0x2F {
        let e = scan_authority(r, i + 2);
        (Some(part(r, i + 2, e)), e)
    } else {
        (None, i)
    };
    // $5 = `[^?#]*`
    let e = scan_path(r, j);
    let path = part(r, j, e);
    // $6 = `(\?([^#]*))?`, $7 = `[^#]*`
    let (query, f) = if e < r.len() && r[e as int] == 0x3F {
        let g = scan_query(r, e + 1);
        (Some(part(r, e + 1, g)), g)
    } else {
        (None, e)
    };
    // $8 = `(#(.*))?`, $9 = `.*`
    let fragment = if f < r.len() && r[f as int] == 0x23 {
        Some(part(r, f + 1, r.len()))
    } else {
        None
    };
    Components { scheme: scheme, authority: authority, path: path, query: query, fragment: fragment }
}

// ---------------------------------------------------------------------
// §5.2.4 Remove Dot Segments.
// ---------------------------------------------------------------------

/// `s` begins with `prefix`.
pub open spec fn begins_with(s: Seq<u32>, prefix: Seq<u32>) -> bool {
    prefix.len() <= s.len() && s.subrange(0, prefix.len() as int) == prefix
}

/// `s` without its first `n` code points.
pub open spec fn after(s: Seq<u32>, n: nat) -> Seq<u32> {
    if n <= s.len() {
        s.subrange(n as int, s.len() as int)
    } else {
        seq![]
    }
}

/// The index of the last "/" in `s` before `i`, if any.
pub open spec fn last_slash(s: Seq<u32>, i: nat) -> Option<nat>
    decreases i
{
    if i == 0 || i > s.len() {
        None
    } else if s[i - 1] == 0x2F {
        Some((i - 1) as nat)
    } else {
        last_slash(s, (i - 1) as nat)
    }
}

/// Step 2C: "remove the last segment and its preceding "/" (if any) from
/// the output buffer".
pub open spec fn remove_last_segment(output: Seq<u32>) -> Seq<u32> {
    match last_slash(output, output.len()) {
        Some(k) => output.subrange(0, k as int),
        None => seq![],
    }
}

/// The end of the first path segment of `s` from `i`: "up to, but not
/// including, the next "/" character or the end of the input buffer".
pub open spec fn segment_end(s: Seq<u32>, i: nat) -> nat
    decreases s.len() - i
{
    if i < s.len() && s[i as int] != 0x2F {
        segment_end(s, i + 1)
    } else {
        i
    }
}

/// Step 2, "While the input buffer is not empty, loop as follows", with
/// the two buffers; then step 3, "the output buffer is returned".
pub open spec fn remove_dot_segments_loop(input: Seq<u32>, output: Seq<u32>) -> Seq<u32>
    decreases input.len() via remove_dot_segments_loop_decreases
{
    if input.len() == 0 {
        // 3. "Finally, the output buffer is returned as the result of
        //    remove_dot_segments."
        output
    } else if begins_with(input, seq![0x2Eu32, 0x2E, 0x2F]) {
        // A. "If the input buffer begins with a prefix of "../" or "./",
        //    then remove that prefix from the input buffer; otherwise,"
        remove_dot_segments_loop(after(input, 3), output)
    } else if begins_with(input, seq![0x2Eu32, 0x2F]) {
        remove_dot_segments_loop(after(input, 2), output)
    } else if begins_with(input, seq![0x2Fu32, 0x2E, 0x2F]) {
        // B. "if the input buffer begins with a prefix of "/./" or "/.",
        //    where "." is a complete path segment, then replace that prefix
        //    with "/" in the input buffer; otherwise,"
        remove_dot_segments_loop(seq![0x2Fu32] + after(input, 3), output)
    } else if input == seq![0x2Fu32, 0x2E] {
        remove_dot_segments_loop(seq![0x2Fu32], output)
    } else if begins_with(input, seq![0x2Fu32, 0x2E, 0x2E, 0x2F]) {
        // C. "if the input buffer begins with a prefix of "/../" or "/..",
        //    where ".." is a complete path segment, then replace that
        //    prefix with "/" in the input buffer and remove the last
        //    segment and its preceding "/" (if any) from the output buffer;
        //    otherwise,"
        remove_dot_segments_loop(seq![0x2Fu32] + after(input, 4), remove_last_segment(output))
    } else if input == seq![0x2Fu32, 0x2E, 0x2E] {
        remove_dot_segments_loop(seq![0x2Fu32], remove_last_segment(output))
    } else if input == seq![0x2Eu32] || input == seq![0x2Eu32, 0x2E] {
        // D. "if the input buffer consists only of "." or "..", then remove
        //    that from the input buffer; otherwise,"
        output
    } else {
        // E. "move the first path segment in the input buffer to the end of
        //    the output buffer, including the initial "/" character (if
        //    any) and any subsequent characters up to, but not including,
        //    the next "/" character or the end of the input buffer."
        let start: nat = if input[0] == 0x2F {
            1
        } else {
            0
        };
        let end = segment_end(input, start);
        remove_dot_segments_loop(after(input, end), output + part(input, 0, end))
    }
}

/// Termination of [`remove_dot_segments_loop`]: step E moves at least one
/// code point (a "/", or the first code point, which is not "/").
#[via_fn]
proof fn remove_dot_segments_loop_decreases(input: Seq<u32>, output: Seq<u32>) {
    if input.len() > 0 {
        lemma_segment_end_bounds(input, 0);
        lemma_segment_end_bounds(input, 1);
    }
}

/// `segment_end(s, i)` is between `i` and the end, and past `i` if `s[i]`
/// is not "/".
pub proof fn lemma_segment_end_bounds(s: Seq<u32>, i: nat)
    requires
        i <= s.len(),
    ensures
        i <= segment_end(s, i) <= s.len(),
        i < s.len() && s[i as int] != 0x2F ==> segment_end(s, i) > i,
    decreases s.len() - i,
{
    if i < s.len() && s[i as int] != 0x2F {
        lemma_segment_end_bounds(s, i + 1);
    }
}

/// §5.2.4 remove_dot_segments: "1. The input buffer is initialized with
/// the now-appended path components and the output buffer is initialized
/// to the empty string."
pub open spec fn remove_dot_segments(path: Seq<u32>) -> Seq<u32> {
    remove_dot_segments_loop(path, seq![])
}

// ---------------------------------------------------------------------
// §5.2.3 Merge Paths, §5.2.2 Transform References, §5.3 Recomposition.
// ---------------------------------------------------------------------

/// §5.2.3 merge(base, reference path).
pub open spec fn merge(base: Components, r_path: Seq<u32>) -> Seq<u32> {
    if base.authority is Some && base.path.len() == 0 {
        // "If the base URI has a defined authority component and an empty
        // path, then return a string consisting of "/" concatenated with
        // the reference's path; otherwise,"
        seq![0x2Fu32] + r_path
    } else {
        // "return a string consisting of the reference's path component
        // appended to all but the last segment of the base URI's path
        // (i.e., excluding any characters after the right-most "/" in the
        // base URI path, or excluding the entire base URI path if it does
        // not contain any "/" characters)."
        match last_slash(base.path, base.path.len()) {
            Some(k) => base.path.subrange(0, k as int + 1) + r_path,
            None => r_path,
        }
    }
}

/// §5.2.2 "Transform References", strict, from the parsed reference `r`
/// and base `base` to the target T.
pub open spec fn transform(r: Components, base: Components) -> Components {
    if r.scheme is Some {
        Components {
            scheme: r.scheme,
            authority: r.authority,
            path: remove_dot_segments(r.path),
            query: r.query,
            fragment: r.fragment,
        }
    } else if r.authority is Some {
        Components {
            scheme: base.scheme,
            authority: r.authority,
            path: remove_dot_segments(r.path),
            query: r.query,
            fragment: r.fragment,
        }
    } else if r.path.len() == 0 {
        Components {
            scheme: base.scheme,
            authority: base.authority,
            path: base.path,
            query: if r.query is Some {
                r.query
            } else {
                base.query
            },
            fragment: r.fragment,
        }
    } else if r.path[0] == 0x2F {
        Components {
            scheme: base.scheme,
            authority: base.authority,
            path: remove_dot_segments(r.path),
            query: r.query,
            fragment: r.fragment,
        }
    } else {
        Components {
            scheme: base.scheme,
            authority: base.authority,
            path: remove_dot_segments(merge(base, r.path)),
            query: r.query,
            fragment: r.fragment,
        }
    }
}

/// §5.3 Component Recomposition.
pub open spec fn recompose(t: Components) -> Seq<u32> {
    let result = match t.scheme {
        Some(s) => s + seq![0x3Au32],
        None => seq![],
    };
    let result = match t.authority {
        Some(a) => result + seq![0x2Fu32, 0x2F] + a,
        None => result,
    };
    let result = result + t.path;
    let result = match t.query {
        Some(q) => result + seq![0x3Fu32] + q,
        None => result,
    };
    match t.fragment {
        Some(f) => result + seq![0x23u32] + f,
        None => result,
    }
}

/// RFC 3986 reference resolution of the string `r` against the base URI
/// string `b`: parse both, transform, recompose.
pub open spec fn rfc_resolve(r: Seq<u32>, b: Seq<u32>) -> Seq<u32> {
    recompose(transform(rfc_parse(r), rfc_parse(b)))
}


// ---------------------------------------------------------------------
// The class where the two standards agree.
// ---------------------------------------------------------------------

/// An ASCII lower alpha (Infra §4.6).
pub open spec fn is_ascii_lower_alpha(c: u32) -> bool {
    0x61 <= c <= 0x7A
}

/// The base of the agreement class (see the module comment).
pub open spec fn rfc_base(base: Url) -> bool {
    &&& base.scheme.len() > 0
    &&& forall|k: int| 0 <= k < base.scheme.len() ==> is_ascii_lower_alpha(#[trigger] base.scheme[k])
    &&& !is_special_scheme(base.scheme)
    &&& base.username.len() == 0 && base.password.len() == 0
    &&& base.port is None && base.fragment is None
    &&& base.host matches Some(crate::host::spec::Host::Opaque(h)) && h.len() > 0 && (forall|k: int|
        0 <= k < h.len() ==> (is_ascii_lower_alpha(#[trigger] h[k]) || crate::host::spec::is_ascii_digit(h[k])))
    &&& base.path matches UrlPath::List(segs) && (forall|i: int| 0 <= i < segs.len() ==> super::runs::all_alphanumeric(
        #[trigger] segs[i],
    ))
    &&& base.query matches Some(q) ==> super::runs::all_alphanumeric(q)
}

/// A reference's path: "/" and the segments joined with "/" if
/// `absolute`, otherwise the segments joined with "/".
pub open spec fn ref_path(absolute: bool, segs: Seq<Seq<u32>>) -> Seq<u32> {
    if absolute {
        seq![0x2Fu32] + super::runs::join(segs)
    } else {
        super::runs::join(segs)
    }
}

/// `s`, then "?" and the query if there is one.
pub open spec fn with_query(s: Seq<u32>, query: Option<Seq<u32>>) -> Seq<u32> {
    match query {
        Some(q) => s + seq![0x3Fu32] + q,
        None => s,
    }
}

/// `s`, then "#" and the fragment if there is one.
pub open spec fn with_fragment(s: Seq<u32>, fragment: Option<Seq<u32>>) -> Seq<u32> {
    match fragment {
        Some(f) => s + seq![0x23u32] + f,
        None => s,
    }
}

/// A reference: path, optional query, optional fragment.
pub open spec fn ref_string(absolute: bool, segs: Seq<Seq<u32>>, query: Option<Seq<u32>>, fragment: Option<Seq<u32>>) -> Seq<u32> {
    with_fragment(with_query(ref_path(absolute, segs), query), fragment)
}

/// The references of the agreement class (see the module comment): every
/// segment is ASCII alphanumerics, "." or ".."; an absolute path is "/"
/// or starts with a non-empty segment (so it never starts with "//"); a
/// relative path is empty or starts with a non-empty segment; the query
/// and fragment are ASCII alphanumerics.
pub open spec fn rfc_reference(absolute: bool, segs: Seq<Seq<u32>>, query: Option<Seq<u32>>, fragment: Option<Seq<u32>>) -> bool {
    &&& forall|i: int| 0 <= i < segs.len() ==> super::runs::segment_ok(#[trigger] segs[i])
    &&& absolute ==> segs.len() > 0 && (segs.len() == 1 || segs[0].len() > 0)
    &&& (!absolute && segs.len() > 0) ==> segs[0].len() > 0
    &&& query matches Some(q) ==> super::runs::all_alphanumeric(q)
    &&& fragment matches Some(f) ==> super::runs::all_alphanumeric(f)
}

// ---------------------------------------------------------------------
// The WHATWG side: what the basic URL parser returns.
// ---------------------------------------------------------------------

/// base's path, as a list.
pub open spec fn base_segments(base: Url) -> Seq<Seq<u32>> {
    match base.path {
        UrlPath::List(l) => l,
        UrlPath::Opaque(_) => seq![],
    }
}

/// The URL the basic URL parser returns for a reference of the class.
pub open spec fn resolved_url(base: Url, absolute: bool, segs: Seq<Seq<u32>>, query: Option<Seq<u32>>, fragment: Option<Seq<u32>>) -> Url {
    if !absolute && segs.len() == 0 {
        Url {
            query: if query is Some {
                query
            } else {
                base.query
            },
            fragment: fragment,
            ..base
        }
    } else {
        Url {
            path: UrlPath::List(
                super::runs::path_model(
                    if absolute {
                        seq![]
                    } else {
                        super::runs::shorten_list(base_segments(base))
                    },
                    segs,
                ),
            ),
            query: query,
            fragment: fragment,
            ..base
        }
    }
}

/// The code points of a reference of the class are above U+0020 SPACE.
proof fn lemma_reference_chars(absolute: bool, segs: Seq<Seq<u32>>, query: Option<Seq<u32>>, fragment: Option<Seq<u32>>)
    requires
        rfc_reference(absolute, segs, query, fragment),
    ensures
        super::runs::no_c0_or_space(super::runs::join(segs)),
        super::runs::no_c0_or_space(ref_string(absolute, segs, query, fragment)),
{
    lemma_join_chars(segs);
    let p = ref_path(absolute, segs);
    assert(super::runs::no_c0_or_space(p));
    let pq = with_query(p, query);
    assert(super::runs::no_c0_or_space(pq)) by {
        if let Some(q) = query {
            assert forall|k: int| 0 <= k < pq.len() implies #[trigger] pq[k] > 0x20 by {
                if k >= p.len() + 1 {
                    assert(pq[k] == q[k - p.len() - 1]);
                }
            }
        }
    }
    let r = with_fragment(pq, fragment);
    assert(super::runs::no_c0_or_space(r)) by {
        if let Some(f) = fragment {
            assert forall|k: int| 0 <= k < r.len() implies #[trigger] r[k] > 0x20 by {
                if k >= pq.len() + 1 {
                    assert(r[k] == f[k - pq.len() - 1]);
                }
            }
        }
    }
}

/// `super::runs::join(segs)` holds segment code points and U+002F (/).
proof fn lemma_join_chars(segs: Seq<Seq<u32>>)
    requires
        forall|i: int| 0 <= i < segs.len() ==> super::runs::segment_ok(#[trigger] segs[i]),
    ensures
        forall|k: int| 0 <= k < super::runs::join(segs).len() ==> (is_ascii_alphanumeric(#[trigger] super::runs::join(segs)[k]) || super::runs::join(segs)[k]
            == 0x2E || super::runs::join(segs)[k] == 0x2F),
    decreases segs.len(),
{
    if segs.len() > 0 {
        let s = segs[0];
        assert(super::runs::segment_ok(s));
        assert forall|k: int| 0 <= k < s.len() implies (is_ascii_alphanumeric(#[trigger] s[k]) || s[k] == 0x2E) by {
            if !super::runs::all_alphanumeric(s) {
                assert(s == seq![0x2Eu32] || s == seq![0x2Eu32, 0x2E]);
            }
        }
        if segs.len() > 1 {
            let rest = segs.subrange(1, segs.len() as int);
            assert forall|i: int| 0 <= i < rest.len() implies super::runs::segment_ok(#[trigger] rest[i]) by {
                assert(rest[i] == segs[i + 1]);
            }
            lemma_join_chars(rest);
            let j = super::runs::join(segs);
            assert(j == s + seq![0x2Fu32] + super::runs::join(rest));
            assert forall|k: int| 0 <= k < j.len() implies (is_ascii_alphanumeric(#[trigger] j[k]) || j[k] == 0x2E
                || j[k] == 0x2F) by {
                if k > s.len() {
                    assert(j[k] == super::runs::join(rest)[k - s.len() - 1]);
                }
            }
        }
    }
}

/// `url` with the reference's query and fragment, where it has them.
pub open spec fn tail_url(url: Url, query: Option<Seq<u32>>, fragment: Option<Seq<u32>>) -> Url {
    Url {
        query: if query is Some {
            query
        } else {
            url.query
        },
        fragment: if fragment is Some {
            fragment
        } else {
            url.fragment
        },
        ..url
    }
}

/// The tail after the path (query, fragment) when the parser reaches it
/// at `e` in the Query, Fragment or no state.
proof fn lemma_tail(ctx: Ctx, url: Url, m: Machine, e: int, query: Option<Seq<u32>>, fragment: Option<Seq<u32>>)
    requires
        ctx.state_override is None,
        m.state is Path,
        0 <= e <= ctx.input.len(),
        ctx.input == with_fragment(with_query(ctx.input.subrange(0, e), query), fragment),
        query matches Some(q) ==> super::runs::all_alphanumeric(q),
        fragment matches Some(f) ==> super::runs::all_alphanumeric(f),
    ensures
        e == ctx.input.len() ==> query is None && fragment is None,
        (e < ctx.input.len() && ctx.input[e] == 0x3F) ==> run(
            ctx,
            Machine { url: Url { query: Some(seq![]), ..url }, buffer: seq![], state: State::Query, pointer: e + 1, ..m },
        ) == Some(tail_url(url, query, fragment)),
        (e < ctx.input.len() && ctx.input[e] == 0x23) ==> run(
            ctx,
            Machine { url: Url { fragment: Some(seq![]), ..url }, buffer: seq![], state: State::Fragment, pointer: e + 1, ..m },
        ) == Some(tail_url(url, query, fragment)),
        e < ctx.input.len() ==> (ctx.input[e] == 0x3F || ctx.input[e] == 0x23) && (ctx.input[e] == 0x23 ==> query is None),
{
    let input = ctx.input;
    let len = input.len() as int;
    let head = input.subrange(0, e);
    match (query, fragment) {
        (None, None) => {
            assert(input =~= head);
        },
        (Some(q), None) => {
            assert(input =~= head + seq![0x3Fu32] + q);
            assert(input.len() == e + 1 + q.len());
            assert(input[e] == 0x3F);
            let mq = Machine { url: Url { query: Some(seq![]), ..url }, buffer: seq![], state: State::Query, pointer: e + 1, ..m };
            assert(super::runs::alphanumeric_between(input, e + 1, len)) by {
                assert forall|k: int| e + 1 <= k < len implies is_ascii_alphanumeric(#[trigger] input[k]) by {
                    assert(input[k] == q[k - e - 1]);
                }
            }
            super::runs::lemma_alphanumeric_outside(input, e + 1, len);
            assert(super::runs::outside_all(Seq::<u32>::empty(), super::runs::query_set(mq.url)));
            super::runs::lemma_query_run(ctx, mq, seq![], len);
            assert(input.subrange(e + 1, len) =~= q);
            assert(Seq::<u32>::empty() + Seq::<u32>::empty() + q =~= q);
        },
        (Some(q), Some(f)) => {
            let ql = e + 1 + q.len();
            assert(input =~= head + seq![0x3Fu32] + q + seq![0x23u32] + f);
            assert(input.len() == ql + 1 + f.len());
            assert(input[e] == 0x3F);
            assert(input[ql] == 0x23);
            let mq = Machine { url: Url { query: Some(seq![]), ..url }, buffer: seq![], state: State::Query, pointer: e + 1, ..m };
            assert(super::runs::alphanumeric_between(input, e + 1, ql)) by {
                assert forall|k: int| e + 1 <= k < ql implies is_ascii_alphanumeric(#[trigger] input[k]) by {
                    assert(input[k] == q[k - e - 1]);
                }
            }
            assert(super::runs::alphanumeric_between(input, ql + 1, len)) by {
                assert forall|k: int| ql + 1 <= k < len implies is_ascii_alphanumeric(#[trigger] input[k]) by {
                    assert(input[k] == f[k - ql - 1]);
                }
            }
            super::runs::lemma_alphanumeric_outside(input, e + 1, ql);
            super::runs::lemma_alphanumeric_outside(input, ql + 1, len);
            assert(super::runs::outside_all(Seq::<u32>::empty(), super::runs::query_set(mq.url)));
            super::runs::lemma_query_run(ctx, mq, seq![], ql);
            assert(input.subrange(e + 1, ql) =~= q);
            assert(input.subrange(ql + 1, len) =~= f);
            assert(Seq::<u32>::empty() + Seq::<u32>::empty() + q =~= q);
        },
        (None, Some(f)) => {
            assert(input =~= head + seq![0x23u32] + f);
            assert(input.len() == e + 1 + f.len());
            assert(input[e] == 0x23);
            let mf = Machine { url: Url { fragment: Some(seq![]), ..url }, buffer: seq![], state: State::Fragment, pointer: e + 1, ..m };
            assert(super::runs::alphanumeric_between(input, e + 1, len)) by {
                assert forall|k: int| e + 1 <= k < len implies is_ascii_alphanumeric(#[trigger] input[k]) by {
                    assert(input[k] == f[k - e - 1]);
                }
            }
            super::runs::lemma_alphanumeric_outside(input, e + 1, len);
            super::runs::lemma_fragment_run(ctx, mf, seq![]);
            assert(Seq::<u32>::empty() + input.subrange(e + 1, len) =~= f);
        },
    }
}

/// The parser's context for a reference of the class.
pub open spec fn ref_ctx(r: Seq<u32>, base: Url, dp: crate::host::spec::DomainParser) -> Ctx {
    Ctx { input: r, base: Some(base), state_override: None, domain_parser: dp }
}

/// The initial machine (basic URL parser steps 4 to 8).
pub open spec fn start_machine() -> Machine {
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

/// The scheme start, scheme and no scheme states take a reference of the
/// class to the relative state at its first code point.
proof fn lemma_reference_start(base: Url, absolute: bool, segs: Seq<Seq<u32>>, query: Option<Seq<u32>>, fragment: Option<Seq<u32>>, dp: crate::host::spec::DomainParser)
    requires
        rfc_base(base),
        rfc_reference(absolute, segs, query, fragment),
    ensures
        ({
            let r = ref_string(absolute, segs, query, fragment);
            basic_url_parser(r, Some(base), dp) == run(
                ref_ctx(r, base, dp),
                Machine { state: State::Relative, ..start_machine() },
            )
        }),
{
    let r = ref_string(absolute, segs, query, fragment);
    let p = ref_path(absolute, segs);
    let j = super::runs::join(segs);
    lemma_reference_chars(absolute, segs, query, fragment);
    super::runs::lemma_prepared_identity(r);
    lemma_join_chars(segs);
    let ctx = ref_ctx(r, base, dp);
    let len = r.len() as int;
    let m0 = start_machine();
    assert(basic_url_parser(r, Some(base), dp) == run(ctx, m0));
    assert(r.subrange(0, p.len() as int) =~= p);
    let k: int = if segs.len() > 0 {
        segs[0].len() as int
    } else {
        0
    };
    if r.len() > 0 && is_ascii_alpha(r[0]) {
        lemma_reference_first_run(absolute, segs, query, fragment);
    }
    super::runs::lemma_no_scheme_start(ctx, m0, k);
    let m1 = super::runs::no_scheme_machine(m0);
    lemma_no_scheme_to_relative(ctx, m1);
}

/// If a reference of the class starts with an ASCII alpha, its path is
/// relative and its first segment is followed by "/", "?", "#" or the
/// end.
proof fn lemma_reference_first_run(absolute: bool, segs: Seq<Seq<u32>>, query: Option<Seq<u32>>, fragment: Option<Seq<u32>>)
    requires
        rfc_reference(absolute, segs, query, fragment),
        ref_string(absolute, segs, query, fragment).len() > 0,
        is_ascii_alpha(ref_string(absolute, segs, query, fragment)[0]),
    ensures
        ({
            let r = ref_string(absolute, segs, query, fragment);
            let k = segs[0].len() as int;
            &&& !absolute && segs.len() > 0
            &&& 1 <= k <= r.len()
            &&& forall|i: int| 0 <= i < k ==> super::runs::is_scheme_code_point(#[trigger] r[i])
            &&& k == r.len() || (r[k] != 0x3A && !super::runs::is_scheme_code_point(r[k]))
        }),
{
    let r = ref_string(absolute, segs, query, fragment);
    let p = ref_path(absolute, segs);
    let j = super::runs::join(segs);
    lemma_join_chars(segs);
    assert(r.subrange(0, p.len() as int) =~= p);
    assert(r == with_fragment(with_query(r.subrange(0, p.len() as int), query), fragment));
    if absolute {
        assert(r[0] == 0x2F);
    }
    if segs.len() == 0 {
        assert(p.len() == 0);
        assert(r[0] == 0x3F || r[0] == 0x23) by {
            match (query, fragment) {
                (Some(q), _) => assert(r[0] == with_query(p, query)[0]),
                (None, Some(f)) => {},
                (None, None) => {},
            }
        }
    }
    let k = segs[0].len() as int;
    if segs.len() > 1 {
        assert(j == segs[0] + seq![0x2Fu32] + super::runs::join(segs.subrange(1, segs.len() as int)));
    } else {
        assert(j == segs[0]);
    }
    assert forall|i: int| 0 <= i < k implies super::runs::is_scheme_code_point(#[trigger] r[i]) by {
        assert(r[i] == j[i]);
    }
    if k < r.len() {
        if segs.len() > 1 {
            assert(r[k] == j[k]);
        } else {
            lemma_tail_delimiter(r, k, query, fragment);
        }
    }
}

/// The code point after the path, if any, is "?" or "#".
pub proof fn lemma_tail_delimiter(r: Seq<u32>, e: int, query: Option<Seq<u32>>, fragment: Option<Seq<u32>>)
    requires
        0 <= e < r.len(),
        r == with_fragment(with_query(r.subrange(0, e), query), fragment),
    ensures
        r[e] == 0x3F || r[e] == 0x23,
        r[e] == 0x23 ==> query is None,
{
    let head = r.subrange(0, e);
    match (query, fragment) {
        (None, None) => {
            assert(r.len() == e);
        },
        (Some(q), None) => {
            assert(r[e] == (head + seq![0x3Fu32] + q)[e]);
        },
        (Some(q), Some(f)) => {
            assert(r[e] == (head + seq![0x3Fu32] + q + seq![0x23u32] + f)[e]);
        },
        (None, Some(f)) => {
            assert(r[e] == (head + seq![0x23u32] + f)[e]);
        },
    }
}

/// The no scheme state with a base that has a list path and is not
/// "file" goes to the relative state at the same code point.
proof fn lemma_no_scheme_to_relative(ctx: Ctx, m: Machine)
    requires
        m.state is NoScheme,
        m.pointer == 0,
        ctx.base matches Some(b) && b.path is List && b.scheme != file_str(),
    ensures
        run(ctx, m) == run(ctx, Machine { state: State::Relative, ..m }),
{
    reveal(state_step);
}

/// The relative state at the first code point, for a reference with an
/// empty path.
proof fn lemma_reference_empty_path(base: Url, query: Option<Seq<u32>>, fragment: Option<Seq<u32>>, dp: crate::host::spec::DomainParser)
    requires
        rfc_base(base),
        rfc_reference(false, seq![], query, fragment),
    ensures
        ({
            let r = ref_string(false, seq![], query, fragment);
            run(ref_ctx(r, base, dp), Machine { state: State::Relative, ..start_machine() }) == Some(
                resolved_url(base, false, seq![], query, fragment),
            )
        }),
{
    reveal(state_step);
    let r = ref_string(false, seq![], query, fragment);
    let ctx = ref_ctx(r, base, dp);
    let m2 = Machine { state: State::Relative, ..start_machine() };
    let u_copy = Url { scheme: base.scheme, ..base };
    assert(Url { scheme: base.scheme, ..new_url() } == Url { scheme: base.scheme, ..new_url() });
    let u_rel = Url { scheme: base.scheme, ..new_url() };
    let u = Url {
        username: base.username,
        password: base.password,
        host: base.host,
        port: base.port,
        path: base.path,
        query: base.query,
        ..u_rel
    };
    assert(u == Url { fragment: None, ..base });
    assert(super::runs::join(Seq::<Seq<u32>>::empty()) == Seq::<u32>::empty());
    assert(r.subrange(0, 0) =~= Seq::<u32>::empty());
    assert(r == with_fragment(with_query(r.subrange(0, 0), query), fragment));
    lemma_tail(ctx, u, Machine { state: State::Path, ..m2 }, 0, query, fragment);
    if r.len() > 0 {
        lemma_tail_delimiter(r, 0, query, fragment);
    }
}

/// The relative state at the first code point, for an absolute-path
/// reference.
proof fn lemma_reference_absolute(base: Url, segs: Seq<Seq<u32>>, query: Option<Seq<u32>>, fragment: Option<Seq<u32>>, dp: crate::host::spec::DomainParser)
    requires
        rfc_base(base),
        rfc_reference(true, segs, query, fragment),
    ensures
        ({
            let r = ref_string(true, segs, query, fragment);
            run(ref_ctx(r, base, dp), Machine { state: State::Relative, ..start_machine() }) == Some(
                resolved_url(base, true, segs, query, fragment),
            )
        }),
{
    let r = ref_string(true, segs, query, fragment);
    let ctx = ref_ctx(r, base, dp);
    let j = super::runs::join(segs);
    let p = ref_path(true, segs);
    let len = r.len() as int;
    lemma_join_chars(segs);
    assert(r.subrange(0, p.len() as int) =~= p);
    assert(r == with_fragment(with_query(r.subrange(0, p.len() as int), query), fragment));
    assert(r[0] == 0x2F);
    let m2 = Machine { state: State::Relative, ..start_machine() };
    let u_rel = Url { scheme: base.scheme, ..new_url() };
    let m3 = Machine { url: u_rel, state: State::RelativeSlash, pointer: 1, ..m2 };
    lemma_relative_slash_start(ctx, m2, m3);
    // Relative slash state: c is not U+002F (/).
    if segs[0].len() > 0 {
        if segs.len() > 1 {
            assert(j == segs[0] + seq![0x2Fu32] + super::runs::join(segs.subrange(1, segs.len() as int)));
        } else {
            assert(j == segs[0]);
        }
        assert(r[1] == j[0]);
    } else {
        assert(segs.len() == 1);
        assert(j == segs[0]);
        if 1 < len {
            assert(r.subrange(0, 1) =~= p);
            lemma_tail_delimiter(r, 1, query, fragment);
        }
    }
    let u_path = Url { username: base.username, password: base.password, host: base.host, port: base.port, ..u_rel };
    let m4 = Machine { url: u_path, state: State::Path, pointer: 1, ..m2 };
    lemma_relative_slash_to_path(ctx, m3, m4, base);
    assert(r.subrange(1, 1 + j.len() as int) =~= j);
    let e = 1 + j.len() as int;
    assert(r.subrange(0, e) =~= p);
    if e < len {
        lemma_tail_delimiter(r, e, query, fragment);
    }
    super::runs::lemma_segments_path_ok(segs);
    super::runs::lemma_path_run(ctx, m4, seq![], segs);
    lemma_tail(ctx, Url { path: UrlPath::List(super::runs::path_model(seq![], segs)), ..u_path }, m4, e, query, fragment);
    assert(Url { query: query, fragment: fragment, path: UrlPath::List(super::runs::path_model(seq![], segs)), ..u_path }
        == resolved_url(base, true, segs, query, fragment));
}

/// The relative state at "/" goes to the relative slash state.
proof fn lemma_relative_slash_start(ctx: Ctx, m2: Machine, m3: Machine)
    requires
        m2.state is Relative,
        m2.pointer == 0,
        ctx.input.len() > 0 && ctx.input[0] == 0x2F,
        ctx.base matches Some(b) && m3 == (Machine {
            url: Url { scheme: b.scheme, ..m2.url },
            state: State::RelativeSlash,
            pointer: 1,
            ..m2
        }),
    ensures
        run(ctx, m2) == run(ctx, m3),
{
    reveal(state_step);
}

/// The relative slash state of a non-special url at a code point that is
/// not "/" goes to the path state there.
proof fn lemma_relative_slash_to_path(ctx: Ctx, m3: Machine, m4: Machine, base: Url)
    requires
        m3.state is RelativeSlash,
        !is_special(m3.url),
        ctx.base == Some(base),
        0 <= m3.pointer <= ctx.input.len(),
        !(m3.pointer < ctx.input.len() && ctx.input[m3.pointer] == 0x2F),
        m3.pointer < ctx.input.len() || m3.pointer == ctx.input.len(),
        m4 == (Machine {
            url: Url { username: base.username, password: base.password, host: base.host, port: base.port, ..m3.url },
            state: State::Path,
            ..m3
        }),
    ensures
        run(ctx, m3) == run(ctx, m4),
{
    reveal(state_step);
}

/// The relative state at the first code point of a relative-path
/// reference.
proof fn lemma_reference_relative(base: Url, segs: Seq<Seq<u32>>, query: Option<Seq<u32>>, fragment: Option<Seq<u32>>, dp: crate::host::spec::DomainParser)
    requires
        rfc_base(base),
        rfc_reference(false, segs, query, fragment),
        segs.len() > 0,
    ensures
        ({
            let r = ref_string(false, segs, query, fragment);
            run(ref_ctx(r, base, dp), Machine { state: State::Relative, ..start_machine() }) == Some(
                resolved_url(base, false, segs, query, fragment),
            )
        }),
{
    let r = ref_string(false, segs, query, fragment);
    let ctx = ref_ctx(r, base, dp);
    let j = super::runs::join(segs);
    let len = r.len() as int;
    lemma_join_chars(segs);
    assert(r.subrange(0, j.len() as int) =~= j);
    assert(r == with_fragment(with_query(r.subrange(0, j.len() as int), query), fragment));
    if segs.len() > 1 {
        assert(j == segs[0] + seq![0x2Fu32] + super::runs::join(segs.subrange(1, segs.len() as int)));
    } else {
        assert(j == segs[0]);
    }
    assert(r[0] == j[0]);
    let m2 = Machine { state: State::Relative, ..start_machine() };
    let shortened = super::runs::shorten_list(base_segments(base));
    let u_path = Url { path: UrlPath::List(shortened), query: None, fragment: None, ..base };
    let m4 = Machine { url: u_path, state: State::Path, pointer: 0, ..m2 };
    lemma_relative_to_path(ctx, m2, m4, base);
    let e = j.len() as int;
    if e < len {
        lemma_tail_delimiter(r, e, query, fragment);
    }
    super::runs::lemma_segments_path_ok(segs);
    super::runs::lemma_path_run(ctx, m4, shortened, segs);
    lemma_tail(ctx, Url { path: UrlPath::List(super::runs::path_model(shortened, segs)), ..u_path }, m4, e, query, fragment);
    assert(Url { query: query, fragment: fragment, path: UrlPath::List(super::runs::path_model(shortened, segs)), ..u_path }
        == resolved_url(base, false, segs, query, fragment));
}

/// The relative state at a segment code point copies base and shortens
/// its path, then goes to the path state there.
proof fn lemma_relative_to_path(ctx: Ctx, m2: Machine, m4: Machine, base: Url)
    requires
        m2.state is Relative,
        m2.url == new_url(),
        m2.pointer == 0,
        rfc_base(base),
        ctx.base == Some(base),
        ctx.input.len() > 0,
        is_ascii_alphanumeric(ctx.input[0]) || ctx.input[0] == 0x2E,
        m4 == (Machine {
            url: Url { path: UrlPath::List(super::runs::shorten_list(base_segments(base))), query: None, fragment: None, ..base },
            state: State::Path,
            ..m2
        }),
    ensures
        run(ctx, m2) == run(ctx, m4),
{
    reveal(state_step);
    assert(base.scheme != file_str());
    let u = Url {
        username: base.username,
        password: base.password,
        host: base.host,
        port: base.port,
        path: base.path,
        query: None,
        ..Url { scheme: base.scheme, ..new_url() }
    };
    assert(shorten(u) == m4.url);
}

/// What the basic URL parser returns for a reference of the class.
proof fn lemma_whatwg_reference(
    base: Url,
    absolute: bool,
    segs: Seq<Seq<u32>>,
    query: Option<Seq<u32>>,
    fragment: Option<Seq<u32>>,
    dp: crate::host::spec::DomainParser,
)
    requires
        rfc_base(base),
        rfc_reference(absolute, segs, query, fragment),
    ensures
        basic_url_parser(ref_string(absolute, segs, query, fragment), Some(base), dp) == Some(
            resolved_url(base, absolute, segs, query, fragment),
        ),
{
    lemma_reference_start(base, absolute, segs, query, fragment, dp);
    if !absolute && segs.len() == 0 {
        assert(segs =~= Seq::<Seq<u32>>::empty());
        lemma_reference_empty_path(base, query, fragment, dp);
    } else if absolute {
        lemma_reference_absolute(base, segs, query, fragment, dp);
    } else {
        lemma_reference_relative(base, segs, query, fragment, dp);
    }
}

/// **Theorem.** For every base and reference of the agreement class and
/// every domain parser, the basic URL parser resolves the reference
/// against the base, and its serialization is RFC 3986's resolution of the
/// reference against the base's serialization.
pub proof fn lemma_resolution_agrees(
    base: Url,
    absolute: bool,
    segs: Seq<Seq<u32>>,
    query: Option<Seq<u32>>,
    fragment: Option<Seq<u32>>,
    dp: crate::host::spec::DomainParser,
)
    requires
        rfc_base(base),
        rfc_reference(absolute, segs, query, fragment),
    ensures
        ({
            let r = ref_string(absolute, segs, query, fragment);
            basic_url_parser(r, Some(base), dp) matches Some(u) && url_serializer(u, false) == rfc_resolve(
                r,
                url_serializer(base, false),
            )
        }),
{
    lemma_whatwg_reference(base, absolute, segs, query, fragment, dp);
    lemma_rfc_reference(base, absolute, segs, query, fragment);
}

// ---------------------------------------------------------------------
// The RFC side: what RFC 3986 resolution gives.
// ---------------------------------------------------------------------

/// `scan_scheme` stops at the first of ":", "/", "?", "#" at or after `i`.
proof fn lemma_scan_scheme(s: Seq<u32>, i: nat, k: nat)
    requires
        i <= k <= s.len(),
        forall|j: int| i <= j < k ==> !is_colon_slash_question_hash(#[trigger] s[j]),
        k == s.len() || is_colon_slash_question_hash(s[k as int]),
    ensures
        scan_scheme(s, i) == k,
    decreases k - i,
{
    if i < k {
        lemma_scan_scheme(s, i + 1, k);
    }
}

/// `scan_authority` stops at the first of "/", "?", "#" at or after `i`.
proof fn lemma_scan_authority(s: Seq<u32>, i: nat, k: nat)
    requires
        i <= k <= s.len(),
        forall|j: int| i <= j < k ==> !is_slash_question_hash(#[trigger] s[j]),
        k == s.len() || is_slash_question_hash(s[k as int]),
    ensures
        scan_authority(s, i) == k,
    decreases k - i,
{
    if i < k {
        lemma_scan_authority(s, i + 1, k);
    }
}

/// `scan_path` stops at the first of "?", "#" at or after `i`.
proof fn lemma_scan_path(s: Seq<u32>, i: nat, k: nat)
    requires
        i <= k <= s.len(),
        forall|j: int| i <= j < k ==> !is_question_hash(#[trigger] s[j]),
        k == s.len() || is_question_hash(s[k as int]),
    ensures
        scan_path(s, i) == k,
    decreases k - i,
{
    if i < k {
        lemma_scan_path(s, i + 1, k);
    }
}

/// `scan_query` stops at the first "#" at or after `i`.
proof fn lemma_scan_query(s: Seq<u32>, i: nat, k: nat)
    requires
        i <= k <= s.len(),
        forall|j: int| i <= j < k ==> #[trigger] s[j] != 0x23,
        k == s.len() || s[k as int] == 0x23,
    ensures
        scan_query(s, i) == k,
    decreases k - i,
{
    if i < k {
        lemma_scan_query(s, i + 1, k);
    }
}

/// The query and fragment parts of `head` + tail, as Appendix B reads
/// them, when `head` holds no "?" or "#" and the query has no "#": from the
/// end of `head`, the path ends there and the query and fragment are the
/// tail's.
proof fn lemma_parse_tail(s: Seq<u32>, j: nat, query: Option<Seq<u32>>, fragment: Option<Seq<u32>>)
    requires
        j <= s.len(),
        s == with_fragment(with_query(s.subrange(0, j as int), query), fragment),
        forall|k: int| 0 <= k < j ==> !is_question_hash(#[trigger] s[k]),
        query matches Some(q) ==> super::runs::all_alphanumeric(q),
        fragment matches Some(f) ==> super::runs::all_alphanumeric(f),
    ensures
        ({
            let e = scan_path(s, j);
            let (q, f) = if e < s.len() && s[e as int] == 0x3F {
                let g = scan_query(s, e + 1);
                (Some(part(s, e + 1, g)), g)
            } else {
                (None, e)
            };
            &&& e == j
            &&& q == query
            &&& (if f < s.len() && s[f as int] == 0x23 {
                Some(part(s, f + 1, s.len()))
            } else {
                None
            }) == fragment
        }),
{
    let head = s.subrange(0, j as int);
    match (query, fragment) {
        (None, None) => {
            assert(s =~= head);
            lemma_scan_path(s, j, j);
        },
        (Some(q), None) => {
            assert(s =~= head + seq![0x3Fu32] + q);
            assert(s[j as int] == 0x3F);
            lemma_scan_path(s, j, j);
            assert forall|k: int| j + 1 <= k < s.len() implies #[trigger] s[k] != 0x23 by {
                assert(s[k] == q[k - j - 1]);
            }
            lemma_scan_query(s, j + 1, s.len());
            assert(part(s, j + 1, s.len()) =~= q);
        },
        (Some(q), Some(f)) => {
            let g = j + 1 + q.len();
            assert(s =~= head + seq![0x3Fu32] + q + seq![0x23u32] + f);
            assert(s[j as int] == 0x3F);
            assert(s[g as int] == 0x23);
            lemma_scan_path(s, j, j);
            assert forall|k: int| j + 1 <= k < g implies #[trigger] s[k] != 0x23 by {
                assert(s[k] == q[k - j - 1]);
            }
            lemma_scan_query(s, j + 1, g);
            assert(part(s, j + 1, g) =~= q);
            assert(part(s, g + 1, s.len()) =~= f);
        },
        (None, Some(f)) => {
            assert(s =~= head + seq![0x23u32] + f);
            assert(s[j as int] == 0x23);
            lemma_scan_path(s, j, j);
            assert(part(s, j + 1, s.len()) =~= f);
        },
    }
}

/// Appendix B on a reference of the class: no scheme, no authority, the
/// path, query and fragment it was made of.
proof fn lemma_parse_reference(absolute: bool, segs: Seq<Seq<u32>>, query: Option<Seq<u32>>, fragment: Option<Seq<u32>>)
    requires
        rfc_reference(absolute, segs, query, fragment),
    ensures
        rfc_parse(ref_string(absolute, segs, query, fragment)) == (Components {
            scheme: None,
            authority: None,
            path: ref_path(absolute, segs),
            query: query,
            fragment: fragment,
        }),
{
    let r = ref_string(absolute, segs, query, fragment);
    let p = ref_path(absolute, segs);
    let j = super::runs::join(segs);
    lemma_join_chars(segs);
    assert(r.subrange(0, p.len() as int) =~= p);
    assert(r == with_fragment(with_query(r.subrange(0, p.len() as int), query), fragment));
    assert forall|k: int| 0 <= k < p.len() implies !is_question_hash(#[trigger] r[k]) by {
        assert(r[k] == p[k]);
        if absolute && k > 0 {
            assert(p[k] == j[k - 1]);
        }
    }
    // No scheme: the first of ":", "/", "?", "#" is not ":" (there is no ":").
    let k0 = scan_scheme(r, 0);
    assert forall|k: int| 0 <= k < r.len() implies #[trigger] r[k] != 0x3A by {
        lemma_reference_chars(absolute, segs, query, fragment);
        if k < p.len() {
            assert(r[k] == p[k]);
            if absolute && k > 0 {
                assert(p[k] == j[k - 1]);
            }
        } else {
            lemma_tail_chars(r, p.len() as int, k, query, fragment);
        }
    }
    // No authority: the path does not start with "//".
    if r.len() > 1 && r[0] == 0x2F && r[1] == 0x2F {
        assert(absolute);
        if segs[0].len() > 0 {
            if segs.len() > 1 {
                assert(j == segs[0] + seq![0x2Fu32] + super::runs::join(segs.subrange(1, segs.len() as int)));
            } else {
                assert(j == segs[0]);
            }
            assert(r[1] == j[0]);
        } else {
            assert(j == segs[0]);
            assert(p.len() == 1);
            lemma_tail_delimiter(r, 1, query, fragment);
        }
    }
    if p.len() < r.len() {
        lemma_tail_delimiter(r, p.len() as int, query, fragment);
    }
    lemma_scan_path(r, 0, p.len());
    lemma_parse_tail(r, p.len(), query, fragment);
    assert(part(r, 0, p.len()) =~= p);
}

/// The code points of a reference's query and fragment part are "?", "#"
/// and ASCII alphanumerics.
proof fn lemma_tail_chars(r: Seq<u32>, e: int, k: int, query: Option<Seq<u32>>, fragment: Option<Seq<u32>>)
    requires
        0 <= e <= k < r.len(),
        r == with_fragment(with_query(r.subrange(0, e), query), fragment),
        query matches Some(q) ==> super::runs::all_alphanumeric(q),
        fragment matches Some(f) ==> super::runs::all_alphanumeric(f),
    ensures
        r[k] == 0x3F || r[k] == 0x23 || is_ascii_alphanumeric(r[k]),
{
    let head = r.subrange(0, e);
    match (query, fragment) {
        (None, None) => {
            assert(r =~= head);
        },
        (Some(q), None) => {
            assert(r =~= head + seq![0x3Fu32] + q);
            if k > e {
                assert(r[k] == q[k - e - 1]);
            }
        },
        (Some(q), Some(f)) => {
            assert(r =~= head + seq![0x3Fu32] + q + seq![0x23u32] + f);
            if k > e && k < e + 1 + q.len() {
                assert(r[k] == q[k - e - 1]);
            } else if k > e + 1 + q.len() {
                assert(r[k] == f[k - e - 2 - q.len()]);
            }
        },
        (None, Some(f)) => {
            assert(r =~= head + seq![0x23u32] + f);
            if k > e {
                assert(r[k] == f[k - e - 1]);
            }
        },
    }
}

/// A path serialization of ASCII alphanumeric segments holds only "/" and
/// ASCII alphanumerics.
proof fn lemma_serialize_chars(l: Seq<Seq<u32>>)
    requires
        forall|i: int| 0 <= i < l.len() ==> super::runs::all_alphanumeric(#[trigger] l[i]),
    ensures
        forall|k: int| 0 <= k < serialize_segments(l).len() ==> (is_ascii_alphanumeric(#[trigger] serialize_segments(l)[k])
            || serialize_segments(l)[k] == 0x2F),
        l.len() > 0 ==> serialize_segments(l).len() > 0 && serialize_segments(l)[0] == 0x2F,
    decreases l.len(),
{
    if l.len() > 0 {
        let t = l.drop_last();
        assert forall|i: int| 0 <= i < t.len() implies super::runs::all_alphanumeric(#[trigger] t[i]) by {
            assert(t[i] == l[i]);
        }
        lemma_serialize_chars(t);
        let s = serialize_segments(l);
        let st = serialize_segments(t);
        assert(s == st + seq![0x2Fu32] + l.last());
        assert(super::runs::all_alphanumeric(l[l.len() - 1]));
        assert forall|k: int| 0 <= k < s.len() implies (is_ascii_alphanumeric(#[trigger] s[k]) || s[k] == 0x2F) by {
            if k > st.len() {
                assert(s[k] == l.last()[k - st.len() - 1]);
            }
        }
        if t.len() > 0 {
            assert(s[0] == st[0]);
        }
    }
}

/// The path serialization of a list, front first: "/", the first segment,
/// then the serialization of the rest.
pub proof fn lemma_serialize_front(l: Seq<Seq<u32>>)
    requires
        l.len() > 0,
    ensures
        serialize_segments(l) == seq![0x2Fu32] + l[0] + serialize_segments(l.subrange(1, l.len() as int)),
    decreases l.len(),
{
    if l.len() == 1 {
        assert(l.drop_last() =~= Seq::<Seq<u32>>::empty());
        assert(l.subrange(1, 1) =~= Seq::<Seq<u32>>::empty());
        assert(seq![0x2Fu32] + l[0] + Seq::<u32>::empty() =~= Seq::<u32>::empty() + seq![0x2Fu32] + l[0]);
    } else {
        let t = l.drop_last();
        lemma_serialize_front(t);
        let rest = l.subrange(1, l.len() as int);
        assert(rest.drop_last() =~= t.subrange(1, t.len() as int));
        assert(rest.last() == l.last());
        assert(serialize_segments(rest) == serialize_segments(rest.drop_last()) + seq![0x2Fu32] + rest.last());
        assert(seq![0x2Fu32] + l[0] + serialize_segments(rest) =~= serialize_segments(t) + seq![0x2Fu32] + l.last());
    }
}

/// `last_slash` finds the "/" at `k` when there is none between it and
/// `i`.
proof fn lemma_last_slash_at(s: Seq<u32>, k: nat, i: nat)
    requires
        k < i <= s.len(),
        s[k as int] == 0x2F,
        forall|j: int| k < j < i ==> #[trigger] s[j] != 0x2F,
    ensures
        last_slash(s, i) == Some(k),
    decreases i - k,
{
    if i - 1 > k {
        lemma_last_slash_at(s, k, (i - 1) as nat);
    }
}

/// `last_slash` finds none in a string with no "/" before `i`.
proof fn lemma_last_slash_none(s: Seq<u32>, i: nat)
    requires
        i <= s.len(),
        forall|j: int| 0 <= j < i ==> #[trigger] s[j] != 0x2F,
    ensures
        last_slash(s, i) is None,
    decreases i,
{
    if i > 0 {
        lemma_last_slash_none(s, (i - 1) as nat);
    }
}

/// The last "/" of a path serialization of ASCII alphanumeric segments is
/// the one before its last segment.
proof fn lemma_serialize_last_slash(l: Seq<Seq<u32>>)
    requires
        forall|i: int| 0 <= i < l.len() ==> super::runs::all_alphanumeric(#[trigger] l[i]),
    ensures
        l.len() > 0 ==> last_slash(serialize_segments(l), serialize_segments(l).len()) == Some(
            serialize_segments(l.drop_last()).len(),
        ),
        l.len() == 0 ==> last_slash(serialize_segments(l), serialize_segments(l).len()) is None,
{
    let s = serialize_segments(l);
    if l.len() > 0 {
        let st = serialize_segments(l.drop_last());
        let last = l.last();
        assert(super::runs::all_alphanumeric(l[l.len() - 1]));
        assert(s == st + seq![0x2Fu32] + last);
        assert forall|j: int| st.len() < j < s.len() implies #[trigger] s[j] != 0x2F by {
            assert(s[j] == last[j - st.len() - 1]);
        }
        lemma_last_slash_at(s, st.len(), s.len());
    } else {
        lemma_last_slash_none(s, 0);
    }
}

/// Step 2C on a path serialization is shortening the list.
proof fn lemma_remove_last_segment(l: Seq<Seq<u32>>)
    requires
        forall|i: int| 0 <= i < l.len() ==> super::runs::all_alphanumeric(#[trigger] l[i]),
    ensures
        remove_last_segment(serialize_segments(l)) == serialize_segments(super::runs::shorten_list(l)),
{
    lemma_serialize_last_slash(l);
    if l.len() > 0 {
        let st = serialize_segments(l.drop_last());
        assert(serialize_segments(l) == st + seq![0x2Fu32] + l.last());
        assert(serialize_segments(l).subrange(0, st.len() as int) =~= st);
    }
}

/// Step 2E on "/" + a segment of ASCII alphanumerics + the rest (empty or
/// starting with "/"): the segment moves to the output.
proof fn lemma_rds_move(s: Seq<u32>, rest: Seq<u32>, output: Seq<u32>)
    requires
        super::runs::all_alphanumeric(s),
        rest.len() == 0 || rest[0] == 0x2F,
    ensures
        remove_dot_segments_loop(seq![0x2Fu32] + s + rest, output) == remove_dot_segments_loop(rest, output + seq![0x2Fu32] + s),
{
    let input = seq![0x2Fu32] + s + rest;
    assert(input[0] == 0x2F);
    if s.len() > 0 {
        assert(input[1] == s[0]);
    } else if rest.len() > 0 {
        assert(input[1] == rest[0]);
    }
    assert(!begins_with(input, seq![0x2Eu32, 0x2E, 0x2F]) && !begins_with(input, seq![0x2Eu32, 0x2F])) by {
        if begins_with(input, seq![0x2Eu32, 0x2F]) {
            assert(input.subrange(0, 2)[0] == input[0]);
        }
        if begins_with(input, seq![0x2Eu32, 0x2E, 0x2F]) {
            assert(input.subrange(0, 3)[0] == input[0]);
        }
    }
    assert(!begins_with(input, seq![0x2Fu32, 0x2E, 0x2F]) && input != seq![0x2Fu32, 0x2E]) by {
        if begins_with(input, seq![0x2Fu32, 0x2E, 0x2F]) {
            assert(input.subrange(0, 3)[1] == input[1]);
        }
        if input == seq![0x2Fu32, 0x2E] {
            assert(input[1] == 0x2E);
        }
    }
    assert(!begins_with(input, seq![0x2Fu32, 0x2E, 0x2E, 0x2F]) && input != seq![0x2Fu32, 0x2E, 0x2E]) by {
        if begins_with(input, seq![0x2Fu32, 0x2E, 0x2E, 0x2F]) {
            assert(input.subrange(0, 4)[1] == input[1]);
        }
        if input == seq![0x2Fu32, 0x2E, 0x2E] {
            assert(input[1] == 0x2E);
        }
    }
    assert(input != seq![0x2Eu32] && input != seq![0x2Eu32, 0x2E]) by {
        if input == seq![0x2Eu32] || input == seq![0x2Eu32, 0x2E] {
            assert(input[0] == 0x2E);
        }
    }
    let end = 1 + s.len();
    assert(segment_end(input, 1) == end) by {
        lemma_segment_end_at(input, 1, end as nat);
    }
    assert(after(input, end as nat) =~= rest);
    assert(part(input, 0, end as nat) =~= seq![0x2Fu32] + s);
    assert(output + part(input, 0, end as nat) =~= output + seq![0x2Fu32] + s);
}

/// `segment_end` stops at the first "/" (or the end) at or after `i`.
proof fn lemma_segment_end_at(s: Seq<u32>, i: nat, k: nat)
    requires
        i <= k <= s.len(),
        forall|j: int| i <= j < k ==> #[trigger] s[j] != 0x2F,
        k == s.len() || s[k as int] == 0x2F,
    ensures
        segment_end(s, i) == k,
    decreases k - i,
{
    if i < k {
        lemma_segment_end_at(s, i + 1, k);
    }
}

/// Steps 2B and then 2E on "/." + the rest (empty or starting with "/").
proof fn lemma_rds_dot(rest: Seq<u32>, output: Seq<u32>)
    requires
        rest.len() == 0 || rest[0] == 0x2F,
    ensures
        remove_dot_segments_loop(seq![0x2Fu32, 0x2E] + rest, output) == if rest.len() == 0 {
            output + seq![0x2Fu32]
        } else {
            remove_dot_segments_loop(rest, output)
        },
{
    let input = seq![0x2Fu32, 0x2E] + rest;
    assert(input[0] == 0x2F && input[1] == 0x2E);
    assert(!begins_with(input, seq![0x2Eu32, 0x2E, 0x2F]) && !begins_with(input, seq![0x2Eu32, 0x2F])) by {
        if begins_with(input, seq![0x2Eu32, 0x2F]) {
            assert(input.subrange(0, 2)[0] == input[0]);
        }
        if begins_with(input, seq![0x2Eu32, 0x2E, 0x2F]) {
            assert(input.subrange(0, 3)[0] == input[0]);
        }
    }
    if rest.len() == 0 {
        assert(input =~= seq![0x2Fu32, 0x2E]);
        assert(!begins_with(input, seq![0x2Fu32, 0x2E, 0x2F]));
        lemma_rds_move(seq![], seq![], output);
        assert(seq![0x2Fu32] + Seq::<u32>::empty() + Seq::<u32>::empty() =~= seq![0x2Fu32]);
        assert(remove_dot_segments_loop(Seq::<u32>::empty(), output + seq![0x2Fu32] + Seq::<u32>::empty()) == output + seq![0x2Fu32] + Seq::<u32>::empty());
        assert(output + seq![0x2Fu32] + Seq::<u32>::empty() =~= output + seq![0x2Fu32]);
    } else {
        assert(input[2] == 0x2F);
        assert(input.subrange(0, 3) =~= seq![0x2Fu32, 0x2E, 0x2F]);
        assert(seq![0x2Fu32] + after(input, 3) =~= rest);
    }
}

/// Steps 2C and then 2E on "/.." + the rest (empty or starting with "/").
proof fn lemma_rds_dot_dot(rest: Seq<u32>, output: Seq<u32>)
    requires
        rest.len() == 0 || rest[0] == 0x2F,
    ensures
        remove_dot_segments_loop(seq![0x2Fu32, 0x2E, 0x2E] + rest, output) == if rest.len() == 0 {
            remove_last_segment(output) + seq![0x2Fu32]
        } else {
            remove_dot_segments_loop(rest, remove_last_segment(output))
        },
{
    let input = seq![0x2Fu32, 0x2E, 0x2E] + rest;
    assert(input[0] == 0x2F && input[1] == 0x2E && input[2] == 0x2E);
    assert(!begins_with(input, seq![0x2Eu32, 0x2E, 0x2F]) && !begins_with(input, seq![0x2Eu32, 0x2F])) by {
        if begins_with(input, seq![0x2Eu32, 0x2F]) {
            assert(input.subrange(0, 2)[0] == input[0]);
        }
        if begins_with(input, seq![0x2Eu32, 0x2E, 0x2F]) {
            assert(input.subrange(0, 3)[0] == input[0]);
        }
    }
    assert(!begins_with(input, seq![0x2Fu32, 0x2E, 0x2F])) by {
        if begins_with(input, seq![0x2Fu32, 0x2E, 0x2F]) {
            assert(input.subrange(0, 3)[2] == input[2]);
        }
    }
    assert(input != seq![0x2Fu32, 0x2E]);
    if rest.len() == 0 {
        assert(input =~= seq![0x2Fu32, 0x2E, 0x2E]);
        lemma_rds_move(seq![], seq![], remove_last_segment(output));
        assert(seq![0x2Fu32] + Seq::<u32>::empty() + Seq::<u32>::empty() =~= seq![0x2Fu32]);
        assert(remove_last_segment(output) + seq![0x2Fu32] + Seq::<u32>::empty() =~= remove_last_segment(output) + seq![0x2Fu32]);
    } else {
        assert(input[3] == 0x2F);
        assert(input.subrange(0, 4) =~= seq![0x2Fu32, 0x2E, 0x2E, 0x2F]);
        assert(seq![0x2Fu32] + after(input, 4) =~= rest);
    }
}

/// The dot segments of the class: an ASCII alphanumeric segment is
/// neither, "." is single-dot, ".." is double-dot (§4.1).
proof fn lemma_dot_segments(s: Seq<u32>)
    requires
        super::runs::segment_ok(s),
    ensures
        is_single_dot_segment(s) <==> s == seq![0x2Eu32],
        is_double_dot_segment(s) <==> s == seq![0x2Eu32, 0x2E],
{
    super::states_path::lemma_ascii_lowercase_string(s);
    let pct2e = seq![0x25u32, 0x32, 0x65];
    let dot_pct2e = seq![0x2Eu32, 0x25, 0x32, 0x65];
    let pct2e_dot = seq![0x25u32, 0x32, 0x65, 0x2E];
    let pct2e2 = seq![0x25u32, 0x32, 0x65, 0x25, 0x32, 0x65];
    super::states_path::lemma_ascii_lowercase_string(pct2e);
    super::states_path::lemma_ascii_lowercase_string(dot_pct2e);
    super::states_path::lemma_ascii_lowercase_string(pct2e_dot);
    super::states_path::lemma_ascii_lowercase_string(pct2e2);
    if super::runs::all_alphanumeric(s) {
        // Each pattern has a "%" or "." at index 0 or 1, which no ASCII
        // alphanumeric lowercases to.
        if is_ascii_case_insensitive_match(s, pct2e) {
            assert(ascii_lowercase_string(s)[0] == ascii_lowercase_string(pct2e)[0]);
            assert(is_ascii_alphanumeric(s[0]));
        }
        if is_ascii_case_insensitive_match(s, dot_pct2e) {
            assert(ascii_lowercase_string(s)[0] == ascii_lowercase_string(dot_pct2e)[0]);
            assert(is_ascii_alphanumeric(s[0]));
        }
        if is_ascii_case_insensitive_match(s, pct2e_dot) {
            assert(ascii_lowercase_string(s)[0] == ascii_lowercase_string(pct2e_dot)[0]);
            assert(is_ascii_alphanumeric(s[0]));
        }
        if is_ascii_case_insensitive_match(s, pct2e2) {
            assert(ascii_lowercase_string(s)[0] == ascii_lowercase_string(pct2e2)[0]);
            assert(is_ascii_alphanumeric(s[0]));
        }
        if s == seq![0x2Eu32] || s == seq![0x2Eu32, 0x2E] {
            assert(is_ascii_alphanumeric(s[0]));
        }
    } else if s == seq![0x2Eu32] {
        assert(ascii_lowercase_string(s).len() == 1);
    } else {
        assert(ascii_lowercase_string(s).len() == 2);
    }
}

/// remove_dot_segments over "/" + `super::runs::join(segs)` with the output holding
/// the serialization of `l` gives the serialization of the path state's
/// result.
proof fn lemma_rds_segments(l: Seq<Seq<u32>>, segs: Seq<Seq<u32>>)
    requires
        segs.len() > 0,
        forall|i: int| 0 <= i < segs.len() ==> super::runs::segment_ok(#[trigger] segs[i]),
        forall|i: int| 0 <= i < l.len() ==> super::runs::all_alphanumeric(#[trigger] l[i]),
    ensures
        remove_dot_segments_loop(seq![0x2Fu32] + super::runs::join(segs), serialize_segments(l)) == serialize_segments(super::runs::path_model(l, segs)),
        forall|i: int| 0 <= i < super::runs::path_model(l, segs).len() ==> super::runs::all_alphanumeric(#[trigger] super::runs::path_model(l, segs)[i]),
    decreases segs.len(),
{
    let s = segs[0];
    lemma_dot_segments(s);
    let out = serialize_segments(l);
    let (rest, slash) = if segs.len() > 1 {
        (seq![0x2Fu32] + super::runs::join(segs.subrange(1, segs.len() as int)), true)
    } else {
        (Seq::<u32>::empty(), false)
    };
    if segs.len() > 1 {
        assert(super::runs::join(segs) == s + seq![0x2Fu32] + super::runs::join(segs.subrange(1, segs.len() as int)));
    } else {
        assert(super::runs::join(segs) == s);
    }
    assert(seq![0x2Fu32] + super::runs::join(segs) =~= seq![0x2Fu32] + s + rest);
    let l2 = super::runs::seg_step(l, s, slash);
    let empty = Seq::<u32>::empty();
    assert(super::runs::all_alphanumeric(empty));
    lemma_remove_last_segment(l);
    if s == seq![0x2Eu32] {
        assert(seq![0x2Fu32] + s + rest =~= seq![0x2Fu32, 0x2E] + rest);
        lemma_rds_dot(rest, out);
        assert(l.push(empty).drop_last() =~= l);
        assert(serialize_segments(l.push(empty)) == out + seq![0x2Fu32] + empty);
        assert(out + seq![0x2Fu32] + empty =~= out + seq![0x2Fu32]);
    } else if s == seq![0x2Eu32, 0x2E] {
        assert(seq![0x2Fu32] + s + rest =~= seq![0x2Fu32, 0x2E, 0x2E] + rest);
        lemma_rds_dot_dot(rest, out);
        let sl = super::runs::shorten_list(l);
        assert(sl.push(empty).drop_last() =~= sl);
        assert(serialize_segments(sl.push(empty)) == serialize_segments(sl) + seq![0x2Fu32] + empty);
        assert(serialize_segments(sl) + seq![0x2Fu32] + empty =~= serialize_segments(sl) + seq![0x2Fu32]);
    } else {
        assert(super::runs::all_alphanumeric(s));
        lemma_rds_move(s, rest, out);
        assert(l.push(s).drop_last() =~= l);
        assert(serialize_segments(l.push(s)) == out + seq![0x2Fu32] + s);
    }
    assert(forall|i: int| 0 <= i < l2.len() ==> super::runs::all_alphanumeric(#[trigger] l2[i])) by {
        assert forall|i: int| 0 <= i < l2.len() implies super::runs::all_alphanumeric(#[trigger] l2[i]) by {
            if i < l.len() && i < l2.len() - 1 {
                assert(l2[i] == l[i]);
            } else if l2.len() > l.len() {
            }
        }
    }
    if segs.len() > 1 {
        let tail = segs.subrange(1, segs.len() as int);
        assert forall|i: int| 0 <= i < tail.len() implies super::runs::segment_ok(#[trigger] tail[i]) by {
            assert(tail[i] == segs[i + 1]);
        }
        lemma_rds_segments(l2, tail);
        assert(super::runs::path_model(l, segs) == super::runs::path_model(l2, tail));
    }
}

/// remove_dot_segments moves a serialization of ASCII alphanumeric
/// segments in front of the rest (empty or starting with "/") to the
/// output as it is.
proof fn lemma_rds_prefix(l: Seq<Seq<u32>>, x: Seq<u32>, output: Seq<u32>)
    requires
        forall|i: int| 0 <= i < l.len() ==> super::runs::all_alphanumeric(#[trigger] l[i]),
        x.len() == 0 || x[0] == 0x2F,
    ensures
        remove_dot_segments_loop(serialize_segments(l) + x, output) == remove_dot_segments_loop(x, output + serialize_segments(l)),
    decreases l.len(),
{
    if l.len() == 0 {
        assert(serialize_segments(l) + x =~= x);
        assert(output + serialize_segments(l) =~= output);
    } else {
        let tail = l.subrange(1, l.len() as int);
        assert forall|i: int| 0 <= i < tail.len() implies super::runs::all_alphanumeric(#[trigger] tail[i]) by {
            assert(tail[i] == l[i + 1]);
        }
        lemma_serialize_front(l);
        lemma_serialize_chars(tail);
        let rest = serialize_segments(tail) + x;
        if tail.len() > 0 {
            assert(rest[0] == serialize_segments(tail)[0]);
        } else {
            assert(rest =~= x);
        }
        assert(super::runs::all_alphanumeric(l[0]));
        lemma_rds_move(l[0], rest, output);
        assert(serialize_segments(l) + x =~= seq![0x2Fu32] + l[0] + rest);
        lemma_rds_prefix(tail, x, output + seq![0x2Fu32] + l[0]);
        assert(output + seq![0x2Fu32] + l[0] + serialize_segments(tail) =~= output + serialize_segments(l));
    }
}

/// The serialization of a base of the class: scheme, "://", host, path,
/// and "?" and the query if it has one.
proof fn lemma_serialize_base(base: Url)
    requires
        rfc_base(base),
    ensures
        ({
            let h = base.host->Some_0->Opaque_0;
            url_serializer(base, false) == with_query(
                base.scheme + seq![0x3Au32, 0x2F, 0x2F] + h + serialize_segments(base_segments(base)),
                base.query,
            )
        }),
{
    let h = base.host->Some_0->Opaque_0;
    assert(crate::host::spec::host_serializer(crate::host::spec::Host::Opaque(h)) == h);
    let o = base.scheme + seq![0x3Au32] + seq![0x2Fu32, 0x2F] + h;
    assert(o =~= base.scheme + seq![0x3Au32, 0x2F, 0x2F] + h);
}

/// The scans of Appendix B over a base serialization `s` = scheme ":" "//"
/// host path, then "?" query if there is one.
proof fn lemma_base_scans(scheme: Seq<u32>, h: Seq<u32>, sp: Seq<u32>, query: Option<Seq<u32>>)
    requires
        scheme.len() > 0,
        forall|k: int| 0 <= k < scheme.len() ==> is_ascii_lower_alpha(#[trigger] scheme[k]),
        forall|k: int| 0 <= k < h.len() ==> (is_ascii_lower_alpha(#[trigger] h[k]) || crate::host::spec::is_ascii_digit(h[k])),
        forall|k: int| 0 <= k < sp.len() ==> (is_ascii_alphanumeric(#[trigger] sp[k]) || sp[k] == 0x2F),
        sp.len() > 0 ==> sp[0] == 0x2F,
        query matches Some(q) ==> super::runs::all_alphanumeric(q),
    ensures
        ({
            let head = scheme + seq![0x3Au32, 0x2F, 0x2F] + h + sp;
            let s = with_query(head, query);
            let n = scheme.len();
            let a = n + 3;
            let e = a + h.len();
            let j = e + sp.len();
            &&& s.subrange(0, j as int) == head
            &&& s == with_fragment(with_query(s.subrange(0, j as int), query), None)
            &&& scan_scheme(s, 0) == n && n < s.len() && s[n as int] == 0x3A
            &&& s[n as int + 1] == 0x2F && s[n as int + 2] == 0x2F
            &&& scan_authority(s, a) == e
            &&& scan_path(s, e) == j
            &&& part(s, 0, n) == scheme && part(s, a, e) == h && part(s, e, j) == sp
            &&& forall|k: int| 0 <= k < j ==> !is_question_hash(#[trigger] s[k])
        }),
{
    let head = scheme + seq![0x3Au32, 0x2F, 0x2F] + h + sp;
    let s = with_query(head, query);
    let n = scheme.len();
    let a = n + 3;
    let e = a + h.len();
    let j = e + sp.len();
    assert(s.subrange(0, j as int) =~= head) by {
        match query {
            Some(q) => assert(s =~= head + seq![0x3Fu32] + q),
            None => {},
        }
    }
    assert(forall|k: int| 0 <= k < j ==> s[k] == head[k]);
    assert forall|k: int| 0 <= k < n implies !is_colon_slash_question_hash(#[trigger] s[k]) by {
        assert(head[k] == scheme[k]);
    }
    assert(head[n as int] == 0x3A && head[n as int + 1] == 0x2F && head[n as int + 2] == 0x2F);
    lemma_scan_scheme(s, 0, n);
    assert forall|k: int| a <= k < e implies !is_slash_question_hash(#[trigger] s[k]) by {
        assert(head[k] == h[k - a]);
    }
    if e < s.len() {
        if sp.len() > 0 {
            assert(head[e as int] == sp[0]);
        } else {
            lemma_tail_delimiter(s, e as int, query, None);
        }
    }
    lemma_scan_authority(s, a, e);
    assert forall|k: int| e <= k < j implies !is_question_hash(#[trigger] s[k]) by {
        assert(head[k] == sp[k - e]);
    }
    if j < s.len() {
        lemma_tail_delimiter(s, j as int, query, None);
    }
    lemma_scan_path(s, e, j);
    assert(part(s, 0, n) =~= scheme);
    assert(part(s, a, e) =~= h);
    assert(part(s, e, j) =~= sp);
    assert forall|k: int| 0 <= k < j implies !is_question_hash(#[trigger] s[k]) by {
        if k < n {
            assert(head[k] == scheme[k]);
        } else if a <= k < e {
            assert(head[k] == h[k - a]);
        } else if k >= e {
            assert(head[k] == sp[k - e]);
        }
    }
}

/// Appendix B on the serialization of a base of the class: its scheme,
/// host (the authority), path and query.
proof fn lemma_parse_base(base: Url)
    requires
        rfc_base(base),
    ensures
        rfc_parse(url_serializer(base, false)) == (Components {
            scheme: Some(base.scheme),
            authority: Some(base.host->Some_0->Opaque_0),
            path: serialize_segments(base_segments(base)),
            query: base.query,
            fragment: None,
        }),
{
    let h = base.host->Some_0->Opaque_0;
    let segs = base_segments(base);
    let sp = serialize_segments(segs);
    lemma_serialize_base(base);
    lemma_serialize_chars(segs);
    lemma_base_scans(base.scheme, h, sp, base.query);
    let s = url_serializer(base, false);
    let j = base.scheme.len() + 3 + h.len() + sp.len();
    lemma_parse_tail(s, j, base.query, None);
}

/// RFC 3986 resolution of a reference of the class against the
/// serialization of a base of the class is the serialization of the URL
/// the basic URL parser returns.
proof fn lemma_rfc_reference(base: Url, absolute: bool, segs: Seq<Seq<u32>>, query: Option<Seq<u32>>, fragment: Option<Seq<u32>>)
    requires
        rfc_base(base),
        rfc_reference(absolute, segs, query, fragment),
    ensures
        url_serializer(resolved_url(base, absolute, segs, query, fragment), false) == rfc_resolve(
            ref_string(absolute, segs, query, fragment),
            url_serializer(base, false),
        ),
{
    let r = ref_string(absolute, segs, query, fragment);
    let h = base.host->Some_0->Opaque_0;
    let bsegs = base_segments(base);
    lemma_parse_reference(absolute, segs, query, fragment);
    lemma_parse_base(base);
    let rc = rfc_parse(r);
    let bc = rfc_parse(url_serializer(base, false));
    let t = transform(rc, bc);
    let u = resolved_url(base, absolute, segs, query, fragment);
    let j = super::runs::join(segs);
    lemma_join_chars(segs);
    assert(forall|i: int| 0 <= i < bsegs.len() ==> super::runs::all_alphanumeric(#[trigger] bsegs[i]));
    // T's path is the serialization of u's path.
    if !absolute && segs.len() == 0 {
        assert(ref_path(absolute, segs).len() == 0);
        assert(t.path == serialize_segments(bsegs));
        assert(u.path == base.path);
    } else if absolute {
        assert(ref_path(absolute, segs)[0] == 0x2F);
        lemma_rds_segments(seq![], segs);
        assert(serialize_segments(Seq::<Seq<u32>>::empty()) == Seq::<u32>::empty());
        assert(t.path == serialize_segments(super::runs::path_model(seq![], segs)));
    } else {
        if segs.len() > 1 {
            assert(j == segs[0] + seq![0x2Fu32] + super::runs::join(segs.subrange(1, segs.len() as int)));
        } else {
            assert(j == segs[0]);
        }
        assert(ref_path(absolute, segs)[0] == segs[0][0]);
        assert(super::runs::segment_ok(segs[0]));
        assert(segs[0][0] != 0x2F) by {
            if !super::runs::all_alphanumeric(segs[0]) {
                assert(segs[0][0] == 0x2E);
            }
        }
        let l = super::runs::shorten_list(bsegs);
        assert forall|i: int| 0 <= i < l.len() implies super::runs::all_alphanumeric(#[trigger] l[i]) by {
            assert(l[i] == bsegs[i]);
        }
        lemma_serialize_last_slash(bsegs);
        let merged = merge(bc, j);
        if bsegs.len() > 0 {
            let st = serialize_segments(bsegs.drop_last());
            assert(serialize_segments(bsegs) == st + seq![0x2Fu32] + bsegs.last());
            assert(serialize_segments(bsegs).subrange(0, st.len() as int + 1) =~= st + seq![0x2Fu32]);
            assert(merged =~= serialize_segments(l) + (seq![0x2Fu32] + j));
        } else {
            assert(serialize_segments(bsegs).len() == 0);
            assert(merged =~= serialize_segments(l) + (seq![0x2Fu32] + j));
        }
        lemma_rds_prefix(l, seq![0x2Fu32] + j, seq![]);
        assert(Seq::<u32>::empty() + serialize_segments(l) =~= serialize_segments(l));
        lemma_rds_segments(l, segs);
        assert(t.path == serialize_segments(super::runs::path_model(l, segs)));
    }
    assert(crate::host::spec::host_serializer(crate::host::spec::Host::Opaque(h)) == h);
    assert(url_serializer(u, false) =~= recompose(t));
}

} // verus!
