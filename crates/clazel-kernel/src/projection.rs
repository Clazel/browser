//! The jar seen from one cookie root (item 2.11): what retrieval, storage
//! and the passing of time do to the unexpired cookies of a root depends on
//! nothing else in the jar. These are the facts `theorem_cookie_noninterference`
//! builds on, on top of `clazel-cookie`'s frame and within-root lemmas
//! (item 2.9), which say what other roots' operations do *not* change.
//!
//! `live_root(jar, now, root)` is what a renderer on `root`'s hosts can
//! depend on of the jar at time `now`: its unexpired cookies, in order.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The unexpired cookies of `jar` under `root`.
pub open spec fn live_root(rules: Seq<clazel_psl::spec::Rule>, jar: Seq<clazel_cookie::storage::spec::Cookie>, now: int, root: clazel_cookie::matching::spec::CanonicalHost) -> Seq<clazel_cookie::storage::spec::Cookie> {
    clazel_cookie::storage::spec::cookies_of_root(rules, clazel_cookie::storage::spec::evict_expired(jar, now), root)
}

// ---------------------------------------------------------------------
// Filters and maps.
// ---------------------------------------------------------------------

/// If `p` implies `q` on the elements, filtering by `p` is filtering by `q`
/// and then by `p`.
pub proof fn lemma_filter_implies<A>(s: Seq<A>, p: spec_fn(A) -> bool, q: spec_fn(A) -> bool)
    requires
        forall|i: int| 0 <= i < s.len() && p(#[trigger] s[i]) ==> q(s[i]),
    ensures
        s.filter(p) == s.filter(q).filter(p),
    decreases s.len(),
{
    reveal(Seq::filter);
    if s.len() > 0 {
        let t = s.drop_last();
        let x = s.last();
        assert forall|i: int| 0 <= i < t.len() && p(#[trigger] t[i]) implies q(t[i]) by {
            assert(s[i] == t[i]);
        }
        lemma_filter_implies(t, p, q);
        assert(s == t.push(x));
        assert(s[s.len() - 1] == x);
        clazel_cookie::storage::lemmas::lemma_filter_push(t, x, p);
        clazel_cookie::storage::lemmas::lemma_filter_push(t, x, q);
        if q(x) {
            clazel_cookie::storage::lemmas::lemma_filter_push(t.filter(q), x, p);
        }
        if p(x) {
            assert(q(x));
        }
    }
}

/// Filtering after mapping a function that does not change `p` is mapping
/// after filtering.
pub proof fn lemma_map_filter<A>(s: Seq<A>, f: spec_fn(A) -> A, p: spec_fn(A) -> bool)
    requires
        forall|c: A| #[trigger] p(f(c)) == p(c),
    ensures
        s.map_values(f).filter(p) == s.filter(p).map_values(f),
    decreases s.len(),
{
    reveal(Seq::filter);
    if s.len() > 0 {
        let t = s.drop_last();
        let x = s.last();
        lemma_map_filter(t, f, p);
        assert(s == t.push(x));
        assert(s.map_values(f).drop_last() =~= t.map_values(f));
        assert(s.map_values(f).last() == f(x));
        if p(x) {
            assert(s.filter(p) == t.filter(p).push(x));
            assert(t.filter(p).push(x).map_values(f) =~= t.filter(p).map_values(f).push(f(x)));
        }
    }
}

/// Removing from a sequence an element that `p` accepts, at `i`: the filter
/// loses the element at the number of accepted elements before `i`.
pub proof fn lemma_filter_remove_at<A>(s: Seq<A>, i: int, p: spec_fn(A) -> bool)
    requires
        0 <= i < s.len(),
        p(s[i]),
    ensures
        ({
            let k = s.subrange(0, i).filter(p).len() as int;
            0 <= k < s.filter(p).len() && s.filter(p)[k] == s[i] && s.remove(i).filter(p) == s.filter(p).remove(k) && (forall|m: int|
                0 <= m < k ==> s.filter(p)[m] == s.subrange(0, i).filter(p)[m])
        }),
{
    let a = s.subrange(0, i);
    let m = seq![s[i]];
    let b = s.subrange(i + 1, s.len() as int);
    assert(s =~= a + m + b);
    assert(s.remove(i) =~= a + b);
    Seq::<A>::filter_distributes_over_add(a + m, b, p);
    Seq::<A>::filter_distributes_over_add(a, m, p);
    Seq::<A>::filter_distributes_over_add(a, b, p);
    reveal(Seq::filter);
    assert(m.filter(p) =~= m) by {
        assert(m =~= Seq::<A>::empty().push(s[i]));
        clazel_cookie::storage::lemmas::lemma_filter_push(Seq::<A>::empty(), s[i], p);
    }
    let fa = a.filter(p);
    let fb = b.filter(p);
    assert(s.filter(p) =~= fa + m + fb);
    assert(s.remove(i).filter(p) =~= fa + fb);
    let k = fa.len() as int;
    assert((fa + m + fb)[k] == s[i]);
    assert((fa + m + fb).remove(k) =~= fa + fb);
    assert forall|q: int| 0 <= q < k implies s.filter(p)[q] == s.subrange(0, i).filter(p)[q] by {
        assert((fa + m + fb)[q] == fa[q]);
    }
}

// ---------------------------------------------------------------------
// live_root helpers.
// ---------------------------------------------------------------------

/// A jar whose root-`root` cookies are those of `jar` after expiry has the
/// same unexpired cookies under `root`.
pub proof fn lemma_live_root_from_root(rules: Seq<clazel_psl::spec::Rule>, x: Seq<clazel_cookie::storage::spec::Cookie>, jar: Seq<clazel_cookie::storage::spec::Cookie>, now: int, root: clazel_cookie::matching::spec::CanonicalHost)
    requires
        clazel_cookie::storage::spec::cookies_of_root(rules, x, root) == clazel_cookie::storage::spec::cookies_of_root(rules, clazel_cookie::storage::spec::evict_expired(jar, now), root),
    ensures
        live_root(rules, x, now, root) == live_root(rules, jar, now, root),
{
    let ne = clazel_cookie::storage::spec::not_expired(now);
    let p = clazel_cookie::storage::spec::in_root(rules, root);
    // live_root(x) = x.filter(ne).filter(p) = x.filter(p).filter(ne).
    clazel_cookie::storage::lemmas::lemma_filter_commute(x, ne, p);
    // = jar.filter(ne).filter(p).filter(ne) = jar.filter(ne).filter(ne).filter(p).
    let live = jar.filter(ne);
    clazel_cookie::storage::lemmas::lemma_filter_commute(live, p, ne);
    clazel_cookie::storage::lemmas::lemma_filter_idempotent(jar, ne);
}

/// What an unexpired root's cookies become at a later time.
pub proof fn lemma_live_root_later(rules: Seq<clazel_psl::spec::Rule>, j: Seq<clazel_cookie::storage::spec::Cookie>, now: int, now2: int, root: clazel_cookie::matching::spec::CanonicalHost)
    requires
        now <= now2,
    ensures
        live_root(rules, j, now2, root) == live_root(rules, j, now, root).filter(clazel_cookie::storage::spec::not_expired(now2)),
{
    let ne = clazel_cookie::storage::spec::not_expired(now);
    let ne2 = clazel_cookie::storage::spec::not_expired(now2);
    let p = clazel_cookie::storage::spec::in_root(rules, root);
    assert forall|i: int| 0 <= i < j.len() && ne2(#[trigger] j[i]) implies ne(j[i]) by {}
    lemma_filter_implies(j, ne2, ne);
    // j.filter(ne2) = j.filter(ne).filter(ne2); then commute with p.
    clazel_cookie::storage::lemmas::lemma_filter_commute(j.filter(ne), ne2, p);
}

/// Expiry commutes: the unexpired cookies of a root after eviction.
pub proof fn lemma_live_root_evict(rules: Seq<clazel_psl::spec::Rule>, j: Seq<clazel_cookie::storage::spec::Cookie>, now: int, root: clazel_cookie::matching::spec::CanonicalHost)
    ensures
        live_root(rules, clazel_cookie::storage::spec::evict_expired(j, now), now, root) == live_root(rules, j, now, root),
{
    clazel_cookie::storage::lemmas::lemma_filter_idempotent(j, clazel_cookie::storage::spec::not_expired(now));
}

// ---------------------------------------------------------------------
// What other roots' cookie calls leave alone.
// ---------------------------------------------------------------------

/// Another root's retrieval leaves this root's unexpired cookies as they were.
pub proof fn lemma_foreign_retrieval(
    rules: Seq<clazel_psl::spec::Rule>,
    jar: Seq<clazel_cookie::storage::spec::Cookie>,
    url: clazel_cookie::storage::spec::RequestUrl,
    ctx: clazel_cookie::storage::spec::RequestContext,
    now: int,
    host: clazel_cookie::matching::spec::CanonicalHost,
    other: clazel_cookie::matching::spec::CanonicalHost,
)
    requires
        url.host == Some(host),
        other != clazel_cookie::storage::spec::cookie_root(rules, host),
        clazel_cookie::storage::isolation::jar_domains_nonempty(jar),
    ensures
        live_root(rules, clazel_cookie::storage::spec::jar_after_retrieval(rules, jar, url, ctx, now), now, other) == live_root(rules, jar, now, other),
{
    clazel_cookie::storage::isolation::lemma_retrieve_frame(rules, jar, url, ctx, now, host, other);
    lemma_live_root_from_root(rules, clazel_cookie::storage::spec::jar_after_retrieval(rules, jar, url, ctx, now), jar, now, other);
}

/// Another root's storage leaves this root's unexpired cookies as they were.
pub proof fn lemma_foreign_store(
    rules: Seq<clazel_psl::spec::Rule>,
    jar: Seq<clazel_cookie::storage::spec::Cookie>,
    s: Seq<u8>,
    url: clazel_cookie::storage::spec::RequestUrl,
    ctx: clazel_cookie::storage::spec::RequestContext,
    now: int,
    host: clazel_cookie::matching::spec::CanonicalHost,
    other: clazel_cookie::matching::spec::CanonicalHost,
)
    requires
        url.host == Some(host),
        other != clazel_cookie::storage::spec::cookie_root(rules, host),
    ensures
        live_root(rules, clazel_cookie::storage::spec::store_a_set_cookie_string(rules, jar, s, url, ctx, now), now, other) == live_root(rules, jar, now, other),
{
    match clazel_cookie::set_cookie::spec::parse_a_set_cookie_string(s, url.path, now) {
        None => {
            lemma_live_root_evict(rules, jar, now, other);
        },
        Some(received) => {
            clazel_cookie::storage::isolation::lemma_store_frame(rules, jar, url, ctx, received, now, host, other);
            lemma_live_root_from_root(rules, clazel_cookie::storage::spec::store_a_set_cookie_string(rules, jar, s, url, ctx, now), jar, now, other);
        },
    }
}

/// A tick leaves two jars that agreed on a root's unexpired cookies agreeing.
pub proof fn lemma_tick_agree(rules: Seq<clazel_psl::spec::Rule>, ja: Seq<clazel_cookie::storage::spec::Cookie>, jb: Seq<clazel_cookie::storage::spec::Cookie>, now: int, now2: int, root: clazel_cookie::matching::spec::CanonicalHost)
    requires
        now <= now2,
        live_root(rules, ja, now, root) == live_root(rules, jb, now, root),
    ensures
        live_root(rules, clazel_cookie::storage::spec::evict_expired(ja, now2), now2, root) == live_root(rules, clazel_cookie::storage::spec::evict_expired(jb, now2), now2, root),
{
    lemma_live_root_evict(rules, ja, now2, root);
    lemma_live_root_evict(rules, jb, now2, root);
    lemma_live_root_later(rules, ja, now, now2, root);
    lemma_live_root_later(rules, jb, now, now2, root);
}

} // verus!
