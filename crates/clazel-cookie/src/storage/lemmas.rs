//! Facts proven about [`super::spec`]. They are evidence that the
//! transcription is right (here: that storing a cookie touches only its own
//! root), not part of what the implementation must meet.
//!
//! What is proven here does not need `clazel-psl`'s root lemmas:
//! `lemma_store_frame_of_new_root` and `lemma_retrieve_frame_of_root` say that
//! storing a cookie (retrieving for a host) changes only the cookies under
//! the root of the new cookie (the host's root). The isolation lemmas
//! proper (`lemma_store_within_root`, `lemma_retrieve_within_root`,
//! `lemma_store_frame`, `lemma_retrieve_frame`, `lemma_store_bounds`) are in
//! [`super::isolation`], which builds on these.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------
// Filters.
// ---------------------------------------------------------------------

/// Filtering after a push: the pushed element is kept if `p` holds of it.
pub proof fn lemma_filter_push<A>(s: Seq<A>, x: A, p: spec_fn(A) -> bool)
    ensures
        s.push(x).filter(p) == (if p(x) {
            s.filter(p).push(x)
        } else {
            s.filter(p)
        }),
{
    reveal(Seq::filter);
    assert(s.push(x).drop_last() == s);
    assert(s.push(x).last() == x);
}

/// Filtering by `p` and then `q` is filtering by `q` and then `p`.
pub proof fn lemma_filter_commute<A>(s: Seq<A>, p: spec_fn(A) -> bool, q: spec_fn(A) -> bool)
    ensures
        s.filter(p).filter(q) == s.filter(q).filter(p),
    decreases s.len(),
{
    reveal(Seq::filter);
    if s.len() > 0 {
        let t = s.drop_last();
        let x = s.last();
        lemma_filter_commute(t, p, q);
        assert(s == t.push(x));
        lemma_filter_push(t, x, p);
        lemma_filter_push(t, x, q);
        if p(x) {
            lemma_filter_push(t.filter(p), x, q);
        }
        if q(x) {
            lemma_filter_push(t.filter(q), x, p);
        }
    }
}

/// Filtering twice by the same predicate is filtering once.
pub proof fn lemma_filter_idempotent<A>(s: Seq<A>, q: spec_fn(A) -> bool)
    ensures
        s.filter(q).filter(q) == s.filter(q),
    decreases s.len(),
{
    reveal(Seq::filter);
    if s.len() > 0 {
        let t = s.drop_last();
        let x = s.last();
        lemma_filter_idempotent(t, q);
        assert(s == t.push(x));
        lemma_filter_push(t, x, q);
        if q(x) {
            lemma_filter_push(t.filter(q), x, q);
        }
    }
}

/// Removing an element that `p` rejects does not change the filter.
pub proof fn lemma_filter_remove_rejected<A>(s: Seq<A>, i: int, p: spec_fn(A) -> bool)
    requires
        0 <= i < s.len(),
        !p(s[i]),
    ensures
        s.remove(i).filter(p) == s.filter(p),
{
    let a = s.subrange(0, i);
    let m = seq![s[i]];
    let b = s.subrange(i + 1, s.len() as int);
    assert(s =~= a + m + b);
    assert(s.remove(i) == a + b);
    Seq::<A>::filter_distributes_over_add(a + m, b, p);
    Seq::<A>::filter_distributes_over_add(a, m, p);
    Seq::<A>::filter_distributes_over_add(a, b, p);
    assert(m =~= Seq::<A>::empty().push(s[i]));
    lemma_filter_push(Seq::<A>::empty(), s[i], p);
    reveal(Seq::filter);
    assert(Seq::<A>::empty().filter(p) == Seq::<A>::empty());
    assert(m.filter(p) =~= Seq::<A>::empty());
    assert(a.filter(p) + Seq::<A>::empty() =~= a.filter(p));
}

// ---------------------------------------------------------------------
// Eviction and insertion touch only the root they work on.
// ---------------------------------------------------------------------

/// The victim of [`victim_from`] is a cookie of the root, before `n`.
pub proof fn lemma_victim_from_in_root(
    rules: Seq<clazel_psl::spec::Rule>,
    jar: Seq<Cookie>,
    root: crate::matching::spec::CanonicalHost,
    n: nat,
)
    requires
        n <= jar.len(),
    ensures
        victim_from(rules, jar, root, n) matches Some(j) ==> (0 <= j < n && cookie_root_of(rules, jar[j]) == root),
    decreases n,
{
    if n > 0 {
        lemma_victim_from_in_root(rules, jar, root, (n - 1) as nat);
    }
}

/// [`evict_over_limit`] for `root` leaves the cookies of every other root
/// as they were (and in the same order).
pub proof fn lemma_evict_over_limit_frame(
    rules: Seq<clazel_psl::spec::Rule>,
    jar: Seq<Cookie>,
    root: crate::matching::spec::CanonicalHost,
    other: crate::matching::spec::CanonicalHost,
)
    requires
        other != root,
    ensures
        cookies_of_root(rules, evict_over_limit(rules, jar, root), other) == cookies_of_root(rules, jar, other),
    decreases jar.len(),
{
    if root_count(rules, jar, root) > max_cookies_per_root() {
        lemma_victim_from_in_root(rules, jar, root, jar.len());
        match victim_from(rules, jar, root, jar.len()) {
            Some(i) => {
                if 0 <= i < jar.len() {
                    jar.remove_ensures(i);
                    lemma_filter_remove_rejected(jar, i, in_root(rules, other));
                    lemma_evict_over_limit_frame(rules, jar.remove(i), root, other);
                }
            },
            None => {},
        }
    }
}

/// The old-cookie found has the same key as the new one.
pub proof fn lemma_find_old_cookie_from(jar: Seq<Cookie>, new: Cookie, i: nat)
    ensures
        find_old_cookie_from(jar, new, i) matches Some(j) ==> (0 <= j < jar.len() && same_key(jar[j], new)),
    decreases jar.len() - i,
{
    if i < jar.len() && !same_key(jar[i as int], new) {
        lemma_find_old_cookie_from(jar, new, i + 1);
    }
}

/// Inserting a cookie of root `r` into a jar leaves the cookies of any
/// other root as they were: the old-cookie it replaces has the new
/// cookie's domain, hence its root.
pub proof fn lemma_insert_a_cookie_frame(
    rules: Seq<clazel_psl::spec::Rule>,
    jar: Seq<Cookie>,
    new: Cookie,
    other: crate::matching::spec::CanonicalHost,
)
    requires
        cookie_root_of(rules, new) != other,
    ensures
        cookies_of_root(rules, insert_a_cookie(jar, new), other) == cookies_of_root(rules, jar, other),
{
    lemma_find_old_cookie_from(jar, new, 0);
    let p = in_root(rules, other);
    match find_old_cookie(jar, new) {
        Some(i) => {
            lemma_filter_remove_rejected(jar, i, p);
            lemma_filter_push(jar.remove(i), new, p);
        },
        None => {
            lemma_filter_push(jar, new, p);
        },
    }
}

/// Storing a cookie changes the cookies of a root only if it is the root of
/// the new cookie: the cookies of any other root are those of the jar after
/// the eviction of expired cookies, in the same order.
///
/// With `lemma_store_within_root` (the new cookie's root is the request
/// host's), this is the plan's `lemma_store_frame`.
pub proof fn lemma_store_frame_of_new_root(
    rules: Seq<clazel_psl::spec::Rule>,
    jar: Seq<Cookie>,
    url: RequestUrl,
    ctx: RequestContext,
    received: crate::set_cookie::spec::SetCookie,
    now: int,
    new: Cookie,
    other: crate::matching::spec::CanonicalHost,
)
    requires
        create_a_cookie(rules, evict_expired(jar, now), url, ctx, received, now) == Some(new),
        cookie_root_of(rules, new) != other,
    ensures
        cookies_of_root(rules, store_a_cookie(rules, jar, url, ctx, received, now), other) == cookies_of_root(
            rules,
            evict_expired(jar, now),
            other,
        ),
{
    let live = evict_expired(jar, now);
    let inserted = insert_a_cookie(live, new);
    let evicted = evict_expired(inserted, now);
    let r = in_root(rules, other);
    let alive = not_expired(now);
    // The excess of the new cookie's root.
    lemma_evict_over_limit_frame(rules, evicted, cookie_root_of(rules, new), other);
    // The eviction of expired cookies commutes with taking a root's cookies.
    lemma_filter_commute(inserted, alive, r);
    // The insertion does not touch another root.
    lemma_insert_a_cookie_frame(rules, live, new, other);
    // `live` holds no expired cookie, so evicting again changes nothing.
    lemma_filter_idempotent(jar, alive);
    lemma_filter_commute(live, r, alive);
    assert(live.filter(alive) == live);
}

/// Mapping `f` over a sequence does not change what `p` keeps, when `f`
/// does not change whether `p` holds and fixes every element `p` holds of.
pub proof fn lemma_map_values_filter<A>(s: Seq<A>, f: spec_fn(A) -> A, p: spec_fn(A) -> bool)
    requires
        forall|c: A| #[trigger] p(f(c)) == p(c),
        forall|c: A| p(c) ==> #[trigger] f(c) == c,
    ensures
        s.map_values(f).filter(p) == s.filter(p),
    decreases s.len(),
{
    reveal(Seq::filter);
    if s.len() > 0 {
        let t = s.drop_last();
        let x = s.last();
        lemma_map_values_filter(t, f, p);
        assert(s.map_values(f).drop_last() =~= t.map_values(f));
        assert(s.map_values(f).last() == f(x));
    }
}

/// Retrieval changes the cookies of a root only if some retrieved cookie is
/// under it: for a root `other` that no retrieved cookie has, the jar after
/// retrieval has the cookies of `other` of the jar after the eviction of
/// expired cookies, in the same order.
///
/// With `lemma_retrieve_within_root` (a retrieved cookie has the host's
/// root), this is the plan's `lemma_retrieve_frame`.
pub proof fn lemma_retrieve_frame_of_root(
    rules: Seq<clazel_psl::spec::Rule>,
    jar: Seq<Cookie>,
    url: RequestUrl,
    ctx: RequestContext,
    now: int,
    host: crate::matching::spec::CanonicalHost,
    other: crate::matching::spec::CanonicalHost,
)
    requires
        url.host == Some(host),
        forall|c: Cookie| #[trigger] cookie_is_retrieved(rules, url, ctx, host, c) ==> cookie_root_of(rules, c) != other,
    ensures
        cookies_of_root(rules, jar_after_retrieval(rules, jar, url, ctx, now), other) == cookies_of_root(
            rules,
            evict_expired(jar, now),
            other,
        ),
{
    let live = evict_expired(jar, now);
    let f = update_last_access_time(rules, url, ctx, host, now);
    let p = in_root(rules, other);
    assert forall|c: Cookie| #[trigger] p(f(c)) == p(c) by {
        if cookie_is_retrieved(rules, url, ctx, host, c) {
            assert(f(c) == with_last_access_time(c, now));
            assert(cookie_root_of(rules, f(c)) == cookie_root_of(rules, c));
        } else {
            assert(f(c) == c);
        }
    }
    assert forall|c: Cookie| p(c) implies #[trigger] f(c) == c by {
        assert(!cookie_is_retrieved(rules, url, ctx, host, c));
    }
    lemma_map_values_filter(live, f, p);
}

} // verus!
