//! The isolation lemmas of item 2.9, proven from `clazel-psl`'s root
//! lemmas: a store for host `h` produces a cookie whose domain has `h`'s
//! cookie root and changes no cookie of another root
//! ([`lemma_store_within_root`], [`lemma_store_frame`]); a retrieval for `h`
//! returns only cookies under `h`'s root and changes no cookie of another
//! root ([`lemma_retrieve_within_root`], [`lemma_retrieve_frame`]); storage
//! keeps every root within its limit and the keys unique
//! ([`lemma_store_bounds`]).
//!
//! `clazel-psl` states domain matching over `u32` code points
//! (`domain_match_u32`) and this crate over `u8` octets
//! (`crate::matching::spec::domain_matches`); [`lemma_domain_matches_bridge`]
//! is the bridge: for host names they are the same relation on a string and
//! its [`widen`]ing.
//!
//! # A hypothesis the header of `spec.rs` did not record
//!
//! `lemma_retrieve_within_root` as the header of `spec.rs` states it (every
//! cookie of every jar) is false: a cookie whose domain is the empty string
//! is not a public suffix and, with host-only-flag false, "domain-matches"
//! any host that ends in "." (the empty domain string is a suffix of it and
//! the last character before it is "."). The cookie root of "" is "", and of
//! "a." is "a.", which differ. No cookie the algorithms create has an empty
//! domain (step 10 gives the request host, which is not empty, or a
//! non-empty domain-attribute), so the lemmas below assume the invariant
//! [`jar_domains_nonempty`] of the jar, and
//! [`lemma_store_preserves_domains_nonempty`] shows storage keeps it. The
//! kernel's invariant (2.10) must include it. The store lemmas need no such
//! hypothesis.

use super::lemmas::*;
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------
// The u8 / u32 bridge.
// ---------------------------------------------------------------------

/// `widen` is injective.
pub proof fn lemma_widen_injective(a: Seq<u8>, b: Seq<u8>)
    ensures
        (widen(a) == widen(b)) <==> (a == b),
{
    assert(widen(a).len() == a.len());
    assert(widen(b).len() == b.len());
    if widen(a) == widen(b) {
        assert(a.len() == b.len());
        assert forall|i: int| 0 <= i < a.len() implies a[i] == b[i] by {
            assert(widen(a)[i] == a[i] as u32);
            assert(widen(b)[i] == b[i] as u32);
        }
        assert(a =~= b);
    }
}

/// `widen` commutes with `subrange`.
pub proof fn lemma_widen_subrange(a: Seq<u8>, i: int, j: int)
    requires
        0 <= i <= j <= a.len(),
    ensures
        widen(a).subrange(i, j) == widen(a.subrange(i, j)),
{
    assert(widen(a).subrange(i, j) =~= widen(a.subrange(i, j)));
}

/// The bridge between the two statements of domain matching: for a string
/// that is a host name, [`crate::matching::spec::domain_matches`] over
/// octets is `clazel_psl::spec::domain_match_u32` over their code points.
pub proof fn lemma_domain_matches_bridge(h: Seq<u8>, c: Seq<u8>)
    ensures
        crate::matching::spec::domain_matches(h, true, c) <==> clazel_psl::spec::domain_match_u32(widen(h), widen(c)),
{
    lemma_widen_injective(h, c);
    assert(widen(h).len() == h.len());
    assert(widen(c).len() == c.len());
    if c.len() <= h.len() {
        lemma_widen_subrange(h, h.len() - c.len(), h.len() as int);
        let sub = h.subrange(h.len() - c.len(), h.len() as int);
        lemma_widen_injective(c, sub);
        if h.len() > c.len() {
            assert(widen(h)[h.len() - c.len() - 1] == h[h.len() - c.len() - 1] as u32);
        }
    }
}

// ---------------------------------------------------------------------
// Well-formed jars.
// ---------------------------------------------------------------------

/// The cookie's domain is not the empty string.
pub open spec fn cookie_domain_nonempty(c: Cookie) -> bool {
    c.domain.name.len() > 0
}

/// Every cookie of the jar has a non-empty domain: the invariant of every
/// jar the algorithms produce, and the hypothesis the retrieval lemmas need.
pub open spec fn jar_domains_nonempty(jar: Seq<Cookie>) -> bool {
    forall|i: int| 0 <= i < jar.len() ==> cookie_domain_nonempty(#[trigger] jar[i])
}

/// The request URL's host, if any, has a non-empty name (a canonicalized
/// host never is empty: the host parser fails on the empty host).
pub open spec fn url_host_nonempty(url: RequestUrl) -> bool {
    url.host matches Some(h) ==> h.name.len() > 0
}

/// The counterexample to the header's `lemma_retrieve_within_root` without
/// a non-empty domain: a cookie with domain "" is retrieved for host "a.",
/// whose cookie root differs from the root of "".
pub proof fn example_empty_domain_breaks_retrieve_within_root(rules: Seq<clazel_psl::spec::Rule>)
    ensures
        ({
            let host = crate::matching::spec::CanonicalHost { name: seq![0x61u8, 0x2E], is_ip_address: false };
            let dom = crate::matching::spec::CanonicalHost { name: seq![], is_ip_address: false };
            let cookie = Cookie {
                name: seq![],
                value: seq![],
                expiry_time: 0,
                domain: dom,
                path: seq![0x2Fu8],
                creation_time: 0,
                last_access_time: 0,
                persistent_flag: false,
                host_only_flag: false,
                secure_only_flag: false,
                http_only_flag: false,
                same_site_flag: crate::set_cookie::spec::SameSite::None,
            };
            let url = RequestUrl { scheme: lit_https(), host: Some(host), path: seq![0x2Fu8] };
            let ctx = RequestContext::NonHttp(
                DocumentCall {
                    site_for_cookies: clazel_origin::spec::Origin::Opaque(0),
                    top_level_origin: clazel_origin::spec::Origin::Opaque(0),
                },
            );
            cookie_is_retrieved(rules, url, ctx, host, cookie) && cookie_root_of(rules, cookie) != cookie_root(rules, host)
        }),
{
    let host = crate::matching::spec::CanonicalHost { name: seq![0x61u8, 0x2E], is_ip_address: false };
    let dom = crate::matching::spec::CanonicalHost { name: seq![], is_ip_address: false };
    let empty: Seq<u32> = seq![];
    let a_dot: Seq<u32> = seq![0x61u32, 0x2E];
    assert(widen(host.name) =~= a_dot);
    assert(widen(dom.name) =~= empty);
    // "" splits into one empty label, so it is not a public suffix.
    assert(clazel_url::host::spec::collect_not_equal(empty, 0x2E, 0) =~= seq![]);
    assert(clazel_psl::spec::domain_labels(empty) =~= seq![empty]);
    assert(clazel_psl::spec::has_empty_label(clazel_psl::spec::domain_labels(empty))) by {
        assert(clazel_psl::spec::has_empty_label_from(seq![empty], 0));
    }
    assert(!is_public_suffix_string(rules, dom.name));
    // The root of "" is a suffix of "", so empty; the root of "a." has the
    // trailing dot of "a.", so is not.
    clazel_psl::lemmas::lemma_root_is_label_suffix(rules, empty);
    let k0 = choose|k: nat|
        1 <= k <= clazel_psl::spec::domain_labels(empty).len() && clazel_psl::spec::cookie_root_of_domain(rules, empty)
            == clazel_psl::spec::label_suffix(clazel_psl::spec::domain_labels(empty), clazel_psl::spec::has_trailing_dot(empty), k);
    clazel_psl::lemmas::lemma_label_suffix_is_string_suffix(empty, k0);
    assert(clazel_psl::spec::cookie_root_of_domain(rules, empty).len() == 0);
    clazel_psl::lemmas::lemma_root_is_label_suffix(rules, a_dot);
    let k1 = choose|k: nat|
        1 <= k <= clazel_psl::spec::domain_labels(a_dot).len() && clazel_psl::spec::cookie_root_of_domain(rules, a_dot)
            == clazel_psl::spec::label_suffix(clazel_psl::spec::domain_labels(a_dot), clazel_psl::spec::has_trailing_dot(a_dot), k);
    clazel_psl::lemmas::lemma_label_suffix_labels(a_dot, k1);
    assert(clazel_psl::spec::has_trailing_dot(a_dot));
    assert(clazel_psl::spec::cookie_root_of_domain(rules, a_dot).len() > 0);
    assert(cookie_root(rules, dom).name.len() == 0);
    assert(cookie_root(rules, host).name.len() > 0);
}

// ---------------------------------------------------------------------
// Store and retrieve stay within the root.
// ---------------------------------------------------------------------

/// Step 9 and 10 of §5.7 for a request host `host`: the domain of the new
/// cookie is the host itself, or a non-empty domain-attribute that is not a
/// public suffix and that the host domain-matches.
pub proof fn lemma_step_9_10_domain(
    rules: Seq<clazel_psl::spec::Rule>,
    host: crate::matching::spec::CanonicalHost,
    domain_attribute: Seq<u8>,
    da: Seq<u8>,
    domain: crate::matching::spec::CanonicalHost,
    host_only: bool,
)
    requires
        step_9_domain_attribute(rules, host, domain_attribute) == Some(da),
        step_10_domain(host, da) == Some((domain, host_only)),
    ensures
        domain == host || (da.len() > 0 && !is_public_suffix_string(rules, da) && crate::matching::spec::domain_matches(
            host.name,
            !host.is_ip_address,
            da,
        ) && domain == (crate::matching::spec::CanonicalHost { name: da, is_ip_address: host.is_ip_address })),
{
}

/// Storing a cookie for a request to host `host`: the new cookie's domain
/// has `host`'s cookie root.
pub proof fn lemma_store_within_root(
    rules: Seq<clazel_psl::spec::Rule>,
    jar: Seq<Cookie>,
    url: RequestUrl,
    ctx: RequestContext,
    received: crate::set_cookie::spec::SetCookie,
    now: int,
    host: crate::matching::spec::CanonicalHost,
    new: Cookie,
)
    requires
        url.host == Some(host),
        create_a_cookie(rules, jar, url, ctx, received, now) == Some(new),
    ensures
        cookie_root(rules, new.domain) == cookie_root(rules, host),
{
    let domain_attribute = match last_domain_within_1024(received.attributes) {
        Some(d) => d,
        None => seq![],
    };
    let r9 = step_9_domain_attribute(rules, host, domain_attribute);
    assert(r9 is Some);
    let da = r9->Some_0;
    let r10 = step_10_domain(host, da);
    assert(r10 is Some);
    let (domain, host_only) = r10->Some_0;
    assert(new.domain == domain);
    lemma_step_9_10_domain(rules, host, domain_attribute, da, domain, host_only);
    if domain != host {
        if host.is_ip_address {
            // Only "identical" domain-matches an IP address.
            assert(da == host.name);
            assert(domain == host);
        } else {
            lemma_domain_matches_bridge(host.name, da);
            clazel_psl::lemmas::lemma_domain_match_same_root(rules, widen(host.name), widen(da));
            assert(clazel_psl::spec::cookie_root_of_domain(rules, widen(da)) == clazel_psl::spec::cookie_root_of_domain(
                rules,
                widen(host.name),
            ));
        }
    }
}

/// Retrieving for host `host` returns only cookies whose domain has
/// `host`'s cookie root, for a cookie with a non-empty domain (see the
/// module comment for why that is needed).
pub proof fn lemma_retrieve_within_root(
    rules: Seq<clazel_psl::spec::Rule>,
    url: RequestUrl,
    ctx: RequestContext,
    host: crate::matching::spec::CanonicalHost,
    cookie: Cookie,
)
    requires
        url.host == Some(host),
        cookie_domain_nonempty(cookie),
        cookie_is_retrieved(rules, url, ctx, host, cookie),
    ensures
        cookie_root_of(rules, cookie) == cookie_root(rules, host),
{
    if cookie.host_only_flag {
        assert(host == cookie.domain);
    } else if host != cookie.domain {
        assert(!host.is_ip_address && !cookie.domain.is_ip_address);
        assert(crate::matching::spec::domain_matches(host.name, true, cookie.domain.name));
        assert(!is_public_suffix_string(rules, cookie.domain.name));
        lemma_domain_matches_bridge(host.name, cookie.domain.name);
        clazel_psl::lemmas::lemma_domain_match_same_root(rules, widen(host.name), widen(cookie.domain.name));
        assert(widen(cookie.domain.name).len() == cookie.domain.name.len());
    }
}

// ---------------------------------------------------------------------
// Filters, removal and keys (helpers).
// ---------------------------------------------------------------------

/// What a filter keeps was in the sequence, and satisfies the predicate.
pub proof fn lemma_filter_elem<A>(s: Seq<A>, p: spec_fn(A) -> bool, x: A)
    requires
        s.filter(p).contains(x),
    ensures
        s.contains(x),
        p(x),
    decreases s.len(),
{
    reveal(Seq::filter);
    let t = s.drop_last();
    let y = s.last();
    let f = s.filter(p);
    assert(s.len() > 0);
    let j = choose|j: int| 0 <= j < f.len() && f[j] == x;
    if p(y) {
        let sub = t.filter(p);
        assert(f == sub.push(y));
        if j < sub.len() {
            assert(sub[j] == x);
            assert(sub.contains(x));
            lemma_filter_elem(t, p, x);
            let k = choose|k: int| 0 <= k < t.len() && t[k] == x;
            assert(s[k] == x);
        } else {
            assert(x == y);
            assert(s[s.len() - 1] == x);
        }
    } else {
        assert(f == t.filter(p));
        lemma_filter_elem(t, p, x);
        let k = choose|k: int| 0 <= k < t.len() && t[k] == x;
        assert(s[k] == x);
    }
}

/// A filter with something in it had something that satisfies the predicate.
pub proof fn lemma_filter_nonempty<A>(s: Seq<A>, p: spec_fn(A) -> bool)
    requires
        s.filter(p).len() > 0,
    ensures
        exists|i: int| 0 <= i < s.len() && p(#[trigger] s[i]),
    decreases s.len(),
{
    reveal(Seq::filter);
    let t = s.drop_last();
    let y = s.last();
    if p(y) {
        assert(s[s.len() - 1] == y);
    } else {
        assert(s.filter(p) == t.filter(p));
        lemma_filter_nonempty(t, p);
        let i = choose|i: int| 0 <= i < t.len() && p(t[i]);
        assert(s[i] == t[i]);
    }
}

/// Removing an element that `p` accepts removes one from the filter.
pub proof fn lemma_filter_remove_accepted<A>(s: Seq<A>, i: int, p: spec_fn(A) -> bool)
    requires
        0 <= i < s.len(),
        p(s[i]),
    ensures
        s.remove(i).filter(p).len() + 1 == s.filter(p).len(),
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
    assert(m.filter(p) =~= seq![s[i]]);
}

/// Pushing a cookie keeps the keys unique exactly when they were and none
/// is the pushed one's.
pub proof fn lemma_push_keys_unique(s: Seq<Cookie>, x: Cookie)
    ensures
        jar_keys_unique(s.push(x)) <==> (jar_keys_unique(s) && forall|k: int| 0 <= k < s.len() ==> !same_key(#[trigger] s[k], x)),
{
    let t = s.push(x);
    if jar_keys_unique(t) {
        assert forall|i: int, j: int| 0 <= i < j < s.len() implies !same_key(#[trigger] s[i], #[trigger] s[j]) by {
            assert(t[i] == s[i]);
            assert(t[j] == s[j]);
        }
        assert forall|k: int| 0 <= k < s.len() implies !same_key(#[trigger] s[k], x) by {
            assert(t[k] == s[k]);
            assert(t[s.len() as int] == x);
        }
    }
    if jar_keys_unique(s) && forall|k: int| 0 <= k < s.len() ==> !same_key(#[trigger] s[k], x) {
        assert forall|i: int, j: int| 0 <= i < j < t.len() implies !same_key(#[trigger] t[i], #[trigger] t[j]) by {
            if j < s.len() {
                assert(t[i] == s[i]);
                assert(t[j] == s[j]);
            } else {
                assert(t[i] == s[i]);
                assert(t[j] == x);
            }
        }
    }
}

/// Removing a cookie keeps the keys unique and the cookies among the old.
pub proof fn lemma_remove_keys_unique(s: Seq<Cookie>, i: int)
    requires
        0 <= i < s.len(),
        jar_keys_unique(s),
    ensures
        jar_keys_unique(s.remove(i)),
        forall|x: Cookie| s.remove(i).contains(x) ==> s.contains(x),
{
    s.remove_ensures(i);
    let r = s.remove(i);
    assert forall|a: int, b: int| 0 <= a < b < r.len() implies !same_key(#[trigger] r[a], #[trigger] r[b]) by {
        let a2 = if a < i { a } else { a + 1 };
        let b2 = if b < i { b } else { b + 1 };
        assert(r[a] == s[a2]);
        assert(r[b] == s[b2]);
    }
    assert forall|x: Cookie| r.contains(x) implies s.contains(x) by {
        let k = choose|k: int| 0 <= k < r.len() && r[k] == x;
        let k2 = if k < i { k } else { k + 1 };
        assert(s[k2] == x);
    }
}

/// A filter keeps the keys unique.
pub proof fn lemma_filter_keys_unique(s: Seq<Cookie>, p: spec_fn(Cookie) -> bool)
    requires
        jar_keys_unique(s),
    ensures
        jar_keys_unique(s.filter(p)),
    decreases s.len(),
{
    reveal(Seq::filter);
    if s.len() > 0 {
        let t = s.drop_last();
        let y = s.last();
        assert forall|i: int, j: int| 0 <= i < j < t.len() implies !same_key(#[trigger] t[i], #[trigger] t[j]) by {
            assert(s[i] == t[i]);
            assert(s[j] == t[j]);
        }
        lemma_filter_keys_unique(t, p);
        if p(y) {
            let sub = t.filter(p);
            assert forall|k: int| 0 <= k < sub.len() implies !same_key(#[trigger] sub[k], y) by {
                assert(sub.contains(sub[k]));
                lemma_filter_elem(t, p, sub[k]);
                let k2 = choose|k2: int| 0 <= k2 < t.len() && t[k2] == sub[k];
                assert(s[k2] == t[k2]);
                assert(s[s.len() - 1] == y);
            }
            lemma_push_keys_unique(sub, y);
        }
    }
}

/// Evicting expired cookies keeps the keys unique, does not grow any root,
/// and keeps only cookies of the jar.
pub proof fn lemma_evict_expired_props(
    rules: Seq<clazel_psl::spec::Rule>,
    jar: Seq<Cookie>,
    now: int,
    root: crate::matching::spec::CanonicalHost,
)
    ensures
        jar_keys_unique(jar) ==> jar_keys_unique(evict_expired(jar, now)),
        root_count(rules, evict_expired(jar, now), root) <= root_count(rules, jar, root),
        forall|x: Cookie| evict_expired(jar, now).contains(x) ==> jar.contains(x),
{
    if jar_keys_unique(jar) {
        lemma_filter_keys_unique(jar, not_expired(now));
    }
    lemma_filter_commute(jar, not_expired(now), in_root(rules, root));
    jar.filter(in_root(rules, root)).lemma_filter_len(not_expired(now));
    assert forall|x: Cookie| evict_expired(jar, now).contains(x) implies jar.contains(x) by {
        lemma_filter_elem(jar, not_expired(now), x);
    }
}

/// Searching for the old-cookie: none found means none has the key.
pub proof fn lemma_find_old_cookie_none(jar: Seq<Cookie>, new: Cookie, i: nat)
    requires
        find_old_cookie_from(jar, new, i) is None,
    ensures
        forall|k: int| i <= k < jar.len() ==> !same_key(#[trigger] jar[k], new),
    decreases jar.len() - i,
{
    if i < jar.len() {
        lemma_find_old_cookie_none(jar, new, i + 1);
    }
}

/// Inserting a cookie (steps 23.4 and 24) into a jar with unique keys keeps
/// them unique, adds at most the new cookie to its root, and adds no other
/// cookie.
pub proof fn lemma_insert_props(rules: Seq<clazel_psl::spec::Rule>, jar: Seq<Cookie>, new: Cookie, root: crate::matching::spec::CanonicalHost)
    requires
        jar_keys_unique(jar),
    ensures
        jar_keys_unique(insert_a_cookie(jar, new)),
        root_count(rules, insert_a_cookie(jar, new), root) <= root_count(rules, jar, root) + (if cookie_root_of(rules, new) == root {
            1nat
        } else {
            0nat
        }),
        forall|x: Cookie| insert_a_cookie(jar, new).contains(x) ==> (jar.contains(x) || x == new),
{
    lemma_find_old_cookie_from(jar, new, 0);
    let p = in_root(rules, root);
    match find_old_cookie(jar, new) {
        Some(i) => {
            lemma_remove_keys_unique(jar, i);
            let r = jar.remove(i);
            jar.remove_ensures(i);
            assert forall|k: int| 0 <= k < r.len() implies !same_key(#[trigger] r[k], new) by {
                let k2 = if k < i { k } else { k + 1 };
                assert(r[k] == jar[k2]);
                if k2 < i {
                    assert(!same_key(jar[k2], jar[i]));
                } else {
                    assert(!same_key(jar[i], jar[k2]));
                }
            }
            lemma_push_keys_unique(r, new);
            lemma_filter_push(r, new, p);
            if p(jar[i]) {
                lemma_filter_remove_accepted(jar, i, p);
            } else {
                lemma_filter_remove_rejected(jar, i, p);
            }
            // The old cookie has the new one's domain, hence its root.
            assert(cookie_root_of(rules, jar[i]) == cookie_root_of(rules, new));
            assert forall|x: Cookie| r.push(new).contains(x) implies (jar.contains(x) || x == new) by {
                let k = choose|k: int| 0 <= k < r.push(new).len() && r.push(new)[k] == x;
                if k < r.len() {
                    assert(r.push(new)[k] == r[k]);
                    assert(r.contains(x));
                }
            }
        },
        None => {
            lemma_find_old_cookie_none(jar, new, 0);
            lemma_push_keys_unique(jar, new);
            lemma_filter_push(jar, new, p);
            assert forall|x: Cookie| jar.push(new).contains(x) implies (jar.contains(x) || x == new) by {
                let k = choose|k: int| 0 <= k < jar.push(new).len() && jar.push(new)[k] == x;
                if k < jar.len() {
                    assert(jar.push(new)[k] == jar[k]);
                }
            }
        },
    }
}

// ---------------------------------------------------------------------
// The per-root eviction.
// ---------------------------------------------------------------------

/// A cookie of the root among the first `n` makes the victim exist.
pub proof fn lemma_victim_from_some(
    rules: Seq<clazel_psl::spec::Rule>,
    jar: Seq<Cookie>,
    root: crate::matching::spec::CanonicalHost,
    n: nat,
)
    requires
        n <= jar.len(),
        exists|j: int| 0 <= j < n && cookie_root_of(rules, #[trigger] jar[j]) == root,
    ensures
        victim_from(rules, jar, root, n) is Some,
    decreases n,
{
    let j = choose|j: int| 0 <= j < n && cookie_root_of(rules, #[trigger] jar[j]) == root;
    if n > 0 {
        if j < n - 1 {
            lemma_victim_from_some(rules, jar, root, (n - 1) as nat);
        }
    }
}

/// [`evict_over_limit`] leaves the root within the limit, and keeps the
/// keys unique and only cookies of the jar.
pub proof fn lemma_evict_over_limit_props(rules: Seq<clazel_psl::spec::Rule>, jar: Seq<Cookie>, root: crate::matching::spec::CanonicalHost)
    ensures
        root_count(rules, evict_over_limit(rules, jar, root), root) <= max_cookies_per_root(),
        jar_keys_unique(jar) ==> jar_keys_unique(evict_over_limit(rules, jar, root)),
        forall|x: Cookie| evict_over_limit(rules, jar, root).contains(x) ==> jar.contains(x),
    decreases jar.len(),
{
    if root_count(rules, jar, root) > max_cookies_per_root() {
        lemma_filter_nonempty(jar, in_root(rules, root));
        lemma_victim_from_some(rules, jar, root, jar.len());
        lemma_victim_from_in_root(rules, jar, root, jar.len());
        let i = victim_from(rules, jar, root, jar.len())->Some_0;
        assert(0 <= i < jar.len());
        jar.remove_ensures(i);
        assert(in_root(rules, root)(jar[i]));
        lemma_filter_remove_accepted(jar, i, in_root(rules, root));
        lemma_evict_over_limit_props(rules, jar.remove(i), root);
        if jar_keys_unique(jar) {
            lemma_remove_keys_unique(jar, i);
        }
        assert forall|x: Cookie| evict_over_limit(rules, jar, root).contains(x) implies jar.contains(x) by {
            assert(evict_over_limit(rules, jar.remove(i), root).contains(x));
            assert(jar.remove(i).contains(x));
            let k = choose|k: int| 0 <= k < jar.remove(i).len() && jar.remove(i)[k] == x;
            let k2 = if k < i { k } else { k + 1 };
            assert(jar[k2] == x);
        }
    }
}

// ---------------------------------------------------------------------
// Frames and bounds of storage and retrieval.
// ---------------------------------------------------------------------

/// Storing a cookie for a request to host `host` leaves the cookies of every
/// other root as they were (up to the eviction of expired ones).
pub proof fn lemma_store_frame(
    rules: Seq<clazel_psl::spec::Rule>,
    jar: Seq<Cookie>,
    url: RequestUrl,
    ctx: RequestContext,
    received: crate::set_cookie::spec::SetCookie,
    now: int,
    host: crate::matching::spec::CanonicalHost,
    other: crate::matching::spec::CanonicalHost,
)
    requires
        url.host == Some(host),
        other != cookie_root(rules, host),
    ensures
        cookies_of_root(rules, store_a_cookie(rules, jar, url, ctx, received, now), other) == cookies_of_root(
            rules,
            evict_expired(jar, now),
            other,
        ),
{
    let live = evict_expired(jar, now);
    let created = create_a_cookie(rules, live, url, ctx, received, now);
    if created is Some {
        let new = created->Some_0;
        lemma_store_within_root(rules, live, url, ctx, received, now, host, new);
        lemma_store_frame_of_new_root(rules, jar, url, ctx, received, now, new, other);
    }
}

/// [`lemma_map_values_filter`] for the elements of `s` only.
pub proof fn lemma_map_values_filter_in<A>(s: Seq<A>, f: spec_fn(A) -> A, p: spec_fn(A) -> bool)
    requires
        forall|c: A| #[trigger] p(f(c)) == p(c),
        forall|i: int| 0 <= i < s.len() && p(#[trigger] s[i]) ==> f(s[i]) == s[i],
    ensures
        s.map_values(f).filter(p) == s.filter(p),
    decreases s.len(),
{
    reveal(Seq::filter);
    if s.len() > 0 {
        let t = s.drop_last();
        let x = s.last();
        assert forall|i: int| 0 <= i < t.len() && p(#[trigger] t[i]) implies f(t[i]) == t[i] by {
            assert(s[i] == t[i]);
        }
        lemma_map_values_filter_in(t, f, p);
        assert(s.map_values(f).drop_last() =~= t.map_values(f));
        assert(s.map_values(f).last() == f(x));
        assert(s[s.len() - 1] == x);
    }
}

/// Retrieval for host `host` changes no cookie of another root (up to the
/// eviction of expired ones), for a jar of cookies with non-empty domains.
pub proof fn lemma_retrieve_frame(
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
        other != cookie_root(rules, host),
        jar_domains_nonempty(jar),
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
    assert forall|i: int| 0 <= i < live.len() && p(#[trigger] live[i]) implies f(live[i]) == live[i] by {
        assert(live.contains(live[i]));
        lemma_filter_elem(jar, not_expired(now), live[i]);
        let k = choose|k: int| 0 <= k < jar.len() && jar[k] == live[i];
        assert(cookie_domain_nonempty(jar[k]));
        if cookie_is_retrieved(rules, url, ctx, host, live[i]) {
            lemma_retrieve_within_root(rules, url, ctx, host, live[i]);
            assert(false);
        }
    }
    lemma_map_values_filter_in(live, f, p);
}

/// Storage keeps every root within its limit and the keys unique.
pub proof fn lemma_store_bounds(
    rules: Seq<clazel_psl::spec::Rule>,
    jar: Seq<Cookie>,
    url: RequestUrl,
    ctx: RequestContext,
    received: crate::set_cookie::spec::SetCookie,
    now: int,
)
    requires
        jar_within_root_limit(rules, jar),
        jar_keys_unique(jar),
    ensures
        jar_within_root_limit(rules, store_a_cookie(rules, jar, url, ctx, received, now)),
        jar_keys_unique(store_a_cookie(rules, jar, url, ctx, received, now)),
{
    let live = evict_expired(jar, now);
    let any_root = crate::matching::spec::CanonicalHost { name: seq![], is_ip_address: false };
    lemma_evict_expired_props(rules, jar, now, any_root);
    assert forall|root: crate::matching::spec::CanonicalHost| root_count(rules, live, root) <= max_cookies_per_root() by {
        lemma_evict_expired_props(rules, jar, now, root);
    }
    let created = create_a_cookie(rules, live, url, ctx, received, now);
    if created is Some {
        let new = created->Some_0;
        let r = cookie_root_of(rules, new);
        let inserted = insert_a_cookie(live, new);
        let evicted = evict_expired(inserted, now);
        let result = evict_over_limit(rules, evicted, r);
        lemma_insert_props(rules, live, new, r);
        lemma_evict_expired_props(rules, inserted, now, r);
        lemma_evict_over_limit_props(rules, evicted, r);
        assert forall|root: crate::matching::spec::CanonicalHost| root_count(rules, result, root) <= max_cookies_per_root() by {
            lemma_insert_props(rules, live, new, root);
            lemma_evict_expired_props(rules, inserted, now, root);
            if root != r {
                lemma_evict_over_limit_frame(rules, evicted, r, root);
            }
        }
    }
}

/// Storage keeps the domains of the jar non-empty, for a request whose host
/// is.
pub proof fn lemma_store_preserves_domains_nonempty(
    rules: Seq<clazel_psl::spec::Rule>,
    jar: Seq<Cookie>,
    url: RequestUrl,
    ctx: RequestContext,
    received: crate::set_cookie::spec::SetCookie,
    now: int,
)
    requires
        jar_domains_nonempty(jar),
        url_host_nonempty(url),
        jar_keys_unique(jar),
    ensures
        jar_domains_nonempty(store_a_cookie(rules, jar, url, ctx, received, now)),
{
    let live = evict_expired(jar, now);
    let any_root = crate::matching::spec::CanonicalHost { name: seq![], is_ip_address: false };
    lemma_evict_expired_props(rules, jar, now, any_root);
    let created = create_a_cookie(rules, live, url, ctx, received, now);
    let result = store_a_cookie(rules, jar, url, ctx, received, now);
    assert forall|i: int| 0 <= i < live.len() implies cookie_domain_nonempty(#[trigger] live[i]) by {
        assert(live.contains(live[i]));
        assert(jar.contains(live[i]));
        let k = choose|k: int| 0 <= k < jar.len() && jar[k] == live[i];
    }
    if created is Some {
        let new = created->Some_0;
        let host = url.host->Some_0;
        let domain_attribute = match last_domain_within_1024(received.attributes) {
            Some(d) => d,
            None => seq![],
        };
        let r9 = step_9_domain_attribute(rules, host, domain_attribute);
        let da = r9->Some_0;
        let r10 = step_10_domain(host, da);
        let (domain, host_only) = r10->Some_0;
        lemma_step_9_10_domain(rules, host, domain_attribute, da, domain, host_only);
        assert(cookie_domain_nonempty(new));
        let r = cookie_root_of(rules, new);
        let inserted = insert_a_cookie(live, new);
        let evicted = evict_expired(inserted, now);
        lemma_insert_props(rules, live, new, r);
        lemma_evict_expired_props(rules, inserted, now, r);
        lemma_evict_over_limit_props(rules, evicted, r);
        assert forall|i: int| 0 <= i < result.len() implies cookie_domain_nonempty(#[trigger] result[i]) by {
            assert(result.contains(result[i]));
            assert(evicted.contains(result[i]));
            assert(inserted.contains(result[i]));
            if result[i] != new {
                assert(live.contains(result[i]));
                let k = choose|k: int| 0 <= k < live.len() && live[k] == result[i];
            }
        }
    }
}

} // verus!
