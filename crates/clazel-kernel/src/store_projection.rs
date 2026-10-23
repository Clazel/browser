//! Storage seen from one cookie root (item 2.11): the jar after RFC 6265bis
//! storage, restricted to the root of the request host, depends on the jar
//! only through its cookies under that root, provided no cookie of the jar
//! and not the request host is a public suffix. (Without that condition
//! §5.7 step 16 reads cookies of other roots: see `counterexamples.rs`.)

#[allow(unused_imports)]
use super::noninterference::*;
#[allow(unused_imports)]
use super::projection::*;
#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------
// Domains that match are in one root.
// ---------------------------------------------------------------------

/// Two non-empty cookie domains, neither a public suffix, one of which
/// domain-matches the other, have the same cookie root.
pub proof fn lemma_related_same_root(rules: Seq<clazel_psl::spec::Rule>, a: clazel_cookie::matching::spec::CanonicalHost, d: clazel_cookie::matching::spec::CanonicalHost)
    requires
        a.name.len() > 0,
        d.name.len() > 0,
        a.is_ip_address || !clazel_cookie::storage::spec::is_public_suffix_string(rules, a.name),
        d.is_ip_address || !clazel_cookie::storage::spec::is_public_suffix_string(rules, d.name),
        clazel_cookie::storage::spec::canonical_domain_matches(a, d) || clazel_cookie::storage::spec::canonical_domain_matches(d, a),
    ensures
        clazel_cookie::storage::spec::cookie_root(rules, a) == clazel_cookie::storage::spec::cookie_root(rules, d),
{
    if a != d {
        assert(!a.is_ip_address && !d.is_ip_address);
        if clazel_cookie::storage::spec::canonical_domain_matches(a, d) {
            clazel_cookie::storage::isolation::lemma_domain_matches_bridge(a.name, d.name);
            clazel_psl::lemmas::lemma_domain_match_same_root(rules, clazel_cookie::storage::spec::widen(a.name), clazel_cookie::storage::spec::widen(d.name));
            assert(clazel_cookie::storage::spec::widen(d.name).len() == d.name.len());
        } else {
            clazel_cookie::storage::isolation::lemma_domain_matches_bridge(d.name, a.name);
            clazel_psl::lemmas::lemma_domain_match_same_root(rules, clazel_cookie::storage::spec::widen(d.name), clazel_cookie::storage::spec::widen(a.name));
            assert(clazel_cookie::storage::spec::widen(a.name).len() == a.name.len());
        }
    }
}

/// "Leave Secure Cookies Alone" (§5.7 step 16) reads only the cookies under
/// the new cookie's root, when no cookie and not the new cookie's domain is
/// a public suffix.
pub proof fn lemma_overlay_filter(
    rules: Seq<clazel_psl::spec::Rule>,
    x: Seq<clazel_cookie::storage::spec::Cookie>,
    name: Seq<u8>,
    dom: clazel_cookie::matching::spec::CanonicalHost,
    path: Seq<u8>,
    root: clazel_cookie::matching::spec::CanonicalHost,
)
    requires
        clazel_cookie::storage::isolation::jar_domains_nonempty(x),
        jar_no_public_suffix(rules, x),
        dom.name.len() > 0,
        dom.is_ip_address || !clazel_cookie::storage::spec::is_public_suffix_string(rules, dom.name),
        clazel_cookie::storage::spec::cookie_root(rules, dom) == root,
    ensures
        clazel_cookie::storage::spec::secure_cookie_would_be_overlaid(x, name, dom, path) == clazel_cookie::storage::spec::secure_cookie_would_be_overlaid(x.filter(clazel_cookie::storage::spec::in_root(rules, root)), name, dom, path),
{
    let p = clazel_cookie::storage::spec::in_root(rules, root);
    let f = x.filter(p);
    if clazel_cookie::storage::spec::secure_cookie_would_be_overlaid(x, name, dom, path) {
        let i = choose|i: int|
            0 <= i < x.len() && (#[trigger] x[i]).name == name && x[i].secure_only_flag && (clazel_cookie::storage::spec::canonical_domain_matches(x[i].domain, dom)
                || clazel_cookie::storage::spec::canonical_domain_matches(dom, x[i].domain)) && clazel_cookie::matching::spec::path_matches(path, x[i].path);
        assert(clazel_cookie::storage::isolation::cookie_domain_nonempty(x[i]));
        lemma_related_same_root(rules, x[i].domain, dom);
        assert(p(x[i]));
        assert(x.filter(p).contains(x[i])) by {
            lemma_filter_contains(x, p, i);
        }
        let k = choose|k: int| 0 <= k < f.len() && f[k] == x[i];
        assert(clazel_cookie::storage::spec::secure_cookie_would_be_overlaid(f, name, dom, path));
    }
    if clazel_cookie::storage::spec::secure_cookie_would_be_overlaid(f, name, dom, path) {
        let k = choose|k: int|
            0 <= k < f.len() && (#[trigger] f[k]).name == name && f[k].secure_only_flag && (clazel_cookie::storage::spec::canonical_domain_matches(f[k].domain, dom)
                || clazel_cookie::storage::spec::canonical_domain_matches(dom, f[k].domain)) && clazel_cookie::matching::spec::path_matches(path, f[k].path);
        assert(f.contains(f[k]));
        clazel_cookie::storage::isolation::lemma_filter_elem(x, p, f[k]);
        let i = choose|i: int| 0 <= i < x.len() && x[i] == f[k];
        assert(clazel_cookie::storage::spec::secure_cookie_would_be_overlaid(x, name, dom, path));
    }
}

/// An element accepted by `p` is in the filter.
pub proof fn lemma_filter_contains<A>(s: Seq<A>, p: spec_fn(A) -> bool, i: int)
    requires
        0 <= i < s.len(),
        p(s[i]),
    ensures
        s.filter(p).contains(s[i]),
{
    lemma_filter_remove_at(s, i, p);
    let k = s.subrange(0, i).filter(p).len() as int;
    assert(s.filter(p)[k] == s[i]);
}

// ---------------------------------------------------------------------
// The old-cookie of step 23.
// ---------------------------------------------------------------------

/// Nothing before the old-cookie has its key.
pub proof fn lemma_find_old_before(jar: Seq<clazel_cookie::storage::spec::Cookie>, new: clazel_cookie::storage::spec::Cookie, i: nat, j: int)
    requires
        clazel_cookie::storage::spec::find_old_cookie_from(jar, new, i) == Some(j),
    ensures
        forall|k: int| i <= k < j ==> !clazel_cookie::storage::spec::same_key(#[trigger] jar[k], new),
    decreases jar.len() - i,
{
    if i < jar.len() && !clazel_cookie::storage::spec::same_key(jar[i as int], new) {
        lemma_find_old_before(jar, new, i + 1, j);
    }
}

/// The first cookie with the key is found.
pub proof fn lemma_find_old_first(s: Seq<clazel_cookie::storage::spec::Cookie>, new: clazel_cookie::storage::spec::Cookie, i: nat, k: int)
    requires
        i <= k < s.len(),
        forall|m: int| i <= m < k ==> !clazel_cookie::storage::spec::same_key(#[trigger] s[m], new),
        clazel_cookie::storage::spec::same_key(s[k], new),
    ensures
        clazel_cookie::storage::spec::find_old_cookie_from(s, new, i) == Some(k),
    decreases k - i,
{
    if i < k {
        lemma_find_old_first(s, new, i + 1, k);
    }
}

/// No cookie has the key: none is found.
pub proof fn lemma_find_old_none(s: Seq<clazel_cookie::storage::spec::Cookie>, new: clazel_cookie::storage::spec::Cookie, i: nat)
    requires
        forall|m: int| i <= m < s.len() ==> !clazel_cookie::storage::spec::same_key(#[trigger] s[m], new),
    ensures
        clazel_cookie::storage::spec::find_old_cookie_from(s, new, i) is None,
    decreases s.len() - i,
{
    if i < s.len() {
        lemma_find_old_none(s, new, i + 1);
    }
}

/// Inserting a cookie whose key can only be found in the root of `p`
/// commutes with taking the cookies of that root.
pub proof fn lemma_insert_filter(jar: Seq<clazel_cookie::storage::spec::Cookie>, new: clazel_cookie::storage::spec::Cookie, p: spec_fn(clazel_cookie::storage::spec::Cookie) -> bool)
    requires
        p(new),
        forall|c: clazel_cookie::storage::spec::Cookie| #[trigger] clazel_cookie::storage::spec::same_key(c, new) ==> p(c),
    ensures
        clazel_cookie::storage::spec::insert_a_cookie(jar, new).filter(p) == clazel_cookie::storage::spec::insert_a_cookie(jar.filter(p), new),
{
    let f = jar.filter(p);
    clazel_cookie::storage::lemmas::lemma_find_old_cookie_from(jar, new, 0);
    match clazel_cookie::storage::spec::find_old_cookie(jar, new) {
        None => {
            clazel_cookie::storage::isolation::lemma_find_old_cookie_none(jar, new, 0);
            assert forall|m: int| 0 <= m < f.len() implies !clazel_cookie::storage::spec::same_key(#[trigger] f[m], new) by {
                assert(f.contains(f[m]));
                clazel_cookie::storage::isolation::lemma_filter_elem(jar, p, f[m]);
                let q = choose|q: int| 0 <= q < jar.len() && jar[q] == f[m];
            }
            lemma_find_old_none(f, new, 0);
            clazel_cookie::storage::lemmas::lemma_filter_push(jar, new, p);
        },
        Some(i) => {
            assert(p(jar[i]));
            lemma_filter_remove_at(jar, i, p);
            let k = jar.subrange(0, i).filter(p).len() as int;
            lemma_find_old_before(jar, new, 0, i);
            let pre = jar.subrange(0, i);
            assert forall|m: int| 0 <= m < k implies !clazel_cookie::storage::spec::same_key(#[trigger] f[m], new) by {
                assert(f[m] == pre.filter(p)[m]);
                assert(pre.filter(p).contains(pre.filter(p)[m]));
                clazel_cookie::storage::isolation::lemma_filter_elem(pre, p, pre.filter(p)[m]);
                let q = choose|q: int| 0 <= q < pre.len() && pre[q] == pre.filter(p)[m];
                assert(jar[q] == pre[q]);
            }
            assert(clazel_cookie::storage::spec::same_key(f[k], new));
            lemma_find_old_first(f, new, 0, k);
            jar.remove_ensures(i);
            clazel_cookie::storage::lemmas::lemma_filter_push(jar.remove(i), new, p);
            clazel_cookie::storage::lemmas::lemma_filter_push(f.remove(k), new, p);
        },
    }
}

// ---------------------------------------------------------------------
// Per-root eviction.
// ---------------------------------------------------------------------

/// Two jars equal below `n` have the same victim below `n`.
pub proof fn lemma_victim_prefix(rules: Seq<clazel_psl::spec::Rule>, j1: Seq<clazel_cookie::storage::spec::Cookie>, j2: Seq<clazel_cookie::storage::spec::Cookie>, root: clazel_cookie::matching::spec::CanonicalHost, n: nat)
    requires
        n <= j1.len(),
        n <= j2.len(),
        forall|m: int| 0 <= m < n ==> j1[m] == j2[m],
    ensures
        clazel_cookie::storage::spec::victim_from(rules, j1, root, n) == clazel_cookie::storage::spec::victim_from(rules, j2, root, n),
    decreases n,
{
    if n > 0 {
        lemma_victim_prefix(rules, j1, j2, root, (n - 1) as nat);
        assert(j1[(n - 1) as int] == j2[(n - 1) as int]);
        let previous = clazel_cookie::storage::spec::victim_from(rules, j1, root, (n - 1) as nat);
        clazel_cookie::storage::lemmas::lemma_victim_from_in_root(rules, j1, root, (n - 1) as nat);
        if let Some(j) = previous {
            assert(j1[j] == j2[j]);
        }
    }
}

/// The victim of a jar, seen in the jar of the cookies of the root.
pub proof fn lemma_victim_filter(rules: Seq<clazel_psl::spec::Rule>, jar: Seq<clazel_cookie::storage::spec::Cookie>, root: clazel_cookie::matching::spec::CanonicalHost, n: nat)
    requires
        n <= jar.len(),
    ensures
        ({
            let p = clazel_cookie::storage::spec::in_root(rules, root);
            let f = jar.subrange(0, n as int).filter(p);
            match clazel_cookie::storage::spec::victim_from(rules, jar, root, n) {
                None => f.len() == 0,
                Some(j) => 0 <= j < n && p(jar[j]) && f.len() > 0 && clazel_cookie::storage::spec::victim_from(rules, f, root, f.len()) == Some(
                    jar.subrange(0, j).filter(p).len() as int,
                ),
            }
        }),
    decreases n,
{
    let p = clazel_cookie::storage::spec::in_root(rules, root);
    if n > 0 {
        let m = (n - 1) as nat;
        lemma_victim_filter(rules, jar, root, m);
        let c = jar[m as int];
        let pre = jar.subrange(0, m as int);
        let pre1 = jar.subrange(0, n as int);
        assert(pre1 =~= pre.push(c));
        clazel_cookie::storage::lemmas::lemma_filter_push(pre, c, p);
        let f = pre.filter(p);
        if !p(c) {
            assert(pre1.filter(p) == f);
        } else {
            let f2 = f.push(c);
            assert(pre1.filter(p) == f2);
            // victim_from over f2 below f.len() is that over f.
            lemma_victim_prefix(rules, f2, f, root, f.len());
            match clazel_cookie::storage::spec::victim_from(rules, jar, root, m) {
                None => {
                    assert(f.len() == 0);
                    assert(clazel_cookie::storage::spec::victim_from(rules, f2, root, 0) is None);
                    assert(jar.subrange(0, m as int).filter(p).len() == 0);
                },
                Some(j) => {
                    assert(f.len() > 0);
                    let kj = jar.subrange(0, j).filter(p).len() as int;
                    assert(clazel_cookie::storage::spec::victim_from(rules, f, root, f.len()) == Some(kj));
                    // f[kj] is jar[j].
                    lemma_filter_remove_at(pre, j, p);
                    assert(pre.subrange(0, j) =~= jar.subrange(0, j));
                    assert(f[kj] == jar[j]);
                    assert(f2[kj] == jar[j]);
                    assert(f2[f.len() as int] == c);
                    if clazel_cookie::storage::spec::evicted_before(c, jar[j]) {
                        assert(clazel_cookie::storage::spec::victim_from(rules, jar, root, n) == Some(m as int));
                        assert(jar.subrange(0, m as int).filter(p).len() == f.len());
                    }
                },
            }
        }
    }
}

/// Evicting the excess of a root commutes with taking the cookies of that root.
pub proof fn lemma_evict_over_limit_filter(rules: Seq<clazel_psl::spec::Rule>, jar: Seq<clazel_cookie::storage::spec::Cookie>, root: clazel_cookie::matching::spec::CanonicalHost)
    ensures
        clazel_cookie::storage::spec::evict_over_limit(rules, jar, root).filter(clazel_cookie::storage::spec::in_root(rules, root)) == clazel_cookie::storage::spec::evict_over_limit(rules, jar.filter(clazel_cookie::storage::spec::in_root(rules, root)), root),
    decreases jar.len(),
{
    let p = clazel_cookie::storage::spec::in_root(rules, root);
    let f = jar.filter(p);
    clazel_cookie::storage::lemmas::lemma_filter_idempotent(jar, p);
    assert(clazel_cookie::storage::spec::root_count(rules, jar, root) == f.len());
    assert(clazel_cookie::storage::spec::root_count(rules, f, root) == f.len());
    if f.len() > clazel_cookie::storage::spec::max_cookies_per_root() {
        assert(jar.subrange(0, jar.len() as int) =~= jar);
        lemma_victim_filter(rules, jar, root, jar.len());
        let j = clazel_cookie::storage::spec::victim_from(rules, jar, root, jar.len())->Some_0;
        jar.remove_ensures(j);
        lemma_filter_remove_at(jar, j, p);
        let k = jar.subrange(0, j).filter(p).len() as int;
        lemma_evict_over_limit_filter(rules, jar.remove(j), root);
        assert(clazel_cookie::storage::spec::victim_from(rules, f, root, f.len()) == Some(k));
    }
}

} // verus!
