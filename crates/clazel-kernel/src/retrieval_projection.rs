//! Retrieval seen from one cookie root (item 2.11): the string a getter
//! returns, and the jar after it, depend on the jar only through the
//! unexpired cookies of the request host's root.

#[allow(unused_imports)]
use super::projection::*;
#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// A cookie of an unexpired jar is a cookie of the jar, with a non-empty
/// domain if the jar's are.
pub proof fn lemma_live_cookie_domain_nonempty(jar: Seq<clazel_cookie::storage::spec::Cookie>, now: int, i: int)
    requires
        clazel_cookie::storage::isolation::jar_domains_nonempty(jar),
        0 <= i < clazel_cookie::storage::spec::evict_expired(jar, now).len(),
    ensures
        clazel_cookie::storage::isolation::cookie_domain_nonempty(clazel_cookie::storage::spec::evict_expired(jar, now)[i]),
{
    let live = clazel_cookie::storage::spec::evict_expired(jar, now);
    assert(live.contains(live[i]));
    clazel_cookie::storage::isolation::lemma_filter_elem(jar, clazel_cookie::storage::spec::not_expired(now), live[i]);
    let k = choose|k: int| 0 <= k < jar.len() && jar[k] == live[i];
}

/// The cookie list of a retrieval, as the filter and sort it is.
pub proof fn lemma_retrieval_list_filter(
    rules: Seq<clazel_psl::spec::Rule>,
    jar: Seq<clazel_cookie::storage::spec::Cookie>,
    url: clazel_cookie::storage::spec::RequestUrl,
    ctx: clazel_cookie::storage::spec::RequestContext,
    host: clazel_cookie::matching::spec::CanonicalHost,
)
    requires
        url.host == Some(host),
    ensures
        clazel_cookie::storage::spec::retrieval_cookie_list(rules, jar, url, ctx) == clazel_cookie::storage::spec::sort_cookie_list(
            jar.filter(|c: clazel_cookie::storage::spec::Cookie| clazel_cookie::storage::spec::cookie_is_retrieved(rules, url, ctx, host, c)),
        ),
{
}

/// The cookie list of a retrieval is a function of the jar's cookies under
/// the host's root.
pub proof fn lemma_retrieval_list_agree(
    rules: Seq<clazel_psl::spec::Rule>,
    la: Seq<clazel_cookie::storage::spec::Cookie>,
    lb: Seq<clazel_cookie::storage::spec::Cookie>,
    url: clazel_cookie::storage::spec::RequestUrl,
    ctx: clazel_cookie::storage::spec::RequestContext,
    host: clazel_cookie::matching::spec::CanonicalHost,
    root: clazel_cookie::matching::spec::CanonicalHost,
)
    requires
        url.host == Some(host),
        root == clazel_cookie::storage::spec::cookie_root(rules, host),
        clazel_cookie::storage::isolation::jar_domains_nonempty(la),
        clazel_cookie::storage::isolation::jar_domains_nonempty(lb),
        clazel_cookie::storage::spec::cookies_of_root(rules, la, root) == clazel_cookie::storage::spec::cookies_of_root(rules, lb, root),
    ensures
        clazel_cookie::storage::spec::retrieval_cookie_list(rules, la, url, ctx) == clazel_cookie::storage::spec::retrieval_cookie_list(rules, lb, url, ctx),
{
    let pc = |c: clazel_cookie::storage::spec::Cookie| clazel_cookie::storage::spec::cookie_is_retrieved(rules, url, ctx, host, c);
    let p = clazel_cookie::storage::spec::in_root(rules, root);
    lemma_retrieval_list_filter(rules, la, url, ctx, host);
    lemma_retrieval_list_filter(rules, lb, url, ctx, host);
    assert forall|i: int| 0 <= i < la.len() && pc(#[trigger] la[i]) implies p(la[i]) by {
        clazel_cookie::storage::isolation::lemma_retrieve_within_root(rules, url, ctx, host, la[i]);
    }
    assert forall|i: int| 0 <= i < lb.len() && pc(#[trigger] lb[i]) implies p(lb[i]) by {
        clazel_cookie::storage::isolation::lemma_retrieve_within_root(rules, url, ctx, host, lb[i]);
    }
    lemma_filter_implies(la, pc, p);
    lemma_filter_implies(lb, pc, p);
}

/// The cookie string of a retrieval is a function of the unexpired cookies
/// under the host's root.
pub proof fn lemma_retrieval_agree(
    rules: Seq<clazel_psl::spec::Rule>,
    ja: Seq<clazel_cookie::storage::spec::Cookie>,
    jb: Seq<clazel_cookie::storage::spec::Cookie>,
    url: clazel_cookie::storage::spec::RequestUrl,
    ctx: clazel_cookie::storage::spec::RequestContext,
    now: int,
    host: clazel_cookie::matching::spec::CanonicalHost,
    root: clazel_cookie::matching::spec::CanonicalHost,
)
    requires
        url.host == Some(host),
        root == clazel_cookie::storage::spec::cookie_root(rules, host),
        clazel_cookie::storage::isolation::jar_domains_nonempty(ja),
        clazel_cookie::storage::isolation::jar_domains_nonempty(jb),
        live_root(rules, ja, now, root) == live_root(rules, jb, now, root),
    ensures
        clazel_cookie::storage::spec::retrieve_cookie_string(rules, ja, url, ctx, now) == clazel_cookie::storage::spec::retrieve_cookie_string(rules, jb, url, ctx, now),
{
    let la = clazel_cookie::storage::spec::evict_expired(ja, now);
    let lb = clazel_cookie::storage::spec::evict_expired(jb, now);
    assert forall|i: int| 0 <= i < la.len() implies clazel_cookie::storage::isolation::cookie_domain_nonempty(#[trigger] la[i]) by {
        lemma_live_cookie_domain_nonempty(ja, now, i);
    }
    assert forall|i: int| 0 <= i < lb.len() implies clazel_cookie::storage::isolation::cookie_domain_nonempty(#[trigger] lb[i]) by {
        lemma_live_cookie_domain_nonempty(jb, now, i);
    }
    lemma_retrieval_list_agree(rules, la, lb, url, ctx, host, root);
}

/// `update_last_access_time` does not change a cookie's root.
pub proof fn lemma_update_keeps_root(
    rules: Seq<clazel_psl::spec::Rule>,
    url: clazel_cookie::storage::spec::RequestUrl,
    ctx: clazel_cookie::storage::spec::RequestContext,
    host: clazel_cookie::matching::spec::CanonicalHost,
    now: int,
    root: clazel_cookie::matching::spec::CanonicalHost,
)
    ensures
        forall|c: clazel_cookie::storage::spec::Cookie| #[trigger] clazel_cookie::storage::spec::in_root(rules, root)(clazel_cookie::storage::spec::update_last_access_time(rules, url, ctx, host, now)(c)) == clazel_cookie::storage::spec::in_root(rules, root)(c),
        forall|c: clazel_cookie::storage::spec::Cookie| #[trigger] clazel_cookie::storage::spec::not_expired(now)(clazel_cookie::storage::spec::update_last_access_time(rules, url, ctx, host, now)(c)) == clazel_cookie::storage::spec::not_expired(now)(c),
{
    let f = clazel_cookie::storage::spec::update_last_access_time(rules, url, ctx, host, now);
    assert forall|c: clazel_cookie::storage::spec::Cookie| #[trigger] clazel_cookie::storage::spec::in_root(rules, root)(f(c)) == clazel_cookie::storage::spec::in_root(rules, root)(c) by {
        if clazel_cookie::storage::spec::cookie_is_retrieved(rules, url, ctx, host, c) {
            assert(f(c) == clazel_cookie::storage::spec::with_last_access_time(c, now));
        } else {
            assert(f(c) == c);
        }
    }
    assert forall|c: clazel_cookie::storage::spec::Cookie| #[trigger] clazel_cookie::storage::spec::not_expired(now)(f(c)) == clazel_cookie::storage::spec::not_expired(now)(c) by {
        if clazel_cookie::storage::spec::cookie_is_retrieved(rules, url, ctx, host, c) {
            assert(f(c) == clazel_cookie::storage::spec::with_last_access_time(c, now));
        } else {
            assert(f(c) == c);
        }
    }
}

/// The unexpired cookies of a root after a retrieval for that root are those
/// before, updated.
pub proof fn lemma_retrieval_jar_live_root(
    rules: Seq<clazel_psl::spec::Rule>,
    jar: Seq<clazel_cookie::storage::spec::Cookie>,
    url: clazel_cookie::storage::spec::RequestUrl,
    ctx: clazel_cookie::storage::spec::RequestContext,
    now: int,
    host: clazel_cookie::matching::spec::CanonicalHost,
    root: clazel_cookie::matching::spec::CanonicalHost,
)
    requires
        url.host == Some(host),
    ensures
        live_root(rules, clazel_cookie::storage::spec::jar_after_retrieval(rules, jar, url, ctx, now), now, root) == live_root(rules, jar, now, root).map_values(
            clazel_cookie::storage::spec::update_last_access_time(rules, url, ctx, host, now),
        ),
{
    let live = clazel_cookie::storage::spec::evict_expired(jar, now);
    let f = clazel_cookie::storage::spec::update_last_access_time(rules, url, ctx, host, now);
    let ne = clazel_cookie::storage::spec::not_expired(now);
    let p = clazel_cookie::storage::spec::in_root(rules, root);
    lemma_update_keeps_root(rules, url, ctx, host, now, root);
    let mapped = live.map_values(f);
    assert(clazel_cookie::storage::spec::jar_after_retrieval(rules, jar, url, ctx, now) == mapped);
    // evict_expired(mapped) = mapped.filter(ne) = live.filter(ne).map(f) = live.map(f)
    lemma_map_filter(live, f, ne);
    clazel_cookie::storage::lemmas::lemma_filter_idempotent(jar, ne);
    assert(live.filter(ne) == live);
    assert(clazel_cookie::storage::spec::evict_expired(mapped, now) == mapped);
    lemma_map_filter(live, f, p);
}

/// Two jars that agree on the unexpired cookies of a root still agree after
/// a retrieval for that root.
pub proof fn lemma_retrieval_jar_agree(
    rules: Seq<clazel_psl::spec::Rule>,
    ja: Seq<clazel_cookie::storage::spec::Cookie>,
    jb: Seq<clazel_cookie::storage::spec::Cookie>,
    url: clazel_cookie::storage::spec::RequestUrl,
    ctx: clazel_cookie::storage::spec::RequestContext,
    now: int,
    host: clazel_cookie::matching::spec::CanonicalHost,
    root: clazel_cookie::matching::spec::CanonicalHost,
)
    requires
        url.host == Some(host),
        live_root(rules, ja, now, root) == live_root(rules, jb, now, root),
    ensures
        live_root(rules, clazel_cookie::storage::spec::jar_after_retrieval(rules, ja, url, ctx, now), now, root) == live_root(
            rules,
            clazel_cookie::storage::spec::jar_after_retrieval(rules, jb, url, ctx, now),
            now,
            root,
        ),
{
    lemma_retrieval_jar_live_root(rules, ja, url, ctx, now, host, root);
    lemma_retrieval_jar_live_root(rules, jb, url, ctx, now, host, root);
}

} // verus!
