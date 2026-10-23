//! `independent.rs` (RFC 6265, 2011, §5.3 and §5.4) is equal to the spec
//! (RFC 6265bis draft 22, §5.7 and §5.8) on the class the lemmas below
//! state.
//!
//! The RFCs agree only where the newer draft added nothing. The class
//! excludes, in each lemma's hypotheses:
//!
//! - the SameSite attribute (an attribute list that agrees with a
//!   `Seq<Attr6265>` has none), and requests the draft would treat as
//!   cross-site (the hypothesis `step_18_continues` for storage, and
//!   `is_same_site_request` for retrieval): RFC 6265 has no SameSite;
//! - cookie name prefixes `__Secure-` and `__Host-` (§5.4 of the draft);
//! - the secure-overwrite rule (§5.7 step 16) and the rejection of a
//!   `Secure` cookie from an insecure request (step 13), which RFC 6265
//!   lacks;
//! - the draft's early rejections: both name and value empty, a CTL octet,
//!   name and value over 4096 octets, a `Domain` attribute over 1024 octets
//!   or with an octet outside CHAR, a `Path` over 1024 octets;
//! - IP-address hosts (the RFC 6265 transcription keeps `is_ip` but the
//!   "identical" test of the draft compares it too), and jars in which a
//!   cookie with the new cookie's name, domain and path has the other
//!   host-only-flag (RFC 6265 does not distinguish them, the draft keys on
//!   it);
//! - retrieval of a nameless cookie (the draft omits the "=", RFC 6265
//!   writes it), and of a non-host-only cookie whose domain is a public
//!   suffix (the draft excludes it, RFC 6265 has no such condition in §5.4);
//! - the per-root eviction, which is not RFC 6265's (the equivalence is of
//!   the steps up to insertion: `create_a_cookie` and `insert_a_cookie`);
//! - instants: the latest representable date of a session cookie is
//!   `u64::MAX` in the spec and `i64::MAX` in the transcription, so two
//!   cookies agree when they have the same expiry-time, or are both session
//!   cookies; `now` is below `i64::MAX`.
//!
//! Domain-match, path-match and default-path are the same functions on both
//! sides up to `crate::matching::independent`'s proven agreement.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------
// What "the same" means.
// ---------------------------------------------------------------------

/// A canonical host and a [`Host6265`] are the same.
pub open spec fn host_agrees(h: crate::matching::spec::CanonicalHost, h6: super::independent::Host6265) -> bool {
    h.name == h6.name && h.is_ip_address == h6.is_ip
}

/// A request URL and a [`Request6265`] are the same.
pub open spec fn request_agrees(url: RequestUrl, req: super::independent::Request6265) -> bool {
    url.path == req.path && req.secure == url_is_secure(url) && (match (url.host, req.host) {
        (None, None) => true,
        (Some(h), Some(h6)) => host_agrees(h, h6),
        _ => false,
    })
}

/// A parsed attribute and an [`Attr6265`] are the same. A SameSite
/// attribute agrees with nothing.
pub open spec fn attr_agrees(a: crate::set_cookie::spec::Attribute, b: super::independent::Attr6265) -> bool {
    match (a, b) {
        (crate::set_cookie::spec::Attribute::Expires(x), super::independent::Attr6265::Expires(y)) => x == y,
        (crate::set_cookie::spec::Attribute::MaxAge(x), super::independent::Attr6265::MaxAge(y)) => x == y,
        (crate::set_cookie::spec::Attribute::Domain(x), super::independent::Attr6265::Domain(y)) => x == y,
        (crate::set_cookie::spec::Attribute::Path(x), super::independent::Attr6265::Path(y)) => x == y,
        (crate::set_cookie::spec::Attribute::Secure, super::independent::Attr6265::Secure) => true,
        (crate::set_cookie::spec::Attribute::HttpOnly, super::independent::Attr6265::HttpOnly) => true,
        _ => false,
    }
}

/// Two attribute lists are the same, entry by entry.
pub open spec fn attrs_agree(a: Seq<crate::set_cookie::spec::Attribute>, b: Seq<super::independent::Attr6265>) -> bool {
    a.len() == b.len() && forall|i: int| 0 <= i < a.len() ==> attr_agrees(#[trigger] a[i], b[i])
}

/// A stored cookie and a [`Cookie6265`] are the same (the SameSite flag is
/// not compared). The expiry-times are equal, or both are session cookies.
pub open spec fn cookie_agrees(c: Cookie, d: super::independent::Cookie6265) -> bool {
    c.name == d.name && c.value == d.value && c.domain.name == d.domain.name && c.domain.is_ip_address == d.domain.is_ip && c.path
        == d.path && c.creation_time == d.creation_time && c.last_access_time == d.last_access_time && c.persistent_flag
        == d.persistent_flag && c.host_only_flag == d.host_only_flag && c.secure_only_flag == d.secure_only_flag
        && c.http_only_flag == d.http_only_flag && (c.expiry_time == d.expiry_time || (!c.persistent_flag && c.expiry_time
        == latest_representable() && d.expiry_time == super::independent::latest_date_6265()))
}

/// Two jars are the same, cookie by cookie.
pub open spec fn jars_agree(a: Seq<Cookie>, b: Seq<super::independent::Cookie6265>) -> bool {
    a.len() == b.len() && forall|i: int| 0 <= i < a.len() ==> cookie_agrees(#[trigger] a[i], b[i])
}

// ---------------------------------------------------------------------
// Filters, maps and eviction respect the correspondence.
// ---------------------------------------------------------------------

/// Filtering two jars by predicates that agree on corresponding cookies
/// keeps corresponding cookies.
pub proof fn lemma_filter_agree(a: Seq<Cookie>, b: Seq<super::independent::Cookie6265>, p: spec_fn(Cookie) -> bool, q: spec_fn(super::independent::Cookie6265) -> bool)
    requires
        jars_agree(a, b),
        forall|i: int| 0 <= i < a.len() ==> p(#[trigger] a[i]) == q(b[i]),
    ensures
        jars_agree(a.filter(p), b.filter(q)),
    decreases a.len(),
{
    reveal(Seq::filter);
    if a.len() > 0 {
        let at = a.drop_last();
        let bt = b.drop_last();
        assert forall|i: int| 0 <= i < at.len() implies cookie_agrees(#[trigger] at[i], bt[i]) by {
            assert(at[i] == a[i]);
            assert(bt[i] == b[i]);
        }
        assert forall|i: int| 0 <= i < at.len() implies p(#[trigger] at[i]) == q(bt[i]) by {
            assert(at[i] == a[i]);
            assert(bt[i] == b[i]);
        }
        lemma_filter_agree(at, bt, p, q);
        let last = a.len() - 1;
        assert(a.last() == a[last]);
        assert(b.last() == b[last]);
        if p(a.last()) {
            let fa = at.filter(p);
            let fb = bt.filter(q);
            assert forall|i: int| 0 <= i < fa.push(a.last()).len() implies cookie_agrees(#[trigger] fa.push(a.last())[i], fb.push(b.last())[i]) by {
                if i < fa.len() {
                    assert(fa.push(a.last())[i] == fa[i]);
                    assert(fb.push(b.last())[i] == fb[i]);
                }
            }
        }
    }
}

/// A named predicate for the transcription's "not expired".
pub open spec fn alive6(now: int) -> spec_fn(super::independent::Cookie6265) -> bool {
    |c: super::independent::Cookie6265| !super::independent::is_expired_6265(c, now)
}

/// The transcription's eviction is a filter by [`alive6`].
pub proof fn lemma_evict_expired_6265_is_filter(jar: Seq<super::independent::Cookie6265>, now: int)
    ensures
        super::independent::evict_expired_6265(jar, now) == jar.filter(alive6(now)),
{
    assert((|c: super::independent::Cookie6265| !super::independent::is_expired_6265(c, now)) =~= alive6(now));
}

/// Expiry agrees on corresponding cookies, for a `now` below the
/// transcription's latest date.
pub proof fn lemma_expired_agrees(c: Cookie, d: super::independent::Cookie6265, now: int)
    requires
        cookie_agrees(c, d),
        now < super::independent::latest_date_6265(),
        now <= latest_representable(),
    ensures
        cookie_expired(c, now) == super::independent::is_expired_6265(d, now),
{
}

/// Evicting expired cookies keeps the jars the same.
pub proof fn lemma_evict_expired_agrees(a: Seq<Cookie>, b: Seq<super::independent::Cookie6265>, now: int)
    requires
        jars_agree(a, b),
        0 <= now < super::independent::latest_date_6265(),
    ensures
        jars_agree(evict_expired(a, now), super::independent::evict_expired_6265(b, now)),
{
    lemma_evict_expired_6265_is_filter(b, now);
    assert forall|i: int| 0 <= i < a.len() implies not_expired(now)(#[trigger] a[i]) == alive6(now)(b[i]) by {
        lemma_expired_agrees(a[i], b[i], now);
    }
    lemma_filter_agree(a, b, not_expired(now), alive6(now));
}

// ---------------------------------------------------------------------
// The listing order.
// ---------------------------------------------------------------------

/// Corresponding cookies are listed before corresponding cookies alike.
pub proof fn lemma_listed_before_agrees(c: Cookie, d: super::independent::Cookie6265, c2: Cookie, d2: super::independent::Cookie6265)
    requires
        cookie_agrees(c, d),
        cookie_agrees(c2, d2),
    ensures
        cookie_listed_before(c, c2) == super::independent::listed_before_6265(d, d2),
{
}

/// No cookie of `s` is listed after `c`.
pub open spec fn no_after(s: Seq<Cookie>, c: Cookie) -> bool {
    forall|i: int| 0 <= i < s.len() ==> !cookie_listed_before(c, #[trigger] s[i])
}

/// `s` is sorted: no cookie is listed before an earlier one.
pub open spec fn sorted(s: Seq<Cookie>) -> bool {
    forall|i: int, j: int| 0 <= i < j < s.len() ==> !cookie_listed_before(#[trigger] s[j], #[trigger] s[i])
}

/// Inserting into a list that has nothing listed after `c` appends.
pub proof fn lemma_insert_sorted_append(s: Seq<Cookie>, c: Cookie)
    requires
        no_after(s, c),
    ensures
        insert_sorted(s, c) == s.push(c),
    decreases s.len(),
{
    if s.len() > 0 {
        let rest = s.skip(1);
        assert forall|i: int| 0 <= i < rest.len() implies !cookie_listed_before(c, #[trigger] rest[i]) by {
            assert(rest[i] == s[i + 1]);
        }
        lemma_insert_sorted_append(rest, c);
        assert(s.push(c) =~= seq![s[0]] + rest.push(c));
    } else {
        assert(s.push(c) =~= seq![c]);
    }
}

/// Inserting after a last element `x` that `c` is listed before, when
/// something earlier is listed after `c`, inserts before it.
pub proof fn lemma_insert_sorted_push_after(s: Seq<Cookie>, x: Cookie, c: Cookie)
    requires
        !no_after(s, c),
    ensures
        insert_sorted(s.push(x), c) == insert_sorted(s, c).push(x),
    decreases s.len(),
{
    let k = choose|k: int| 0 <= k < s.len() && cookie_listed_before(c, s[k]);
    if cookie_listed_before(c, s[0]) {
        assert(s.push(x) =~= seq![s[0]] + s.skip(1).push(x));
        assert(insert_sorted(s.push(x), c) =~= seq![c] + s.push(x));
        assert(insert_sorted(s, c) =~= seq![c] + s);
        assert((seq![c] + s).push(x) =~= seq![c] + s.push(x));
    } else {
        let rest = s.skip(1);
        assert(rest[k - 1] == s[k]);
        assert(!no_after(rest, c));
        lemma_insert_sorted_push_after(rest, x, c);
        assert(s.push(x).skip(1) =~= rest.push(x));
        assert(s.push(x)[0] == s[0]);
        assert((seq![s[0]] + insert_sorted(rest, c)).push(x) =~= seq![s[0]] + insert_sorted(rest, c).push(x));
    }
}

/// Inserting a cookie listed before the last one, when nothing earlier is
/// listed after it, puts it just before the last.
pub proof fn lemma_insert_sorted_before_last(s: Seq<Cookie>, x: Cookie, c: Cookie)
    requires
        no_after(s, c),
        cookie_listed_before(c, x),
    ensures
        insert_sorted(s.push(x), c) == s.push(c).push(x),
    decreases s.len(),
{
    if s.len() == 0 {
        assert(s.push(x) =~= seq![x]);
        assert(s.push(c).push(x) =~= seq![c, x]);
    } else {
        let rest = s.skip(1);
        assert forall|i: int| 0 <= i < rest.len() implies !cookie_listed_before(c, #[trigger] rest[i]) by {
            assert(rest[i] == s[i + 1]);
        }
        lemma_insert_sorted_before_last(rest, x, c);
        assert(s.push(x).skip(1) =~= rest.push(x));
        assert(s.push(x)[0] == s[0]);
        assert(!cookie_listed_before(c, s[0]));
        assert(s.push(c).push(x) =~= seq![s[0]] + rest.push(c).push(x));
    }
}

/// Inserting into the list gives only its cookies and the new one, one
/// more.
pub proof fn lemma_insert_sorted_elements(s: Seq<Cookie>, c: Cookie)
    ensures
        insert_sorted(s, c).len() == s.len() + 1,
        forall|y: Cookie| insert_sorted(s, c).contains(y) ==> (s.contains(y) || y == c),
    decreases s.len(),
{
    if s.len() > 0 && !cookie_listed_before(c, s[0]) {
        let rest = s.skip(1);
        lemma_insert_sorted_elements(rest, c);
        assert forall|y: Cookie| insert_sorted(s, c).contains(y) implies (s.contains(y) || y == c) by {
            let k = choose|k: int| 0 <= k < insert_sorted(s, c).len() && insert_sorted(s, c)[k] == y;
            if k == 0 {
                assert(s[0] == y);
            } else {
                assert(insert_sorted(rest, c)[k - 1] == y);
                assert(insert_sorted(rest, c).contains(y));
                if rest.contains(y) {
                    let m = choose|m: int| 0 <= m < rest.len() && rest[m] == y;
                    assert(s[m + 1] == y);
                }
            }
        }
    } else if s.len() > 0 {
        assert forall|y: Cookie| insert_sorted(s, c).contains(y) implies (s.contains(y) || y == c) by {
            let k = choose|k: int| 0 <= k < insert_sorted(s, c).len() && insert_sorted(s, c)[k] == y;
            if k > 0 {
                assert((seq![c] + s)[k] == s[k - 1]);
            }
        }
    } else {
        assert forall|y: Cookie| insert_sorted(s, c).contains(y) implies (s.contains(y) || y == c) by {
            let k = choose|k: int| 0 <= k < insert_sorted(s, c).len() && insert_sorted(s, c)[k] == y;
        }
    }
}

/// Insertion keeps the list sorted.
pub proof fn lemma_insert_sorted_sorted(s: Seq<Cookie>, c: Cookie)
    requires
        sorted(s),
    ensures
        sorted(insert_sorted(s, c)),
    decreases s.len(),
{
    if s.len() == 0 {
        assert(insert_sorted(s, c) =~= seq![c]);
    } else if cookie_listed_before(c, s[0]) {
        let r = seq![c] + s;
        assert forall|i: int, j: int| 0 <= i < j < r.len() implies !cookie_listed_before(#[trigger] r[j], #[trigger] r[i]) by {
            if i == 0 {
                assert(r[0] == c);
                assert(r[j] == s[j - 1]);
                if j - 1 > 0 {
                    assert(!cookie_listed_before(s[j - 1], s[0]));
                }
            } else {
                assert(r[i] == s[i - 1]);
                assert(r[j] == s[j - 1]);
            }
        }
    } else {
        let rest = s.skip(1);
        assert forall|i: int, j: int| 0 <= i < j < rest.len() implies !cookie_listed_before(#[trigger] rest[j], #[trigger] rest[i]) by {
            assert(rest[i] == s[i + 1]);
            assert(rest[j] == s[j + 1]);
        }
        lemma_insert_sorted_sorted(rest, c);
        lemma_insert_sorted_elements(rest, c);
        let ins = insert_sorted(rest, c);
        let r = seq![s[0]] + ins;
        assert(r =~= insert_sorted(s, c));
        assert forall|i: int, j: int| 0 <= i < j < r.len() implies !cookie_listed_before(#[trigger] r[j], #[trigger] r[i]) by {
            if i == 0 {
                assert(r[0] == s[0]);
                assert(r[j] == ins[j - 1]);
                assert(ins.contains(ins[j - 1]));
                if ins[j - 1] != c {
                    assert(rest.contains(ins[j - 1]));
                    let m = choose|m: int| 0 <= m < rest.len() && rest[m] == ins[j - 1];
                    assert(s[m + 1] == ins[j - 1]);
                }
            } else {
                assert(r[i] == ins[i - 1]);
                assert(r[j] == ins[j - 1]);
            }
        }
    }
}

/// The transcription's insertion into the same list as the spec's, when the
/// list is sorted, and the cookies correspond.
pub proof fn lemma_insert_sorted_agrees(s: Seq<Cookie>, s6: Seq<super::independent::Cookie6265>, c: Cookie, c6: super::independent::Cookie6265)
    requires
        sorted(s),
        jars_agree(s, s6),
        cookie_agrees(c, c6),
    ensures
        jars_agree(insert_sorted(s, c), super::independent::insert_sorted_6265(s6, c6)),
    decreases s.len(),
{
    if s.len() == 0 {
        assert(insert_sorted(s, c) =~= seq![c]);
        assert(super::independent::insert_sorted_6265(s6, c6) =~= seq![c6]);
    } else {
        let t = s.drop_last();
        let t6 = s6.drop_last();
        let x = s.last();
        let x6 = s6.last();
        assert(s.last() == s[s.len() - 1]);
        assert(s6.last() == s6[s.len() - 1]);
        assert(s =~= t.push(x));
        assert(s6 =~= t6.push(x6));
        assert(s6[s6.len() - 1] == x6);
        assert forall|i: int, j: int| 0 <= i < j < t.len() implies !cookie_listed_before(#[trigger] t[j], #[trigger] t[i]) by {
            assert(t[i] == s[i]);
            assert(t[j] == s[j]);
        }
        assert forall|i: int| 0 <= i < t.len() implies cookie_agrees(#[trigger] t[i], t6[i]) by {
            assert(t[i] == s[i]);
            assert(t6[i] == s6[i]);
        }
        lemma_listed_before_agrees(c, c6, x, x6);
        assert(s6.subrange(0, s6.len() - 1) =~= t6);
        if cookie_listed_before(c, x) {
            // Both put `c` before the last element.
            assert(super::independent::insert_sorted_6265(s6, c6) == super::independent::insert_sorted_6265(t6, c6).push(x6));
            lemma_insert_sorted_agrees(t, t6, c, c6);
            if no_after(t, c) {
                lemma_insert_sorted_before_last(t, x, c);
                lemma_insert_sorted_append(t, c);
            } else {
                lemma_insert_sorted_push_after(t, x, c);
            }
            let l = insert_sorted(t, c);
            let l6 = super::independent::insert_sorted_6265(t6, c6);
            assert forall|i: int| 0 <= i < l.push(x).len() implies cookie_agrees(#[trigger] l.push(x)[i], l6.push(x6)[i]) by {
                if i < l.len() {
                    assert(l.push(x)[i] == l[i]);
                    assert(l6.push(x6)[i] == l6[i]);
                }
            }
        } else {
            // Nothing in `s` is listed after `c`, so both append.
            assert(super::independent::insert_sorted_6265(s6, c6) == s6.push(c6));
            assert forall|i: int| 0 <= i < s.len() implies !cookie_listed_before(c, #[trigger] s[i]) by {
                if i < s.len() - 1 {
                    assert(!cookie_listed_before(x, s[i]));
                }
            }
            lemma_insert_sorted_append(s, c);
            assert forall|i: int| 0 <= i < s.push(c).len() implies cookie_agrees(#[trigger] s.push(c)[i], s6.push(c6)[i]) by {
                if i < s.len() {
                    assert(s.push(c)[i] == s[i]);
                    assert(s6.push(c6)[i] == s6[i]);
                }
            }
        }
    }
}

/// Appending an element to the list sorts as inserting it into the sort of
/// the list.
pub proof fn lemma_sort_from_push(list: Seq<Cookie>, x: Cookie, i: nat, s: Seq<Cookie>)
    requires
        i <= list.len(),
    ensures
        sort_from(list.push(x), i, s) == insert_sorted(sort_from(list, i, s), x),
    decreases list.len() - i,
{
    if i < list.len() {
        assert(list.push(x)[i as int] == list[i as int]);
        lemma_sort_from_push(list, x, i + 1, insert_sorted(s, list[i as int]));
    } else {
        assert(list.push(x)[i as int] == x);
        assert(list.push(x).len() == i + 1);
        assert(sort_from(list, i, s) == s);
        assert(sort_from(list.push(x), i, s) == sort_from(list.push(x), i + 1, insert_sorted(s, x)));
        assert(sort_from(list.push(x), i + 1, insert_sorted(s, x)) == insert_sorted(s, x));
    }
}

/// The spec's sort of a list is sorted, and the transcription's sort of the
/// corresponding list corresponds to it.
pub proof fn lemma_sort_agrees(list: Seq<Cookie>, list6: Seq<super::independent::Cookie6265>)
    requires
        jars_agree(list, list6),
    ensures
        sorted(sort_cookie_list(list)),
        jars_agree(sort_cookie_list(list), super::independent::sort_cookie_list_6265(list6)),
    decreases list.len(),
{
    if list.len() == 0 {
        assert(sort_cookie_list(list) =~= Seq::<Cookie>::empty());
    } else {
        let t = list.drop_last();
        let t6 = list6.drop_last();
        let x = list.last();
        let x6 = list6.last();
        assert(list.last() == list[list.len() - 1]);
        assert(list6.last() == list6[list.len() - 1]);
        assert forall|i: int| 0 <= i < t.len() implies cookie_agrees(#[trigger] t[i], t6[i]) by {
            assert(t[i] == list[i]);
            assert(t6[i] == list6[i]);
        }
        lemma_sort_agrees(t, t6);
        assert(list =~= t.push(x));
        lemma_sort_from_push(t, x, 0, seq![]);
        assert(sort_cookie_list(list) == insert_sorted(sort_cookie_list(t), x));
        lemma_insert_sorted_sorted(sort_cookie_list(t), x);
        lemma_insert_sorted_agrees(sort_cookie_list(t), super::independent::sort_cookie_list_6265(t6), x, x6);
        assert(list6.subrange(0, list6.len() - 1) =~= t6);
    }
}


// ---------------------------------------------------------------------
// §5.4: retrieval.
// ---------------------------------------------------------------------

/// A filter that rejects everything is empty.
pub proof fn lemma_filter_none<A>(s: Seq<A>, p: spec_fn(A) -> bool)
    requires
        forall|i: int| 0 <= i < s.len() ==> !p(#[trigger] s[i]),
    ensures
        s.filter(p) == Seq::<A>::empty(),
    decreases s.len(),
{
    reveal(Seq::filter);
    if s.len() > 0 {
        let t = s.drop_last();
        assert forall|i: int| 0 <= i < t.len() implies !p(#[trigger] t[i]) by {
            assert(t[i] == s[i]);
        }
        lemma_filter_none(t, p);
        assert(s[s.len() - 1] == s.last());
    }
}

/// Every cookie of the list has a name.
pub open spec fn names_nonempty(s: Seq<Cookie>) -> bool {
    forall|i: int| 0 <= i < s.len() ==> (#[trigger] s[i]).name.len() > 0
}

/// The serialization from index `i` on is the transcription's serialization
/// of the rest, when every cookie has a name.
pub proof fn lemma_serialize_agrees(a: Seq<Cookie>, b: Seq<super::independent::Cookie6265>, i: nat)
    requires
        jars_agree(a, b),
        names_nonempty(a),
        i <= a.len(),
    ensures
        serialize_cookie_list_from(a, i) == super::independent::serialize_cookie_list_6265(b.skip(i as int)),
    decreases a.len() - i,
{
    if i < a.len() {
        let rest = b.skip(i as int);
        assert(rest[0] == b[i as int]);
        assert(a[i as int].name.len() > 0);
        if i + 1 < a.len() {
            lemma_serialize_agrees(a, b, i + 1);
            assert(rest.skip(1) =~= b.skip(i as int + 1));
            assert(rest.len() > 1);
        } else {
            assert(rest.len() == 1);
            assert(serialize_cookie_list_from(a, i + 1) == Seq::<u8>::empty());
        }
    } else {
        assert(b.skip(i as int).len() == 0);
    }
}

/// The sort of a list has only its cookies.
pub proof fn lemma_sort_elements(list: Seq<Cookie>)
    ensures
        forall|y: Cookie| sort_cookie_list(list).contains(y) ==> list.contains(y),
    decreases list.len(),
{
    if list.len() > 0 {
        let t = list.drop_last();
        let x = list.last();
        lemma_sort_elements(t);
        assert(list =~= t.push(x));
        lemma_sort_from_push(t, x, 0, seq![]);
        lemma_insert_sorted_elements(sort_cookie_list(t), x);
        assert forall|y: Cookie| sort_cookie_list(list).contains(y) implies list.contains(y) by {
            if y != x {
                assert(sort_cookie_list(t).contains(y));
                assert(t.contains(y));
                let k = choose|k: int| 0 <= k < t.len() && t[k] == y;
                assert(list[k] == y);
            } else {
                assert(list[list.len() - 1] == x);
            }
        }
    }
}

/// What a cookie must be like for §5.8.3 step 3 and §5.4 step 1 to select
/// the same cookies: a host name (not an IP address) with a domain that, if
/// not host-only, is not a public suffix.
pub open spec fn retrievable_class(rules: Seq<clazel_psl::spec::Rule>, c: Cookie) -> bool {
    c.name.len() > 0 && !c.domain.is_ip_address && (!c.host_only_flag ==> !is_public_suffix_string(rules, c.domain.name))
}

/// The two step-1 conditions select the same cookies.
pub proof fn lemma_retrieved_agrees(
    rules: Seq<clazel_psl::spec::Rule>,
    url: RequestUrl,
    ctx: RequestContext,
    h: crate::matching::spec::CanonicalHost,
    req: super::independent::Request6265,
    non_http: bool,
    c: Cookie,
    d: super::independent::Cookie6265,
)
    requires
        url.host == Some(h),
        !h.is_ip_address,
        request_agrees(url, req),
        non_http == is_non_http(ctx),
        is_same_site_request(rules, ctx),
        cookie_agrees(c, d),
        retrievable_class(rules, c),
    ensures
        cookie_is_retrieved(rules, url, ctx, h, c) == super::independent::in_cookie_list_6265(d, req, non_http),
{
    crate::matching::independent::lemma_path_matches_agree(url.path, c.path);
    crate::matching::independent::lemma_domain_matches_agree(h.name, true, c.domain.name);
    assert(req.host == Some(super::independent::Host6265 { name: h.name, is_ip: false }));
    if !c.host_only_flag {
        assert(canonical_domain_matches(h, c.domain) == crate::matching::spec::domain_matches(h.name, true, c.domain.name));
    }
}

/// A named predicate for the transcription's step 1.
pub open spec fn in_list6(req: super::independent::Request6265, non_http: bool) -> spec_fn(super::independent::Cookie6265) -> bool {
    |c: super::independent::Cookie6265| super::independent::in_cookie_list_6265(c, req, non_http)
}

/// The transcription's step 1 is a filter by [`in_list6`].
pub proof fn lemma_cookie_list_unsorted_is_filter(jar: Seq<super::independent::Cookie6265>, req: super::independent::Request6265, non_http: bool)
    ensures
        super::independent::cookie_list_unsorted_6265(jar, req, non_http) == jar.filter(in_list6(req, non_http)),
{
    assert((|c: super::independent::Cookie6265| super::independent::in_cookie_list_6265(c, req, non_http)) =~= in_list6(req, non_http));
}

/// Retrieval agrees: the cookie-string is the same, and so is the jar after
/// step 5 (the transcription's step 3), for a request to a host name, a
/// same-site context, a jar of cookies of the retrievable class, and a
/// `now` below the transcription's latest date.
pub proof fn lemma_retrieve_agrees(
    rules: Seq<clazel_psl::spec::Rule>,
    jar: Seq<Cookie>,
    jar6: Seq<super::independent::Cookie6265>,
    url: RequestUrl,
    ctx: RequestContext,
    req: super::independent::Request6265,
    non_http: bool,
    now: int,
)
    requires
        jars_agree(jar, jar6),
        request_agrees(url, req),
        non_http == is_non_http(ctx),
        is_same_site_request(rules, ctx),
        0 <= now < super::independent::latest_date_6265(),
        url.host matches Some(h) ==> !h.is_ip_address,
        forall|i: int| 0 <= i < jar.len() ==> retrievable_class(rules, #[trigger] jar[i]),
    ensures
        retrieve_cookie_string(rules, jar, url, ctx, now) == super::independent::cookie_string_6265(super::independent::evict_expired_6265(jar6, now), req, non_http),
        jars_agree(
            jar_after_retrieval(rules, jar, url, ctx, now),
            super::independent::update_last_access_6265(super::independent::evict_expired_6265(jar6, now), req, non_http, now),
        ),
{
    let live = evict_expired(jar, now);
    let live6 = super::independent::evict_expired_6265(jar6, now);
    lemma_evict_expired_agrees(jar, jar6, now);
    // The live cookies are among the jar's, so of the class.
    assert forall|i: int| 0 <= i < live.len() implies retrievable_class(rules, #[trigger] live[i]) by {
        assert(live.contains(live[i]));
        super::isolation::lemma_filter_elem(jar, not_expired(now), live[i]);
        let k = choose|k: int| 0 <= k < jar.len() && jar[k] == live[i];
    }
    match url.host {
        None => {
            assert(req.host is None);
            assert forall|i: int| 0 <= i < live6.len() implies !super::independent::in_cookie_list_6265(live6[i], req, non_http) by {}
            lemma_cookie_list_unsorted_is_filter(live6, req, non_http);
            assert forall|i: int| 0 <= i < live6.len() implies !in_list6(req, non_http)(live6[i]) by {}
            lemma_filter_none(live6, in_list6(req, non_http));
            assert(super::independent::sort_cookie_list_6265(Seq::<super::independent::Cookie6265>::empty()) == Seq::<super::independent::Cookie6265>::empty());
            assert(super::independent::cookie_list_unsorted_6265(live6, req, non_http) =~= Seq::<super::independent::Cookie6265>::empty());
            assert(live6.map_values(|c: super::independent::Cookie6265| if super::independent::in_cookie_list_6265(c, req, non_http) { super::independent::Cookie6265 { last_access_time: now, ..c } } else { c }) =~= live6);
        },
        Some(h) => {
            assert(req.host == Some(super::independent::Host6265 { name: h.name, is_ip: false }));
            super::exec::lemma_retrieval_list_is_filter(rules, live, url, ctx, h);
            lemma_cookie_list_unsorted_is_filter(live6, req, non_http);
            assert forall|i: int| 0 <= i < live.len() implies super::exec::retrieved_pred(rules, url, ctx, h)(#[trigger] live[i])
                == in_list6(req, non_http)(live6[i]) by {
                lemma_retrieved_agrees(rules, url, ctx, h, req, non_http, live[i], live6[i]);
            }
            lemma_filter_agree(live, live6, super::exec::retrieved_pred(rules, url, ctx, h), in_list6(req, non_http));
            let list = live.filter(super::exec::retrieved_pred(rules, url, ctx, h));
            let list6 = live6.filter(in_list6(req, non_http));
            lemma_sort_agrees(list, list6);
            // The names of the sorted list.
            assert forall|i: int| 0 <= i < list.len() implies retrievable_class(rules, #[trigger] list[i]) by {
                assert(list.contains(list[i]));
                super::isolation::lemma_filter_elem(live, super::exec::retrieved_pred(rules, url, ctx, h), list[i]);
                let k = choose|k: int| 0 <= k < live.len() && live[k] == list[i];
            }
            lemma_sort_elements(list);
            let sl = sort_cookie_list(list);
            assert forall|i: int| 0 <= i < sl.len() implies (#[trigger] sl[i]).name.len() > 0 by {
                assert(sl.contains(sl[i]));
                assert(list.contains(sl[i]));
                let k = choose|k: int| 0 <= k < list.len() && list[k] == sl[i];
            }
            lemma_serialize_agrees(sl, super::independent::sort_cookie_list_6265(list6), 0);
            assert(super::independent::sort_cookie_list_6265(list6).skip(0) =~= super::independent::sort_cookie_list_6265(list6));
            // Step 5 / the transcription's step 3.
            let f = update_last_access_time(rules, url, ctx, h, now);
            let g = |c: super::independent::Cookie6265| if super::independent::in_cookie_list_6265(c, req, non_http) { super::independent::Cookie6265 { last_access_time: now, ..c } } else { c };
            assert forall|i: int| 0 <= i < live.len() implies cookie_agrees(#[trigger] live.map_values(f)[i], live6.map_values(g)[i]) by {
                assert(live.map_values(f)[i] == f(live[i]));
                assert(live6.map_values(g)[i] == g(live6[i]));
                lemma_retrieved_agrees(rules, url, ctx, h, req, non_http, live[i], live6[i]);
            }
        },
    }
}


// ---------------------------------------------------------------------
// §5.7 and §5.3: storage.
// ---------------------------------------------------------------------

/// "The user agent is configured to reject public suffixes".
pub open spec fn ps_of(rules: Seq<clazel_psl::spec::Rule>) -> spec_fn(Seq<u8>) -> bool {
    |s: Seq<u8>| is_public_suffix_string(rules, s)
}

/// The attribute values the draft's checks of steps 7, 8 and 11 leave alone.
pub open spec fn attrs_plain(a: Seq<crate::set_cookie::spec::Attribute>) -> bool {
    forall|i: int|
        0 <= i < a.len() ==> (match #[trigger] a[i] {
            crate::set_cookie::spec::Attribute::Domain(d) => d.len() <= 1024 && all_char_from(d, 0),
            crate::set_cookie::spec::Attribute::Path(p) => p.len() <= 1024,
            _ => true,
        })
}

/// The cookie of the transcription as the spec stores it (the SameSite flag
/// is "Default", the cookie has no SameSite attribute).
pub open spec fn cookie_of_6265(d: super::independent::Cookie6265) -> Cookie {
    Cookie {
        name: d.name,
        value: d.value,
        expiry_time: if d.persistent_flag {
            d.expiry_time
        } else {
            latest_representable()
        },
        domain: crate::matching::spec::CanonicalHost { name: d.domain.name, is_ip_address: d.domain.is_ip },
        path: d.path,
        creation_time: d.creation_time,
        last_access_time: d.last_access_time,
        persistent_flag: d.persistent_flag,
        host_only_flag: d.host_only_flag,
        secure_only_flag: d.secure_only_flag,
        http_only_flag: d.http_only_flag,
        same_site_flag: crate::set_cookie::spec::SameSite::Default,
    }
}

/// Step 23 of §5.7 for a newly-created cookie `new`.
pub open spec fn step_23(jar: Seq<Cookie>, non_http: bool, new: Cookie) -> Option<Cookie> {
    match find_old_cookie(jar, new) {
        None => Some(new),
        Some(i) => if non_http && jar[i].http_only_flag {
            None
        } else {
            Some(with_creation_time(new, jar[i].creation_time))
        },
    }
}

/// Dropping the last entry of two attribute lists that agree.
pub proof fn lemma_attrs_agree_drop_last(a: Seq<crate::set_cookie::spec::Attribute>, b: Seq<super::independent::Attr6265>)
    requires
        attrs_agree(a, b),
        a.len() > 0,
    ensures
        attrs_agree(a.drop_last(), b.subrange(0, b.len() - 1)),
{
    assert forall|i: int| 0 <= i < a.drop_last().len() implies attr_agrees(#[trigger] a.drop_last()[i], b.subrange(0, b.len() - 1)[i]) by {
        assert(a.drop_last()[i] == a[i]);
        assert(b.subrange(0, b.len() - 1)[i] == b[i]);
    }
}

/// The last Max-Age, Expires, Domain and Path attributes are the same, and
/// there is no SameSite attribute.
pub proof fn lemma_last_attributes_agree(a: Seq<crate::set_cookie::spec::Attribute>, b: Seq<super::independent::Attr6265>)
    requires
        attrs_agree(a, b),
        attrs_plain(a),
    ensures
        last_max_age(a) == super::independent::last_max_age_6265(b),
        last_expires(a) == super::independent::last_expires_6265(b),
        last_domain_within_1024(a) == super::independent::last_domain_6265(b),
        last_path_within_1024(a) == super::independent::last_path_6265(b),
        last_same_site(a) is None,
    decreases a.len(),
{
    if a.len() > 0 {
        lemma_attrs_agree_drop_last(a, b);
        assert forall|i: int| 0 <= i < a.drop_last().len() implies (match #[trigger] a.drop_last()[i] {
            crate::set_cookie::spec::Attribute::Domain(d) => d.len() <= 1024 && all_char_from(d, 0),
            crate::set_cookie::spec::Attribute::Path(p) => p.len() <= 1024,
            _ => true,
        }) by {
            assert(a.drop_last()[i] == a[i]);
        }
        lemma_last_attributes_agree(a.drop_last(), b.subrange(0, b.len() - 1));
        assert(a[a.len() - 1] == a.last());
        assert(attr_agrees(a[a.len() - 1], b[a.len() - 1]));
        assert(b[b.len() - 1] == b[a.len() - 1]);
    }
}

/// A Secure (HttpOnly) attribute is in one list exactly when it is in the
/// other.
pub proof fn lemma_secure_http_only_agree(a: Seq<crate::set_cookie::spec::Attribute>, b: Seq<super::independent::Attr6265>)
    requires
        attrs_agree(a, b),
    ensures
        crate::set_cookie::spec::contains_secure_attribute(a) == super::independent::has_secure_6265(b),
        contains_http_only_attribute(a) == super::independent::has_http_only_6265(b),
{
    if crate::set_cookie::spec::contains_secure_attribute(a) {
        let i = choose|i: int| 0 <= i < a.len() && (#[trigger] a[i]) is Secure;
        assert(b[i] === super::independent::Attr6265::Secure);
    }
    if super::independent::has_secure_6265(b) {
        let i = choose|i: int| 0 <= i < b.len() && b[i] === super::independent::Attr6265::Secure;
        assert(a[i] is Secure);
    }
    if contains_http_only_attribute(a) {
        let i = choose|i: int| 0 <= i < a.len() && (#[trigger] a[i]) is HttpOnly;
        assert(b[i] === super::independent::Attr6265::HttpOnly);
    }
    if super::independent::has_http_only_6265(b) {
        let i = choose|i: int| 0 <= i < b.len() && b[i] === super::independent::Attr6265::HttpOnly;
        assert(a[i] is HttpOnly);
    }
}

/// The first cookie with the key, in the two jars.
pub proof fn lemma_find_old_agrees(jar: Seq<Cookie>, jar6: Seq<super::independent::Cookie6265>, new: Cookie, i: nat)
    requires
        jars_agree(jar, jar6),
        !new.domain.is_ip_address,
        forall|k: int| 0 <= k < jar.len() ==> ((#[trigger] jar[k]).name == new.name ==> (!jar[k].domain.is_ip_address && jar[k].host_only_flag
            == new.host_only_flag)),
        i <= jar.len(),
    ensures
        find_old_cookie_from(jar, new, i) == (match super::independent::find_old_cookie_6265(jar6.skip(i as int), new.name, new.domain.name, new.path) {
            Some(j) => Some(j + i),
            None => None::<int>,
        }),
    decreases jar.len() - i,
{
    if i < jar.len() {
        let rest = jar6.skip(i as int);
        assert(rest.len() > 0);
        assert(rest[0] == jar6[i as int]);
        assert(cookie_agrees(jar[i as int], jar6[i as int]));
        if !same_key(jar[i as int], new) {
            lemma_find_old_agrees(jar, jar6, new, i + 1);
            assert(rest.skip(1) =~= jar6.skip(i as int + 1));
        }
    }
}

/// Step 9 and 10 on the two sides.
pub proof fn lemma_domain_steps_agree(
    rules: Seq<clazel_psl::spec::Rule>,
    h: crate::matching::spec::CanonicalHost,
    da: Seq<u8>,
)
    requires
        !h.is_ip_address,
    ensures
        step_9_domain_attribute(rules, h, da) == (if ps_of(rules)(da) {
            if da == h.name {
                Some(Seq::<u8>::empty())
            } else {
                None::<Seq<u8>>
            }
        } else {
            Some(da)
        }),
{
}

/// The creation of the cookie is, in the class, the transcription's
/// creation followed by step 23.
pub proof fn lemma_create_agrees(
    rules: Seq<clazel_psl::spec::Rule>,
    jar: Seq<Cookie>,
    url: RequestUrl,
    ctx: RequestContext,
    received: crate::set_cookie::spec::SetCookie,
    now: int,
    req: super::independent::Request6265,
    non_http: bool,
    attrs6: Seq<super::independent::Attr6265>,
)
    requires
        request_agrees(url, req),
        non_http == is_non_http(ctx),
        attrs_agree(received.attributes, attrs6),
        attrs_plain(received.attributes),
        url.host matches Some(h) ==> !h.is_ip_address,
        step_18_continues(rules, ctx),
        !(received.name.len() == 0 && received.value.len() == 0),
        !crate::set_cookie::spec::contains_ctl_excluding_htab(received.name),
        !crate::set_cookie::spec::contains_ctl_excluding_htab(received.value),
        received.name.len() + received.value.len() <= 4096,
        !crate::ascii::begins_with_case_insensitive_match(received.name, crate::set_cookie::spec::lit_secure_prefix()),
        !crate::ascii::begins_with_case_insensitive_match(received.name, crate::set_cookie::spec::lit_host_prefix()),
        !(received.name.len() == 0 && (crate::ascii::begins_with_case_insensitive_match(
            received.value,
            crate::set_cookie::spec::lit_secure_prefix(),
        ) || crate::ascii::begins_with_case_insensitive_match(received.value, crate::set_cookie::spec::lit_host_prefix()))),
        url_is_secure(url) || !crate::set_cookie::spec::contains_secure_attribute(received.attributes),
        url_is_secure(url) || forall|k: int| 0 <= k < jar.len() ==> !((#[trigger] jar[k]).secure_only_flag && jar[k].name == received.name),
    ensures
        create_a_cookie(rules, jar, url, ctx, received, now) == (match super::independent::receive_cookie_6265(
            ps_of(rules),
            req,
            non_http,
            received.name,
            received.value,
            attrs6,
            now,
        ) {
            None => None::<Cookie>,
            Some(d) => step_23(jar, non_http, cookie_of_6265(d)),
        }),
{
    lemma_last_attributes_agree(received.attributes, attrs6);
    lemma_secure_http_only_agree(received.attributes, attrs6);
    let attrs = received.attributes;
    if url.host is Some {
        let h = url.host->Some_0;
        assert(req.host == Some(super::independent::Host6265 { name: h.name, is_ip: false }));
        let da = match last_domain_within_1024(attrs) {
            Some(d) => d,
            None => seq![],
        };
        // Step 8: the domain-attribute is CHAR.
        match last_domain_within_1024(attrs) {
            Some(d) => {
                let k = choose|k: int| 0 <= k < attrs.len() && attrs[k] == crate::set_cookie::spec::Attribute::Domain(d);
                lemma_last_domain_is_a_value(attrs);
            },
            None => {},
        }
        assert(all_char_from(da, 0));
        crate::matching::independent::lemma_default_path_agrees(url.path);
        let r9 = step_9_domain_attribute(rules, h, da);
        if r9 is Some {
            let da9 = r9->Some_0;
            if da9.len() > 0 {
                crate::matching::independent::lemma_domain_matches_agree(h.name, true, da9);
            }
        }
    }
}

/// The last Domain attribute within 1024 is the value of some Domain
/// attribute, hence CHAR for a plain attribute list.
pub proof fn lemma_last_domain_is_a_value(a: Seq<crate::set_cookie::spec::Attribute>)
    requires
        attrs_plain(a),
    ensures
        last_domain_within_1024(a) matches Some(d) ==> all_char_from(d, 0),
    decreases a.len(),
{
    if a.len() > 0 {
        assert forall|i: int| 0 <= i < a.drop_last().len() implies (match #[trigger] a.drop_last()[i] {
            crate::set_cookie::spec::Attribute::Domain(d) => d.len() <= 1024 && all_char_from(d, 0),
            crate::set_cookie::spec::Attribute::Path(p) => p.len() <= 1024,
            _ => true,
        }) by {
            assert(a.drop_last()[i] == a[i]);
        }
        lemma_last_domain_is_a_value(a.drop_last());
        assert(a[a.len() - 1] == a.last());
    }
}


/// What the transcription's new cookie is like, for a request to a host
/// name.
pub proof fn lemma_receive_props(
    is_public_suffix: spec_fn(Seq<u8>) -> bool,
    req: super::independent::Request6265,
    non_http: bool,
    name: Seq<u8>,
    value: Seq<u8>,
    attrs6: Seq<super::independent::Attr6265>,
    now: int,
)
    requires
        req.host matches Some(h) ==> !h.is_ip,
    ensures
        super::independent::receive_cookie_6265(is_public_suffix, req, non_http, name, value, attrs6, now) matches Some(d) ==> (!d.domain.is_ip
            && d.creation_time == now && d.last_access_time == now && d.name == name && d.value == value && (!d.persistent_flag
            ==> d.expiry_time == super::independent::latest_date_6265())),
{
}

/// Finding the key ignores the creation-time.
pub proof fn lemma_find_old_ignores_creation(jar: Seq<Cookie>, new: Cookie, t: int, i: nat)
    ensures
        find_old_cookie_from(jar, with_creation_time(new, t), i) == find_old_cookie_from(jar, new, i),
    decreases jar.len() - i,
{
    if i < jar.len() && !same_key(jar[i as int], new) {
        lemma_find_old_ignores_creation(jar, new, t, i + 1);
    }
}

/// Storage agrees, up to and including the insertion: the jar after
/// `create_a_cookie` and `insert_a_cookie` is the transcription's
/// `store_cookie_6265` of the (already evicted) jar, for a request to a host
/// name, in the class of `lemma_create_agrees`, and a jar in which every
/// cookie with the received name is a host-name cookie of the same
/// host-only-flavour as the new cookie.
pub proof fn lemma_store_agrees(
    rules: Seq<clazel_psl::spec::Rule>,
    live: Seq<Cookie>,
    live6: Seq<super::independent::Cookie6265>,
    url: RequestUrl,
    ctx: RequestContext,
    received: crate::set_cookie::spec::SetCookie,
    now: int,
    req: super::independent::Request6265,
    non_http: bool,
    attrs6: Seq<super::independent::Attr6265>,
)
    requires
        jars_agree(live, live6),
        request_agrees(url, req),
        non_http == is_non_http(ctx),
        attrs_agree(received.attributes, attrs6),
        attrs_plain(received.attributes),
        url.host matches Some(h) ==> !h.is_ip_address,
        step_18_continues(rules, ctx),
        !(received.name.len() == 0 && received.value.len() == 0),
        !crate::set_cookie::spec::contains_ctl_excluding_htab(received.name),
        !crate::set_cookie::spec::contains_ctl_excluding_htab(received.value),
        received.name.len() + received.value.len() <= 4096,
        !crate::ascii::begins_with_case_insensitive_match(received.name, crate::set_cookie::spec::lit_secure_prefix()),
        !crate::ascii::begins_with_case_insensitive_match(received.name, crate::set_cookie::spec::lit_host_prefix()),
        !(received.name.len() == 0 && (crate::ascii::begins_with_case_insensitive_match(
            received.value,
            crate::set_cookie::spec::lit_secure_prefix(),
        ) || crate::ascii::begins_with_case_insensitive_match(received.value, crate::set_cookie::spec::lit_host_prefix()))),
        url_is_secure(url) || !crate::set_cookie::spec::contains_secure_attribute(received.attributes),
        url_is_secure(url) || forall|k: int| 0 <= k < live.len() ==> !((#[trigger] live[k]).secure_only_flag && live[k].name == received.name),
        forall|k: int|
            0 <= k < live.len() ==> ((#[trigger] live[k]).name == received.name ==> (!live[k].domain.is_ip_address && (super::independent::receive_cookie_6265(
                ps_of(rules),
                req,
                non_http,
                received.name,
                received.value,
                attrs6,
                now,
            ) matches Some(d) ==> live[k].host_only_flag == d.host_only_flag))),
        0 <= now < super::independent::latest_date_6265(),
    ensures
        ({
            let store6 = super::independent::store_cookie_6265(ps_of(rules), live6, req, non_http, received.name, received.value, attrs6, now);
            match create_a_cookie(rules, live, url, ctx, received, now) {
                None => jars_agree(live, store6),
                Some(new) => jars_agree(insert_a_cookie(live, new), store6),
            }
        }),
{
    lemma_create_agrees(rules, live, url, ctx, received, now, req, non_http, attrs6);
    let received6 = super::independent::receive_cookie_6265(ps_of(rules), req, non_http, received.name, received.value, attrs6, now);
    lemma_receive_props(ps_of(rules), req, non_http, received.name, received.value, attrs6, now);
    if received6 is Some {
        let d = received6->Some_0;
        let new = cookie_of_6265(d);
        assert(cookie_agrees(new, d));
        lemma_find_old_agrees(live, live6, new, 0);
        assert(live6.skip(0) =~= live6);
        super::lemmas::lemma_find_old_cookie_from(live, new, 0);
        let old = find_old_cookie(live, new);
        match old {
            None => {
                assert(insert_a_cookie(live, new) == live.push(new));
                assert forall|i: int| 0 <= i < live.push(new).len() implies cookie_agrees(#[trigger] live.push(new)[i], live6.push(d)[i]) by {
                    if i < live.len() {
                        assert(live.push(new)[i] == live[i]);
                        assert(live6.push(d)[i] == live6[i]);
                    }
                }
            },
            Some(i) => {
                assert(super::independent::find_old_cookie_6265(live6, d.name, d.domain.name, d.path) == Some(i));
                assert(cookie_agrees(live[i], live6[i]));
                if non_http && live[i].http_only_flag {
                } else {
                    let newc = with_creation_time(new, live[i].creation_time);
                    lemma_find_old_ignores_creation(live, new, live[i].creation_time, 0);
                    assert(find_old_cookie(live, newc) == Some(i));
                    let removed = live.remove(i);
                    let removed6 = live6.remove(i);
                    live.remove_ensures(i);
                    live6.remove_ensures(i);
                    let updated = super::independent::Cookie6265 { creation_time: live6[i].creation_time, ..d };
                    assert(cookie_agrees(newc, updated));
                    assert forall|j: int| 0 <= j < removed.push(newc).len() implies cookie_agrees(#[trigger] removed.push(newc)[j], removed6.push(updated)[j]) by {
                        if j < removed.len() {
                            assert(removed.push(newc)[j] == removed[j]);
                            assert(removed6.push(updated)[j] == removed6[j]);
                            if j < i {
                                assert(removed[j] == live[j]);
                                assert(removed6[j] == live6[j]);
                            } else {
                                assert(removed[j] == live[j + 1]);
                                assert(removed6[j] == live6[j + 1]);
                            }
                        }
                    }
                }
            },
        }
    }
}

} // verus!
