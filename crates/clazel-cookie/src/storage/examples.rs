//! Examples evaluated on the spec: Verus computes the storage and retrieval
//! models on concrete hosts, cookies and the five-rule Public Suffix List of
//! `clazel_psl::examples::rules()` (`com`, `uk`, `co.uk`, `*.ck`, `!www.ck`),
//! so a transcription error shows up here as a failed proof. They also serve
//! as the certificates of `mutations.json`.
//!
//! `create_a_cookie` is not evaluated here: three of the functions it calls
//! (`contains_http_only_attribute`, `contains_secure_attribute` and
//! `secure_cookie_would_be_overlaid`) are quantifiers, which Verus's
//! `compute_only` cannot evaluate on a concrete input. Its steps are covered
//! by the proofs against the exec code, by the isolation lemmas and by the
//! conformance suites; the pieces it is built from that can be evaluated
//! (steps 6, 7, 9, 10, 18, 23, the old-cookie search and the insertion) are
//! covered here.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The five-rule list.
pub open spec fn rules() -> Seq<clazel_psl::spec::Rule> {
    clazel_psl::examples::rules()
}

/// "com".
pub open spec fn s_com() -> Seq<u8> {
    seq![0x63u8, 0x6F, 0x6D]
}

/// "a.com".
pub open spec fn s_a_com() -> Seq<u8> {
    seq![0x61u8, 0x2E, 0x63, 0x6F, 0x6D]
}

/// "b.com".
pub open spec fn s_b_com() -> Seq<u8> {
    seq![0x62u8, 0x2E, 0x63, 0x6F, 0x6D]
}

/// "ba.com".
pub open spec fn s_ba_com() -> Seq<u8> {
    seq![0x62u8, 0x61, 0x2E, 0x63, 0x6F, 0x6D]
}

/// "co.uk".
pub open spec fn s_co_uk() -> Seq<u8> {
    seq![0x63u8, 0x6F, 0x2E, 0x75, 0x6B]
}

/// "a.co.uk".
pub open spec fn s_a_co_uk() -> Seq<u8> {
    seq![0x61u8, 0x2E, 0x63, 0x6F, 0x2E, 0x75, 0x6B]
}

/// "x.a.co.uk".
pub open spec fn s_x_a_co_uk() -> Seq<u8> {
    seq![0x78u8, 0x2E, 0x61, 0x2E, 0x63, 0x6F, 0x2E, 0x75, 0x6B]
}

/// "1.2.3.4".
pub open spec fn s_ip() -> Seq<u8> {
    seq![0x31u8, 0x2E, 0x32, 0x2E, 0x33, 0x2E, 0x34]
}

/// "3.4".
pub open spec fn s_3_4() -> Seq<u8> {
    seq![0x33u8, 0x2E, 0x34]
}

/// A host name.
pub open spec fn host(name: Seq<u8>) -> crate::matching::spec::CanonicalHost {
    crate::matching::spec::CanonicalHost { name, is_ip_address: false }
}

/// An IP address.
pub open spec fn ip(name: Seq<u8>) -> crate::matching::spec::CanonicalHost {
    crate::matching::spec::CanonicalHost { name, is_ip_address: true }
}

/// A request to `https://name/path`.
pub open spec fn https_url(name: Seq<u8>, path: Seq<u8>) -> RequestUrl {
    RequestUrl { scheme: lit_https(), host: Some(host(name)), path }
}

/// "/".
pub open spec fn p_root() -> Seq<u8> {
    seq![0x2Fu8]
}

/// "/x".
pub open spec fn p_x() -> Seq<u8> {
    seq![0x2Fu8, 0x78]
}

/// "/z".
pub open spec fn p_z() -> Seq<u8> {
    seq![0x2Fu8, 0x7A]
}

/// A "non-HTTP" call from a top-level document (`document.cookie`).
pub open spec fn document_call() -> RequestContext {
    RequestContext::NonHttp(
        DocumentCall {
            site_for_cookies: clazel_origin::spec::Origin::Opaque(0),
            top_level_origin: clazel_origin::spec::Origin::Opaque(0),
        },
    )
}

/// A "non-HTTP" call from a frame of another site.
pub open spec fn cross_site_call() -> RequestContext {
    RequestContext::NonHttp(
        DocumentCall {
            site_for_cookies: clazel_origin::spec::Origin::Opaque(0),
            top_level_origin: clazel_origin::spec::Origin::Opaque(1),
        },
    )
}

/// An HTTP request with no client (always same-site).
pub open spec fn http_request() -> RequestContext {
    RequestContext::Http(
        HttpRequest {
            url_origin: clazel_origin::spec::Origin::Opaque(0),
            site_for_cookies: None,
            is_reload_navigation: false,
            reloaded_document_was_same_site: false,
            navigates_top_level_traversable: false,
            method_is_safe: true,
            target_is_active_or_top_level: true,
        },
    )
}

/// A cookie with every flag false.
pub open spec fn cookie(
    name: Seq<u8>,
    value: Seq<u8>,
    domain: crate::matching::spec::CanonicalHost,
    host_only_flag: bool,
    path: Seq<u8>,
    creation_time: int,
) -> Cookie {
    Cookie {
        name,
        value,
        expiry_time: latest_representable(),
        domain,
        path,
        creation_time,
        last_access_time: 0,
        persistent_flag: false,
        host_only_flag,
        secure_only_flag: false,
        http_only_flag: false,
        same_site_flag: crate::set_cookie::spec::SameSite::None,
    }
}

/// "a".
pub open spec fn s_a() -> Seq<u8> {
    seq![0x61u8]
}

/// "b".
pub open spec fn s_b() -> Seq<u8> {
    seq![0x62u8]
}

/// "1".
pub open spec fn s_1() -> Seq<u8> {
    seq![0x31u8]
}

/// "2".
pub open spec fn s_2() -> Seq<u8> {
    seq![0x32u8]
}


// ---------------------------------------------------------------------
// §5.8: the cookie-list and the cookie-string.
// ---------------------------------------------------------------------

/// Cookies `a=1` (path "/", created at 1) and `b=2` (path "/x", created at
/// 2), for `a.com`.
pub open spec fn jar_two_paths() -> Seq<Cookie> {
    seq![cookie(s_a(), s_1(), host(s_a_com()), true, p_root(), 1), cookie(s_b(), s_2(), host(s_a_com()), true, p_x(), 2)]
}

/// "b=2; a=1".
pub open spec fn str_b2_a1() -> Seq<u8> {
    seq![0x62u8, 0x3D, 0x32, 0x3B, 0x20, 0x61, 0x3D, 0x31]
}

/// "a=1; b=2".
pub open spec fn str_a1_b2() -> Seq<u8> {
    seq![0x61u8, 0x3D, 0x31, 0x3B, 0x20, 0x62, 0x3D, 0x32]
}

/// Step 4: "Cookies with longer paths are listed before cookies with shorter
/// paths."
pub proof fn example_sort_longer_path_first()
    ensures
        sort_cookie_list(jar_two_paths()) == seq![jar_two_paths()[1], jar_two_paths()[0]],
{
    assert(sort_cookie_list(jar_two_paths()) == seq![jar_two_paths()[1], jar_two_paths()[0]]) by (compute_only);
}

/// The same two cookies at the same path, created at 5 and at 3.
pub open spec fn jar_two_creations() -> Seq<Cookie> {
    seq![cookie(s_a(), s_1(), host(s_a_com()), true, p_root(), 5), cookie(s_b(), s_2(), host(s_a_com()), true, p_root(), 3)]
}

/// Step 4: "Among cookies that have equal-length path fields, cookies with
/// earlier creation-times are listed before cookies with later
/// creation-times", and cookies listed equally keep their order.
pub proof fn example_sort_earlier_creation_first()
    ensures
        sort_cookie_list(jar_two_creations()) == seq![jar_two_creations()[1], jar_two_creations()[0]],
        sort_cookie_list(seq![jar_two_creations()[0], jar_two_creations()[0]]) == seq![jar_two_creations()[0], jar_two_creations()[0]],
{
    assert(sort_cookie_list(jar_two_creations()) == seq![jar_two_creations()[1], jar_two_creations()[0]]) by (compute_only);
    assert(sort_cookie_list(seq![jar_two_creations()[0], jar_two_creations()[0]]) == seq![jar_two_creations()[0], jar_two_creations()[0]])
        by (compute_only);
}

/// Step 6: the cookie-string of the list in its order, with "; " between
/// the cookies and no "=" for a cookie without a name.
pub proof fn example_serialize()
    ensures
        serialize_cookie_list_from(jar_two_paths(), 0) == str_a1_b2(),
        serialize_cookie_list_from(seq![cookie(seq![], s_1(), host(s_a_com()), true, p_root(), 1)], 0) == s_1(),
        serialize_cookie_list_from(seq![cookie(s_a(), seq![], host(s_a_com()), true, p_root(), 1)], 0) == s_a_eq(),
{
    assert(serialize_cookie_list_from(jar_two_paths(), 0) == str_a1_b2()) by (compute_only);
    assert(serialize_cookie_list_from(seq![cookie(seq![], s_1(), host(s_a_com()), true, p_root(), 1)], 0) == s_1()) by (compute_only);
    assert(serialize_cookie_list_from(seq![cookie(s_a(), seq![], host(s_a_com()), true, p_root(), 1)], 0) == s_a_eq())
        by (compute_only);
}

/// "a=".
pub open spec fn s_a_eq() -> Seq<u8> {
    seq![0x61u8, 0x3D]
}

/// A cookie that expires at 5.
pub open spec fn cookie_expiring() -> Cookie {
    Cookie { expiry_time: 5, ..cookie(s_a(), s_1(), host(s_a_com()), true, p_root(), 1) }
}

/// "A cookie is 'expired' if the cookie has an expiry date in the past": at
/// its expiry-time it is not expired, a second later it is.
pub proof fn example_expiry_boundary()
    ensures
        !cookie_expired(cookie_expiring(), 5),
        cookie_expired(cookie_expiring(), 6),
{
    assert(!cookie_expired(cookie_expiring(), 5)) by (compute_only);
    assert(cookie_expired(cookie_expiring(), 6)) by (compute_only);
}

/// Step 5, for one cookie of a retrieval of `https://a.com/x` at time 9.
pub proof fn example_update_last_access()
    ensures
        update_last_access_time(rules(), https_url(s_a_com(), p_x()), document_call(), host(s_a_com()), 9)(jar_one_matching()[0])
            == with_last_access_time(jar_one_matching()[0], 9),
        update_last_access_time(rules(), https_url(s_a_com(), p_x()), document_call(), host(s_a_com()), 9)(jar_one_matching()[1])
            == jar_one_matching()[1],
{
    assert(update_last_access_time(rules(), https_url(s_a_com(), p_x()), document_call(), host(s_a_com()), 9)(jar_one_matching()[0])
        == with_last_access_time(jar_one_matching()[0], 9)) by (compute_only);
    assert(update_last_access_time(rules(), https_url(s_a_com(), p_x()), document_call(), host(s_a_com()), 9)(jar_one_matching()[1])
        == jar_one_matching()[1]) by (compute_only);
}

/// `a=1` (path "/") and `b=2` (path "/z").
pub open spec fn jar_one_matching() -> Seq<Cookie> {
    seq![cookie(s_a(), s_1(), host(s_a_com()), true, p_root(), 1), cookie(s_b(), s_2(), host(s_a_com()), true, p_z(), 2)]
}

/// A "non-HTTP" call from a cross-site document is not same-site.
pub proof fn example_cross_site_call()
    ensures
        !is_same_site_request(rules(), cross_site_call()),
        is_same_site_request(rules(), document_call()),
        is_same_site_request(rules(), http_request()),
{
    assert(!is_same_site_request(rules(), cross_site_call())) by (compute_only);
    assert(is_same_site_request(rules(), document_call())) by (compute_only);
    assert(is_same_site_request(rules(), http_request())) by (compute_only);
}

// ---------------------------------------------------------------------
// §5.7: pieces of the storage model.
// ---------------------------------------------------------------------

/// Step 9: a host that is itself a public suffix may set a cookie for
/// itself (the domain-attribute becomes empty); another host may not.
pub proof fn example_step_9()
    ensures
        step_9_domain_attribute(rules(), host(s_com()), s_com()) == Some(Seq::<u8>::empty()),
        step_9_domain_attribute(rules(), host(s_a_com()), s_com()) is None,
        step_9_domain_attribute(rules(), host(s_a_com()), s_a_com()) == Some(s_a_com()),
{
    assert(step_9_domain_attribute(rules(), host(s_com()), s_com()) == Some(Seq::<u8>::empty())) by (compute_only);
    assert(step_9_domain_attribute(rules(), host(s_a_com()), s_com()) is None) by (compute_only);
    assert(step_9_domain_attribute(rules(), host(s_a_com()), s_a_com()) == Some(s_a_com())) by (compute_only);
}

/// Step 10: the host must domain-match the domain-attribute, at a "." boundary
/// and not as an IP address.
pub proof fn example_step_10()
    ensures
        step_10_domain(host(s_a_com()), s_com()) == Some((host(s_com()), false)),
        step_10_domain(host(s_ba_com()), s_a_com()) is None,
        step_10_domain(ip(s_ip()), s_3_4()) is None,
        step_10_domain(host(s_a_com()), Seq::<u8>::empty()) == Some((host(s_a_com()), true)),
{
    assert(step_10_domain(host(s_a_com()), s_com()) == Some((host(s_com()), false))) by (compute_only);
    assert(step_10_domain(host(s_ba_com()), s_a_com()) is None) by (compute_only);
    assert(step_10_domain(ip(s_ip()), s_3_4()) is None) by (compute_only);
    assert(step_10_domain(host(s_a_com()), Seq::<u8>::empty()) == Some((host(s_a_com()), true))) by (compute_only);
}

/// Step 6.
pub proof fn example_step_6()
    ensures
        persistent_flag_and_expiry_time(seq![crate::set_cookie::spec::Attribute::Expires(9), crate::set_cookie::spec::Attribute::MaxAge(7)])
            == (true, 7int),
        persistent_flag_and_expiry_time(Seq::<crate::set_cookie::spec::Attribute>::empty()) == (false, latest_representable()),
{
    assert(persistent_flag_and_expiry_time(seq![crate::set_cookie::spec::Attribute::Expires(9), crate::set_cookie::spec::Attribute::MaxAge(7)])
        == (true, 7int)) by (compute_only);
    assert(persistent_flag_and_expiry_time(Seq::<crate::set_cookie::spec::Attribute>::empty()) == (false, latest_representable()))
        by (compute_only);
}

/// A string of 1025 "a".
pub open spec fn long_domain() -> Seq<u8> {
    Seq::new(1025, |i: int| 0x61u8)
}

/// Step 7: "the last attribute [...] with both an attribute-name of 'Domain'
/// and an attribute-value whose length is no more than 1024 octets".
pub proof fn example_step_7()
    ensures
        last_domain_within_1024(seq![crate::set_cookie::spec::Attribute::Domain(s_com()), crate::set_cookie::spec::Attribute::Domain(long_domain())])
            == Some(s_com()),
{
    assert(last_domain_within_1024(seq![
        crate::set_cookie::spec::Attribute::Domain(s_com()),
        crate::set_cookie::spec::Attribute::Domain(long_domain()),
    ]) == Some(s_com())) by (compute_only);
}

/// Step 18.
pub proof fn example_step_18()
    ensures
        step_18_continues(rules(), document_call()),
        !step_18_continues(rules(), cross_site_call()),
        step_18_continues(rules(), http_request()),
{
    assert(step_18_continues(rules(), document_call())) by (compute_only);
    assert(!step_18_continues(rules(), cross_site_call())) by (compute_only);
    assert(step_18_continues(rules(), http_request())) by (compute_only);
}

/// The old cookie of step 23 is replaced, and the new one goes last (step
/// 24).
pub open spec fn jar_with_old() -> Seq<Cookie> {
    seq![cookie(s_a(), s_1(), host(s_a_com()), true, p_root(), 1), cookie(s_b(), s_2(), host(s_a_com()), true, p_root(), 2)]
}

/// A new `a` for `a.com`, with value "2".
pub open spec fn cookie_new_a() -> Cookie {
    cookie(s_a(), s_2(), host(s_a_com()), true, p_root(), 7)
}

/// Steps 23.4 and 24.
pub proof fn example_insert_a_cookie()
    ensures
        insert_a_cookie(jar_with_old(), cookie_new_a()) == seq![jar_with_old()[1], cookie_new_a()],
        find_old_cookie(jar_with_old(), cookie_new_a()) == Some(0int),
        // A cookie of the same name and path, but not host-only, is another cookie.
        find_old_cookie(jar_with_old(), cookie(s_a(), s_2(), host(s_a_com()), false, p_root(), 7)) is None,
{
    assert(insert_a_cookie(jar_with_old(), cookie_new_a()) == seq![jar_with_old()[1], cookie_new_a()]) by (compute_only);
    assert(find_old_cookie(jar_with_old(), cookie_new_a()) == Some(0int)) by (compute_only);
    assert(find_old_cookie(jar_with_old(), cookie(s_a(), s_2(), host(s_a_com()), false, p_root(), 7)) is None) by (compute_only);
}

// ---------------------------------------------------------------------
// The eviction order and the cookie root.
// ---------------------------------------------------------------------

/// A secure-only cookie accessed at 1, then a cookie that is not, accessed
/// at 5, both for `a.com`.
pub open spec fn jar_secure_first() -> Seq<Cookie> {
    seq![
        Cookie { secure_only_flag: true, last_access_time: 1, ..cookie(s_a(), s_1(), host(s_a_com()), true, p_root(), 1) },
        Cookie { last_access_time: 5, ..cookie(s_b(), s_2(), host(s_a_com()), true, p_root(), 2) },
    ]
}

/// Two cookies that are not secure-only, accessed at 5 and at 3.
pub open spec fn jar_access_order() -> Seq<Cookie> {
    seq![
        Cookie { last_access_time: 5, ..cookie(s_a(), s_1(), host(s_a_com()), true, p_root(), 1) },
        Cookie { last_access_time: 3, ..cookie(s_b(), s_2(), host(s_a_com()), true, p_root(), 2) },
    ]
}

/// A cookie of `b.com` first, then one of `a.com`, both accessed at 0.
pub open spec fn jar_two_roots() -> Seq<Cookie> {
    seq![
        cookie(s_a(), s_1(), host(s_b_com()), true, p_root(), 1),
        cookie(s_b(), s_2(), host(s_a_com()), true, p_root(), 2),
    ]
}

/// §5.7: the cookies "whose secure-only-flag is false" are removed first,
/// then the one with "the earliest last-access-time" and, on a tie, the first
/// in the jar; and only a cookie of the root is removed.
pub proof fn example_eviction_order()
    ensures
        victim_from(rules(), jar_secure_first(), host(s_a_com()), 2) == Some(1int),
        victim_from(rules(), jar_access_order(), host(s_a_com()), 2) == Some(1int),
        victim_from(rules(), jar_two_paths(), host(s_a_com()), 2) == Some(0int),
        victim_from(rules(), jar_two_paths(), host(s_b_com()), 2) is None,
        victim_from(rules(), jar_two_roots(), host(s_a_com()), 2) == Some(1int),
        victim_from(rules(), jar_two_roots(), host(s_b_com()), 2) == Some(0int),
{
    assert(victim_from(rules(), jar_secure_first(), host(s_a_com()), 2) == Some(1int)) by (compute_only);
    assert(victim_from(rules(), jar_access_order(), host(s_a_com()), 2) == Some(1int)) by (compute_only);
    assert(victim_from(rules(), jar_two_paths(), host(s_a_com()), 2) == Some(0int)) by (compute_only);
    assert(victim_from(rules(), jar_two_paths(), host(s_b_com()), 2) is None) by (compute_only);
    assert(victim_from(rules(), jar_two_roots(), host(s_a_com()), 2) == Some(1int)) by (compute_only);
    assert(victim_from(rules(), jar_two_roots(), host(s_b_com()), 2) == Some(0int)) by (compute_only);
}

/// The cookie root: the shortest suffix that is not a public suffix.
pub proof fn example_cookie_root()
    ensures
        cookie_root(rules(), host(s_x_a_co_uk())) == host(s_a_co_uk()),
        cookie_root(rules(), host(s_co_uk())) == host(s_co_uk()),
        cookie_root(rules(), host(s_a_com())) == host(s_a_com()),
        cookie_root(rules(), ip(s_ip())) == ip(s_ip()),
{
    assert(cookie_root(rules(), host(s_x_a_co_uk())) == host(s_a_co_uk())) by (compute_only);
    assert(cookie_root(rules(), host(s_co_uk())) == host(s_co_uk())) by (compute_only);
    assert(cookie_root(rules(), host(s_a_com())) == host(s_a_com())) by (compute_only);
    assert(cookie_root(rules(), ip(s_ip())) == ip(s_ip())) by (compute_only);
}

/// Step 3 of §5.8.3 for single cookies.
pub proof fn example_cookie_is_retrieved()
    ensures
        // A host-only cookie goes to its host, not to a subdomain.
        cookie_is_retrieved(rules(), https_url(s_a_com(), p_x()), document_call(), host(s_a_com()), jar_one_matching()[0]),
        !cookie_is_retrieved(rules(), https_url(s_x_a_com(), p_x()), document_call(), host(s_x_a_com()), jar_one_matching()[0]),
        // The path must match.
        !cookie_is_retrieved(rules(), https_url(s_a_com(), p_x()), document_call(), host(s_a_com()), jar_one_matching()[1]),
        // A domain cookie goes to its subdomains, at a "." boundary only.
        cookie_is_retrieved(rules(), https_url(s_x_a_com(), p_x()), document_call(), host(s_x_a_com()), cookie_domain_a_com()),
        !cookie_is_retrieved(rules(), https_url(s_ba_com(), p_x()), document_call(), host(s_ba_com()), cookie_domain_a_com()),
        // A cookie whose domain is a public suffix is not sent to its subdomains.
        !cookie_is_retrieved(rules(), https_url(s_a_com(), p_x()), document_call(), host(s_a_com()), cookie_domain_com()),
        // A host that is a public suffix is not sent a cookie of one below it.
        !cookie_is_retrieved(rules(), https_url(s_co_uk(), p_x()), document_call(), host(s_co_uk()), cookie_domain_a_co_uk()),
        // Secure-only, HttpOnly.
        cookie_is_retrieved(rules(), https_url(s_a_com(), p_x()), document_call(), host(s_a_com()), cookie_secure()),
        !cookie_is_retrieved(rules(), http_url(s_a_com(), p_x()), document_call(), host(s_a_com()), cookie_secure()),
        !cookie_is_retrieved(rules(), https_url(s_a_com(), p_x()), document_call(), host(s_a_com()), cookie_http_only()),
        cookie_is_retrieved(rules(), https_url(s_a_com(), p_x()), http_request(), host(s_a_com()), cookie_http_only()),
        // A cookie that is not SameSite=None stays out of a cross-site call.
        !cookie_is_retrieved(rules(), https_url(s_a_com(), p_x()), cross_site_call(), host(s_a_com()), cookie_lax()),
        cookie_is_retrieved(rules(), https_url(s_a_com(), p_x()), cross_site_call(), host(s_a_com()), jar_one_matching()[0]),
{
    assert(cookie_is_retrieved(rules(), https_url(s_a_com(), p_x()), document_call(), host(s_a_com()), jar_one_matching()[0]))
        by (compute_only);
    assert(!cookie_is_retrieved(rules(), https_url(s_x_a_com(), p_x()), document_call(), host(s_x_a_com()), jar_one_matching()[0]))
        by (compute_only);
    assert(!cookie_is_retrieved(rules(), https_url(s_a_com(), p_x()), document_call(), host(s_a_com()), jar_one_matching()[1]))
        by (compute_only);
    assert(cookie_is_retrieved(rules(), https_url(s_x_a_com(), p_x()), document_call(), host(s_x_a_com()), cookie_domain_a_com()))
        by (compute_only);
    assert(!cookie_is_retrieved(rules(), https_url(s_ba_com(), p_x()), document_call(), host(s_ba_com()), cookie_domain_a_com()))
        by (compute_only);
    assert(!cookie_is_retrieved(rules(), https_url(s_a_com(), p_x()), document_call(), host(s_a_com()), cookie_domain_com()))
        by (compute_only);
    assert(!cookie_is_retrieved(rules(), https_url(s_co_uk(), p_x()), document_call(), host(s_co_uk()), cookie_domain_a_co_uk()))
        by (compute_only);
    assert(cookie_is_retrieved(rules(), https_url(s_a_com(), p_x()), document_call(), host(s_a_com()), cookie_secure()))
        by (compute_only);
    assert(!cookie_is_retrieved(rules(), http_url(s_a_com(), p_x()), document_call(), host(s_a_com()), cookie_secure()))
        by (compute_only);
    assert(!cookie_is_retrieved(rules(), https_url(s_a_com(), p_x()), document_call(), host(s_a_com()), cookie_http_only()))
        by (compute_only);
    assert(cookie_is_retrieved(rules(), https_url(s_a_com(), p_x()), http_request(), host(s_a_com()), cookie_http_only()))
        by (compute_only);
    assert(!cookie_is_retrieved(rules(), https_url(s_a_com(), p_x()), cross_site_call(), host(s_a_com()), cookie_lax()))
        by (compute_only);
    assert(cookie_is_retrieved(rules(), https_url(s_a_com(), p_x()), cross_site_call(), host(s_a_com()), jar_one_matching()[0]))
        by (compute_only);
}

/// "x.a.com".
pub open spec fn s_x_a_com() -> Seq<u8> {
    seq![0x78u8, 0x2E, 0x61, 0x2E, 0x63, 0x6F, 0x6D]
}

/// A request to `http://name/path`.
pub open spec fn http_url(name: Seq<u8>, path: Seq<u8>) -> RequestUrl {
    RequestUrl { scheme: seq![0x68u8, 0x74, 0x74, 0x70], host: Some(host(name)), path }
}

/// A cookie for the domain `a.com` (not host-only).
pub open spec fn cookie_domain_a_com() -> Cookie {
    cookie(s_a(), s_1(), host(s_a_com()), false, p_root(), 1)
}

/// A cookie for the domain `com` (not host-only).
pub open spec fn cookie_domain_com() -> Cookie {
    cookie(s_a(), s_1(), host(s_com()), false, p_root(), 1)
}

/// A cookie for the domain `a.co.uk` (not host-only).
pub open spec fn cookie_domain_a_co_uk() -> Cookie {
    cookie(s_a(), s_1(), host(s_a_co_uk()), false, p_root(), 1)
}

/// A secure-only host-only cookie for `a.com`.
pub open spec fn cookie_secure() -> Cookie {
    Cookie { secure_only_flag: true, ..cookie(s_a(), s_1(), host(s_a_com()), true, p_root(), 1) }
}

/// An HttpOnly host-only cookie for `a.com`.
pub open spec fn cookie_http_only() -> Cookie {
    Cookie { http_only_flag: true, ..cookie(s_a(), s_1(), host(s_a_com()), true, p_root(), 1) }
}

/// A SameSite=Lax host-only cookie for `a.com`.
pub open spec fn cookie_lax() -> Cookie {
    Cookie { same_site_flag: crate::set_cookie::spec::SameSite::Lax, ..cookie(s_a(), s_1(), host(s_a_com()), true, p_root(), 1) }
}

} // verus!
