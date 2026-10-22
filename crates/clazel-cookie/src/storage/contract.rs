//! Contracts the executable storage and retrieval functions (item 2.9, not
//! yet written) must be proven to meet. Each exec function's `ensures`
//! clause will be exactly one of these predicates, so reviewing these (and
//! [`super::spec`]) is enough to know what the implementation guarantees.
//!
//! Strings are octets (`&[u8]`). An exec cookie jar is viewed as a
//! `Seq<Cookie>`, in insertion order; an exec request URL as a
//! [`RequestUrl`], a request context as a [`RequestContext`]. Time is
//! seconds since 1601-01-01T00:00:00Z (`u64`). Every contract is about the
//! Public Suffix List the generated tables hold
//! (`clazel_psl::table::psl_rules()`), as `clazel-psl`'s are; the spec
//! functions hold for every list.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The cookie's instants fit a `u64`, which the exec jar stores them in.
pub open spec fn cookie_in_range(cookie: Cookie) -> bool {
    0 <= cookie.expiry_time <= latest_representable() && 0 <= cookie.creation_time <= latest_representable() && 0
        <= cookie.last_access_time <= latest_representable()
}

/// Every cookie of the jar is [`cookie_in_range`].
pub open spec fn jar_in_range(jar: Seq<Cookie>) -> bool {
    forall|i: int| 0 <= i < jar.len() ==> cookie_in_range(#[trigger] jar[i])
}

/// Precondition of `evict_expired(&Jar, u64) -> Jar`.
pub open spec fn evict_expired_requires(jar: Seq<Cookie>, now: int) -> bool {
    0 <= now <= latest_representable()
}

/// Contract for `evict_expired(&Jar, u64) -> Jar`: "The user agent MUST
/// evict all expired cookies from the cookie store." Also what the kernel
/// does when the time advances.
pub open spec fn evict_expired_ensures(jar: Seq<Cookie>, now: int, output: Seq<Cookie>) -> bool {
    output == evict_expired(jar, now)
}

/// Precondition of `store_a_cookie(&Jar, &RequestUrl, &RequestContext,
/// &SetCookie, u64) -> Jar`. The instants it computes (the time, plus the
/// lifetime limit, from the parser) must fit a `u64`, as for
/// `parse_a_set_cookie_string`.
pub open spec fn store_a_cookie_requires(
    jar: Seq<Cookie>,
    url: RequestUrl,
    ctx: RequestContext,
    received: crate::set_cookie::spec::SetCookie,
    now: int,
) -> bool {
    crate::set_cookie::contract::now_in_range(now) && jar_in_range(jar)
}

/// Contract for `store_a_cookie(&Jar, &RequestUrl, &RequestContext,
/// &SetCookie, u64) -> Jar`: the cookie store after the user agent "receives
/// a cookie" (§5.7), with the cookie-attribute-list `received.attributes`.
pub open spec fn store_a_cookie_ensures(
    jar: Seq<Cookie>,
    url: RequestUrl,
    ctx: RequestContext,
    received: crate::set_cookie::spec::SetCookie,
    now: int,
    output: Seq<Cookie>,
) -> bool {
    output == store_a_cookie(clazel_psl::table::psl_rules(), jar, url, ctx, received, now)
}

/// Precondition of `store_a_set_cookie_string(&Jar, &[u8], &RequestUrl,
/// &RequestContext, u64) -> Jar`.
pub open spec fn store_a_set_cookie_string_requires(
    jar: Seq<Cookie>,
    s: Seq<u8>,
    url: RequestUrl,
    ctx: RequestContext,
    now: int,
) -> bool {
    crate::set_cookie::contract::parse_a_set_cookie_string_requires(s, url.path, now) && jar_in_range(jar)
}

/// Contract for `store_a_set_cookie_string(&Jar, &[u8], &RequestUrl,
/// &RequestContext, u64) -> Jar`: §5.6's parse of the string, then §5.7. This
/// is `document.cookie`'s setter when `ctx` is `NonHttp`.
pub open spec fn store_a_set_cookie_string_ensures(
    jar: Seq<Cookie>,
    s: Seq<u8>,
    url: RequestUrl,
    ctx: RequestContext,
    now: int,
    output: Seq<Cookie>,
) -> bool {
    output == store_a_set_cookie_string(clazel_psl::table::psl_rules(), jar, s, url, ctx, now)
}

/// Precondition of `retrieve_a_cookie_string(&mut Jar, &RequestUrl,
/// &RequestContext, u64) -> Vec<u8>`.
pub open spec fn retrieve_a_cookie_string_requires(jar: Seq<Cookie>, url: RequestUrl, ctx: RequestContext, now: int) -> bool {
    0 <= now <= latest_representable() && jar_in_range(jar)
}

/// Contract for `retrieve_a_cookie_string(&mut Jar, &RequestUrl,
/// &RequestContext, u64) -> Vec<u8>`: the cookie-string of §5.8.3 over the
/// jar as it was (`jar`), and the jar after step 5 (`jar_after`). This is
/// `document.cookie`'s getter when `ctx` is `NonHttp`.
pub open spec fn retrieve_a_cookie_string_ensures(
    jar: Seq<Cookie>,
    url: RequestUrl,
    ctx: RequestContext,
    now: int,
    jar_after: Seq<Cookie>,
    output: Seq<u8>,
) -> bool {
    output == retrieve_cookie_string(clazel_psl::table::psl_rules(), jar, url, ctx, now) && jar_after == jar_after_retrieval(
        clazel_psl::table::psl_rules(),
        jar,
        url,
        ctx,
        now,
    )
}

} // verus!
