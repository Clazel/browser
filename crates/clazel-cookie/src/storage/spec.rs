//! RFC 6265bis §5.2 ("same-site" and "cross-site" requests), §5.7 (the
//! storage model) and §5.8 (the retrieval model), transcribed. Nothing here
//! runs; it defines what "correct" means. Each `// N.` comment is the step
//! number in the cited algorithm.
//!
//! Source (pinned; a review is against exactly this text):
//! - draft-ietf-httpbis-rfc6265bis-22, "Cookies: HTTP State Management
//!   Mechanism", 1 December 2025 (the latest revision on 22 October 2026;
//!   it has not been published as an RFC),
//!   <https://www.ietf.org/archive/id/draft-ietf-httpbis-rfc6265bis-22.txt>:
//!   §5.2 (and §5.2.1), §5.3, §5.7 Storage Model, §5.8 Retrieval Model
//!   (§5.8.1 to §5.8.3), and the limits of §6.1. §5.1 and §5.4 to §5.6 are
//!   in `crate::date`, `crate::matching` and `crate::set_cookie`; the
//!   prefix requirements (steps 20 to 22) are
//!   [`crate::set_cookie::spec::name_prefix_requirements_met`].
//! - HTML Standard, "same site" of two origins (`clazel_origin::spec::
//!   same_site`), which §5.2 means by "[SAMESITE]".
//!
//! # The two isolation decisions
//!
//! The kernel's headline theorem (`theorem_cookie_noninterference`, item
//! 2.11) is false unless both of the following hold, so they are decided
//! here, in the spec, and not left to the implementation.
//!
//! - **The isolation boundary is the cookie root, not the registrable
//!   domain.** A cookie set by `amazonaws.com` with `Domain=amazonaws.com`
//!   is sent to `bucket.s3.amazonaws.com`, whose registrable domain is
//!   `bucket.s3.amazonaws.com` (`s3.amazonaws.com` is a public suffix). So a
//!   theorem partitioning the jar by registrable domain would be false. Two
//!   hosts can share a cookie exactly when they have the same cookie root
//!   (`clazel_psl::spec::cookie_root`: the shortest suffix, in labels, that
//!   is not a public suffix; for an IP address, the address). In this file
//!   [`cookie_root`] is that, over a canonicalized host, and the facts the
//!   theorem needs are the lemmas listed below.
//! - **Eviction is per cookie root, with no global limit.** §5.7's last
//!   paragraphs let the user agent "remove excess cookies" when the store
//!   is too large, and §6.1 suggests a total of 3000. A global limit lets
//!   one site evict another's cookies by setting many of its own, which is
//!   both a write and, by probing, a read across sites. We keep only a
//!   per-root limit, [`max_cookies_per_root`] (180, as Chrome and Firefox use
//!   per domain; §6.1 asks for at least 50 per domain), applied to the root
//!   of the cookie just stored ([`evict_over_limit`]), and no global one.
//!   The RFC leaves the policy to the user agent ("MAY"), so this is a
//!   choice, not an erratum. Memory stays bounded because a renderer can
//!   only add cookies under its own root. (Expired cookies are evicted
//!   globally, [`evict_expired`], which the RFC requires; whether a cookie
//!   is expired depends only on its own expiry time and the current time,
//!   never on other cookies, so it is no channel.)
//!
//! # Modelling choices
//!
//! Each is a deliberate deviation in form, never in meaning, unless it says
//! it fills a gap or makes a policy choice the RFC leaves to the user agent.
//!
//! - **The jar is a `Seq<Cookie>`** (the "cookie store"), in insertion
//!   order, and the current time is the argument `now`, seconds since
//!   1601-01-01T00:00:00Z as in `crate::set_cookie::spec`. A [`Cookie`] has
//!   the twelve fields of §5.7's first paragraph, with the standard's names.
//!   "The latest representable date" ([`latest_representable`]) is
//!   2^64 - 1 seconds, the largest `u64`. "Expired" is "has an expiry date in
//!   the past": `expiry_time < now` ([`cookie_expired`]).
//! - **A cookie's domain is a `CanonicalHost`** (the §5.1.2 result: a
//!   name and whether it is an IP address), not a bare string. §5.1.3 asks
//!   "the string is a host name (i.e., not an IP address)", which a bare
//!   string cannot answer, and the cookie root of an IP address is the
//!   address, not a suffix. "Identical" for two canonical hosts is equality
//!   of both fields, and domain-matching a cookie's domain
//!   ([`canonical_domain_matches`]) is §5.1.3 on the names with the flags
//!   applied. Under the URL host parser a name determines its flag (no
//!   domain looks like an IPv4 or IPv6 address), so this changes nothing a
//!   request can observe. A Domain attribute is an uncanonicalized string
//!   (§5.6.3 only lower-cases it): when it passes step 10 it becomes a
//!   domain with the request host's flag, which is `false` unless it is
//!   identical to an IP-address request host.
//! - **The request URL is an abstract record** ([`RequestUrl`]): scheme,
//!   canonical host (`None` is "fails to be canonicalized") and path, so
//!   that nothing here needs a URL parser. §5.7's "request-uri" and §5.8's
//!   "the retrieval's URI" are both a [`RequestUrl`]. A "secure" connection
//!   ([`url_is_secure`]) is one whose scheme is `https` or `wss`; the draft
//!   leaves it to the user agent and mentions trusting `localhost`, which
//!   we do not (a policy choice; the Phase 2 callers are `https` pages).
//! - **The request context is abstract** ([`RequestContext`]) and carries
//!   what §5.2, §5.7 step 18 and §5.8.3 step 3 ask: for an HTTP request
//!   (`Http`), the request's current URL's origin, its client's "site for
//!   cookies" (or none), whether it is a reload, whether the reloaded
//!   document was originally same-site, whether it navigates a top-level
//!   traversable, whether its method is "safe", and whether its target
//!   browsing context is the active one or a top-level traversable; for
//!   a "non-HTTP" API (`NonHttp`), the calling document's "site for
//!   cookies" and the top-level origin (§5.2.1, §5.8.2). That a cookie "was
//!   received from a 'non-HTTP' API" and "the retrieval's type is 'non-HTTP'"
//!   are both [`is_non_http`]. Origins are `clazel-origin`'s and "same-site"
//!   is `clazel_origin::spec::same_site` over the Public Suffix List
//!   `rules` the functions take. Phase 2's only caller is `document.cookie`
//!   in a top-level document (`NonHttp` with both origins equal); the real
//!   HTTP contexts arrive with Fetch in Phase 3.
//! - **The Public Suffix List is a parameter** `rules: Seq<Rule>`, as in
//!   `clazel-psl`, and the user agent is "configured to reject public
//!   suffixes" (§5.7 step 9, §5.8.3 step 3) unconditionally: the
//!   isolation lemmas depend on it. The contracts instantiate `rules` with
//!   the generated tables.
//! - **Nothing is ignored by policy** (§5.3; §5.7 step 1 "MAY ignore a
//!   received cookie in its entirety"): the caller never passes the
//!   Set-Cookie fields of 100-level responses, and the cookie policy of §7.2
//!   is empty. HTTP responses are Phase 3.
//! - **"Abort ... and ignore the cookie entirely" is `None`**, and an
//!   ignored cookie leaves the jar as it was (apart from the eviction of
//!   expired cookies, below). Retrieval's step 2 "abort this algorithm"
//!   returns the empty cookie-string, as `document.cookie` does.
//! - **Expired cookies are evicted first.** §5.7 says the user agent "MUST
//!   evict all expired cookies from the cookie store if, at any time, an
//!   expired cookie exists". Storage and retrieval therefore begin with
//!   [`evict_expired`] (so no step looks at an expired cookie), and storage
//!   ends with it (so a cookie stored already expired, by `Max-Age=0` or a
//!   past `Expires`, is gone). The kernel also applies it when time
//!   advances.
//! - **Excess cookies are removed by the "remove excess cookies"
//!   priority, per root** ([`evict_over_limit`]): while a root has more than
//!   [`max_cookies_per_root`] cookies, remove one of its cookies, by §5.7's
//!   priority: expired (none are left), then those with secure-only-flag
//!   false, then all, with the earliest last-access-time first, and the
//!   earliest in the jar on a tie (the RFC leaves ties open). Because every
//!   cookie of an over-limit root "shares" the root with more than the
//!   limit's worth of others, the RFC's "share a domain field with more than
//!   a predetermined number of other cookies" is true of all of them, and
//!   the domain field is replaced by the cookie root (a policy choice).
//! - **Retrieval sorts** the cookie-list (step 4 "SHOULD"), stably, by
//!   longer path first and then earlier creation-time first
//!   ([`sort_cookie_list`]), so the result is a function. Step 5, updating
//!   the last-access-time, gives the jar after retrieval
//!   ([`jar_after_retrieval`]); the cookie-string is computed from the jar
//!   before.
//! - **Step 23's "remove the old-cookie"** removes the first cookie with the
//!   same name, domain, host-only-flag and path ([`find_old_cookie`]). The
//!   RFC states the invariant that there is at most one ([`jar_keys_unique`]),
//!   which storage preserves.
//! - **Attribute values over 1024 octets.** Steps 7 and 11 take "the last
//!   attribute ... with both [the name] and an attribute-value whose length
//!   is no more than 1024 octets". If the list has such an attribute name
//!   but none that short, the draft defines no value (the "Otherwise" is
//!   for no attribute at all). We use the empty domain-attribute and the
//!   default-path, as if there were none. The §5.6 parser already ignores
//!   every attribute-value over 1024 octets (its step 6), so the case does
//!   not arise from parsed input. For the same reason steps 20 to 22 use
//!   [`crate::set_cookie::spec::name_prefix_requirements_met`], which reads
//!   the last Path attribute whatever its length.
//! - **§5.7 step 17**: "the attribute-value of the last attribute ... with an
//!   attribute-name of SameSite" is the last SameSite attribute whatever its
//!   value (an unrecognised value is "Default" after §5.6.7), and the
//!   condition "contains ... 'Strict', 'Lax', or 'None'" adds nothing to
//!   that: the flag is the last SameSite attribute's enforcement, or
//!   "Default" if there is none ([`last_same_site`]).
//! - **§5.8.3 step 3, first bullet.** The "Either / Or" lists two
//!   alternatives, and the public-suffix condition is indented under the
//!   second. We read it as part of the second alternative (a cookie with
//!   host-only-flag false), which is the only reading under which a
//!   host-only cookie on a host that is itself a public suffix, which
//!   step 9 allows, can ever be sent back. For isolation either reading
//!   would do: a host-only cookie is returned only to its own host.
//!   `lemma_retrieve_within_root` needs the condition on the other
//!   alternative, and holds for every cookie with a non-empty domain (see
//!   the lemmas below).
//! - **§5.7 step 10 uses "request-host-canonical"**, which the draft binds
//!   only inside step 9 (and only when the domain-attribute is a public
//!   suffix). We canonicalize the request host up front and ignore the
//!   cookie if that fails (`docs/ERRATA.md`).
//! - **"Lax-allowing-unsafe"** (§5.6.7.2) is not used: it is a "MAY", and
//!   Phase 2 has no HTTP requests. Partitioned cookies and third-party
//!   cookie blocking are not in 6265bis.
//! - Strings are octets (`Seq<u8>`), as in the rest of the crate. A host
//!   name is ASCII, so the code points of `clazel-psl` are the octets
//!   ([`widen`]).
//! - The cookie-attribute-list is the parser's `Seq<Attribute>`; the cookie
//!   "received" by §5.7 is its `SetCookie` (`crate::set_cookie::spec`).
//!
//! # Lemmas this spec is for (statements fixed here, proved by item 2.9)
//!
//! These are the facts the isolation theorems use. They are proved in
//! `isolation.rs` (from `clazel_psl`'s `lemma_domain_match_same_root`, item
//! 2.4, and the bridge `lemma_domain_matches_bridge` between the octets of
//! this crate and its code points) and `lemmas.rs`. The statements as first
//! recorded here, in Verus syntax, with `rules: Seq<Rule>` the Public Suffix
//! List throughout; **two of them were wrong as recorded and are proved in a
//! corrected form**, marked below:
//!
//! ```text
//! // clazel-psl, item 2.4 (the dependency):
//! proof fn lemma_root_of_suffix(rules: Seq<Rule>, domain: Seq<u32>, s: Seq<u32>)
//!     requires 0 < s.len() < domain.len(), s.is_suffix_of(domain),
//!              domain[domain.len() - s.len() - 1] == 0x2E,
//!              !is_public_suffix(rules, s),
//!     ensures cookie_root_of_domain(rules, s) == cookie_root_of_domain(rules, domain);
//!
//! // Storing a cookie for a request to host h: the new cookie's domain has h's root.
//! proof fn lemma_store_within_root(rules, jar, url, ctx, received, now, host, new)
//!     requires url.host == Some(host),
//!              create_a_cookie(rules, jar, url, ctx, received, now) == Some(new),
//!     ensures cookie_root(rules, new.domain) == cookie_root(rules, host);
//!
//! // Retrieval for host h returns only cookies whose domain has h's root.
//! // Cookie by cookie; the cookies of `retrieval_cookie_list` are among
//! // those, since it filters by `cookie_is_retrieved` and sorts (a
//! // permutation).
//! // CORRECTED: as first recorded this said "from any jar (it needs no
//! // invariant of the jar)", which is false. A cookie with the empty string
//! // as its domain and host-only-flag false is not a public suffix and
//! // "domain-matches" every host that ends in "." (the empty domain string is
//! // a suffix of it, preceded by "."), and the cookie root of "" is "", of
//! // "a." is "a.". `isolation.rs` proves the counterexample
//! // (`example_empty_domain_breaks_retrieve_within_root`) and the lemma with
//! // the hypothesis `cookie_domain_nonempty(cookie)`, which every cookie
//! // `create_a_cookie` makes has (`lemma_store_preserves_domains_nonempty`).
//! proof fn lemma_retrieve_within_root(rules, url, ctx, host, cookie)
//!     requires url.host == Some(host), cookie_domain_nonempty(cookie),
//!              cookie_is_retrieved(rules, url, ctx, host, cookie),
//!     ensures cookie_root_of(rules, cookie) == cookie_root(rules, host);
//!
//! // Storing for host h leaves the cookies of every other root as they were
//! // (up to the eviction of expired ones, which depends only on `now`).
//! proof fn lemma_store_frame(rules, jar, url, ctx, received, now, host, other)
//!     requires url.host == Some(host), other != cookie_root(rules, host),
//!     ensures cookies_of_root(rules, store_a_cookie(rules, jar, url, ctx, received, now), other)
//!             == cookies_of_root(rules, evict_expired(jar, now), other);
//!
//! // Retrieval for host h changes no cookie of another root, likewise.
//! // CORRECTED: with the jar invariant `jar_domains_nonempty(jar)`, for the
//! // reason above.
//! proof fn lemma_retrieve_frame(rules, jar, url, ctx, now, host, other)
//!     requires url.host == Some(host), other != cookie_root(rules, host),
//!              jar_domains_nonempty(jar),
//!     ensures cookies_of_root(rules, jar_after_retrieval(rules, jar, url, ctx, now), other)
//!             == cookies_of_root(rules, evict_expired(jar, now), other);
//!
//! // Storage keeps every root within the limit and the keys unique.
//! proof fn lemma_store_bounds(rules, jar, url, ctx, received, now)
//!     requires jar_within_root_limit(rules, jar), jar_keys_unique(jar),
//!     ensures jar_within_root_limit(rules, store_a_cookie(rules, jar, url, ctx, received, now)),
//!             jar_keys_unique(store_a_cookie(rules, jar, url, ctx, received, now));
//! ```
//!
//! `lemma_store_frame` and `lemma_retrieve_frame` follow, in `isolation.rs`,
//! from the forms `lemmas.rs` proves, which need only the root of the new
//! cookie (`lemma_store_frame_of_new_root`) and "no retrieved cookie is
//! under `other`" (`lemma_retrieve_frame_of_root`, whose hypothesis is over
//! every cookie, so `isolation.rs` proves the form over the jar's cookies),
//! and the two `within_root` lemmas.

#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------
// The cookie, the request URL and the request context.
// ---------------------------------------------------------------------

/// A stored cookie: "The user agent stores the following fields about each
/// cookie: name, value, expiry-time, domain, path, creation-time,
/// last-access-time, persistent-flag, host-only-flag, secure-only-flag,
/// http-only-flag, and same-site-flag." (§5.7)
pub struct Cookie {
    /// name.
    pub name: Seq<u8>,
    /// value.
    pub value: Seq<u8>,
    /// expiry-time (seconds since 1601; [`latest_representable`] for a
    /// session cookie).
    pub expiry_time: int,
    /// domain (a canonicalized host, see the modelling choices).
    pub domain: crate::matching::spec::CanonicalHost,
    /// path.
    pub path: Seq<u8>,
    /// creation-time.
    pub creation_time: int,
    /// last-access-time.
    pub last_access_time: int,
    /// persistent-flag.
    pub persistent_flag: bool,
    /// host-only-flag.
    pub host_only_flag: bool,
    /// secure-only-flag.
    pub secure_only_flag: bool,
    /// http-only-flag.
    pub http_only_flag: bool,
    /// same-site-flag: "Default", "None", "Strict" or "Lax".
    pub same_site_flag: crate::set_cookie::spec::SameSite,
}

/// The request URL, as far as cookies read it: §5.7's "request-uri" and
/// §5.8's "retrieval's URI".
pub struct RequestUrl {
    /// The URL's scheme (an ASCII string, lower case).
    pub scheme: Seq<u8>,
    /// The URL's host, canonicalized (§5.1.2); `None` if it "fails to be
    /// canonicalized".
    pub host: Option<crate::matching::spec::CanonicalHost>,
    /// The URL's path, serialized (§5.1.4 "the path portion").
    pub path: Seq<u8>,
}

/// What §5.2, §5.7 step 18 and §5.8.3 step 3 read of an HTTP request.
pub struct HttpRequest {
    /// "The request's current url's origin."
    pub url_origin: clazel_origin::spec::Origin,
    /// "The request's client's 'site for cookies' (which is an origin)";
    /// `None` if "the request has no client or the request's client is
    /// null".
    pub site_for_cookies: Option<clazel_origin::spec::Origin>,
    /// "The request is the result of a reload navigation triggered through a
    /// user interface element."
    pub is_reload_navigation: bool,
    /// For such a reload: "the reloaded document was originally navigated to
    /// via a same-site request."
    pub reloaded_document_was_same_site: bool,
    /// "The request ... is navigating a top-level traversable" (§5.7 step
    /// 18.3).
    pub navigates_top_level_traversable: bool,
    /// "The HTTP request associated with the retrieval uses a 'safe'
    /// method."
    pub method_is_safe: bool,
    /// "The target browsing context of the HTTP request associated with the
    /// retrieval is the active browsing context or a top-level traversable."
    pub target_is_active_or_top_level: bool,
}

/// What §5.7 step 18.1 and §5.8.2 read of a call to a "non-HTTP" API from a
/// document (`document.cookie`).
pub struct DocumentCall {
    /// The calling document's "site for cookies" (§5.2.1).
    pub site_for_cookies: clazel_origin::spec::Origin,
    /// The "top-level origin" (§5.2.1).
    pub top_level_origin: clazel_origin::spec::Origin,
}

/// Where a cookie is received from, or a retrieval is for.
pub enum RequestContext {
    /// An HTTP request or response (type "HTTP").
    Http(HttpRequest),
    /// A "non-HTTP" API (type "non-HTTP").
    NonHttp(DocumentCall),
}

/// "The cookie was received from a 'non-HTTP' API" (§5.7 steps 15, 18.1,
/// 23.2), and "the retrieval's type is 'non-HTTP'" (§5.8.3 step 3).
pub open spec fn is_non_http(ctx: RequestContext) -> bool {
    ctx is NonHttp
}

// ---------------------------------------------------------------------
// §5.2 "Same-site" and "cross-site" requests.
// ---------------------------------------------------------------------

/// §5.2: a request is "same-site", and the "same-site status" of §5.8.2.
pub open spec fn is_same_site_request(rules: Seq<clazel_psl::spec::Rule>, ctx: RequestContext) -> bool {
    match ctx {
        RequestContext::Http(request) => if request.is_reload_navigation {
            // "Requests which are the result of a reload navigation
            // triggered through a user interface element are same-site if
            // the reloaded document was originally navigated to via a
            // same-site request." (Criterion 1 is false for them.)
            request.reloaded_document_was_same_site
        } else {
            // 1. "The request is not the result of a reload navigation".
            // 2. "The request's current url's origin is same-site with the
            //    request's client's 'site for cookies' (which is an
            //    origin), or if the request has no client or the request's
            //    client is null."
            match request.site_for_cookies {
                None => true,
                Some(site_for_cookies) => clazel_origin::spec::same_site(rules, request.url_origin, site_for_cookies),
            }
        },
        // §5.8.2: the retrieval's same-site status is "same-site" if the
        // Document's "site for cookies" is same-site with the top-level
        // origin (§5.2.1), "otherwise it is 'cross-site'".
        RequestContext::NonHttp(call) => clazel_origin::spec::same_site(rules, call.site_for_cookies, call.top_level_origin),
    }
}

// ---------------------------------------------------------------------
// Helpers: strings, URLs, hosts.
// ---------------------------------------------------------------------

/// "https"
pub open spec fn lit_https() -> Seq<u8> {
    seq![0x68u8, 0x74, 0x74, 0x70, 0x73]
}

/// "wss"
pub open spec fn lit_wss() -> Seq<u8> {
    seq![0x77u8, 0x73, 0x73]
}

/// The request URL "denote[s] a 'secure' connection (as defined by the user
/// agent)": its scheme is `https` or `wss`.
pub open spec fn url_is_secure(url: RequestUrl) -> bool {
    url.scheme == lit_https() || url.scheme == lit_wss()
}

/// The code points of an ASCII string of octets.
pub open spec fn widen(s: Seq<u8>) -> Seq<u32> {
    s.map_values(|c: u8| c as u32)
}

/// Every octet of `s` from index `i` is in CHAR (RFC 5234 B.1: %x01-7F; no
/// cookie string holds a NUL, so %x00-7F).
pub open spec fn all_char_from(s: Seq<u8>, i: nat) -> bool
    decreases s.len() - i
{
    i >= s.len() || (s[i as int] < 0x80 && all_char_from(s, i + 1))
}

/// `s` is a public suffix (over the Public Suffix List `rules`), as a
/// string of code points.
pub open spec fn is_public_suffix_string(rules: Seq<clazel_psl::spec::Rule>, s: Seq<u8>) -> bool {
    clazel_psl::spec::is_public_suffix(rules, widen(s))
}

/// §5.1.3 on canonicalized hosts, `string` against a cookie's `domain`: the
/// two are identical, or both are host names (not IP addresses) and the
/// domain string domain-matches the host string. See the modelling choice on
/// the cookie's domain.
pub open spec fn canonical_domain_matches(
    string: crate::matching::spec::CanonicalHost,
    domain: crate::matching::spec::CanonicalHost,
) -> bool {
    string == domain || (!string.is_ip_address && !domain.is_ip_address && crate::matching::spec::domain_matches(
        string.name,
        true,
        domain.name,
    ))
}

/// The cookie root of a canonicalized host (item 2.4): of a domain, the
/// shortest suffix, in labels, that is not a public suffix (or the domain
/// itself when every suffix is one); of an IP address, the address. Two hosts
/// can share a cookie exactly when their roots are equal.
pub open spec fn cookie_root(
    rules: Seq<clazel_psl::spec::Rule>,
    host: crate::matching::spec::CanonicalHost,
) -> crate::matching::spec::CanonicalHost {
    if host.is_ip_address {
        host
    } else {
        crate::matching::spec::CanonicalHost {
            name: crate::matching::spec::narrow(clazel_psl::spec::cookie_root_of_domain(rules, widen(host.name))),
            is_ip_address: false,
        }
    }
}

// ---------------------------------------------------------------------
// Limits and expiry.
// ---------------------------------------------------------------------

/// "the latest representable date": 2^64 - 1 seconds since 1601.
pub open spec fn latest_representable() -> int {
    18446744073709551615
}

/// The per-root limit on the cookies stored, 180 (§6.1 asks for at least 50
/// per domain; Chrome and Firefox keep 180). There is no global limit.
pub open spec fn max_cookies_per_root() -> nat {
    180
}

/// "A cookie is 'expired' if the cookie has an expiry date in the past."
pub open spec fn cookie_expired(cookie: Cookie, now: int) -> bool {
    cookie.expiry_time < now
}

/// The cookies that are not expired at `now`.
pub open spec fn not_expired(now: int) -> spec_fn(Cookie) -> bool {
    |c: Cookie| !cookie_expired(c, now)
}

/// "The user agent MUST evict all expired cookies from the cookie store."
pub open spec fn evict_expired(jar: Seq<Cookie>, now: int) -> Seq<Cookie> {
    jar.filter(not_expired(now))
}

/// The root of the cookie's domain.
pub open spec fn cookie_root_of(rules: Seq<clazel_psl::spec::Rule>, cookie: Cookie) -> crate::matching::spec::CanonicalHost {
    cookie_root(rules, cookie.domain)
}

/// The cookies whose domain has the cookie root `root`.
pub open spec fn in_root(rules: Seq<clazel_psl::spec::Rule>, root: crate::matching::spec::CanonicalHost) -> spec_fn(Cookie) -> bool {
    |c: Cookie| cookie_root_of(rules, c) == root
}

/// The cookies of `jar` whose domain has the cookie root `root`, in order.
pub open spec fn cookies_of_root(
    rules: Seq<clazel_psl::spec::Rule>,
    jar: Seq<Cookie>,
    root: crate::matching::spec::CanonicalHost,
) -> Seq<Cookie> {
    jar.filter(in_root(rules, root))
}

/// How many cookies of `jar` are under `root`.
pub open spec fn root_count(rules: Seq<clazel_psl::spec::Rule>, jar: Seq<Cookie>, root: crate::matching::spec::CanonicalHost) -> nat {
    cookies_of_root(rules, jar, root).len()
}

/// Which cookie of `root` is removed first (smaller goes first): §5.7's
/// priority, "Cookies whose secure-only-flag is false" (0), then those that
/// "share a domain field with more than a predetermined number of other
/// cookies" (1). Expired cookies, which come before both, are gone.
pub open spec fn eviction_class(cookie: Cookie) -> nat {
    if !cookie.secure_only_flag { 0 } else { 1 }
}

/// `a` is removed before `b`: a lower class, or the same class and an
/// earlier last-access-time ("If two cookies have the same removal priority,
/// the user agent MUST evict the cookie with the earliest last-access-time
/// first.").
pub open spec fn evicted_before(a: Cookie, b: Cookie) -> bool {
    eviction_class(a) < eviction_class(b) || (eviction_class(a) == eviction_class(b) && a.last_access_time < b.last_access_time)
}

/// The index of the cookie of `root` to remove first among the first `n`
/// cookies of `jar`; the earlier index wins a tie.
pub open spec fn victim_from(
    rules: Seq<clazel_psl::spec::Rule>,
    jar: Seq<Cookie>,
    root: crate::matching::spec::CanonicalHost,
    n: nat,
) -> Option<int>
    decreases n,
{
    if n == 0 {
        None
    } else {
        let previous = victim_from(rules, jar, root, (n - 1) as nat);
        let cookie = jar[n - 1];
        if cookie_root_of(rules, cookie) != root {
            previous
        } else {
            match previous {
                None => Some(n - 1),
                Some(j) => if evicted_before(cookie, jar[j]) { Some(n - 1) } else { Some(j) },
            }
        }
    }
}

/// "Remove excess cookies", for `root` only: while the root has more than
/// [`max_cookies_per_root`] cookies, remove the one the priority picks.
/// Only cookies of `root` are ever removed.
pub open spec fn evict_over_limit(
    rules: Seq<clazel_psl::spec::Rule>,
    jar: Seq<Cookie>,
    root: crate::matching::spec::CanonicalHost,
) -> Seq<Cookie>
    decreases jar.len(),
{
    if root_count(rules, jar, root) <= max_cookies_per_root() {
        jar
    } else {
        match victim_from(rules, jar, root, jar.len()) {
            Some(i) => if 0 <= i < jar.len() { evict_over_limit(rules, jar.remove(i), root) } else { jar },
            None => jar,
        }
    }
}

/// Two cookies have the same name, domain, host-only-flag and path (§5.7
/// step 23).
pub open spec fn same_key(a: Cookie, b: Cookie) -> bool {
    a.name == b.name && a.domain == b.domain && a.host_only_flag == b.host_only_flag && a.path == b.path
}

/// "this algorithm maintains the invariant that there is at most one such
/// cookie."
pub open spec fn jar_keys_unique(jar: Seq<Cookie>) -> bool {
    forall|i: int, j: int| 0 <= i < j < jar.len() ==> !same_key(#[trigger] jar[i], #[trigger] jar[j])
}

/// No root has more than [`max_cookies_per_root`] cookies.
pub open spec fn jar_within_root_limit(rules: Seq<clazel_psl::spec::Rule>, jar: Seq<Cookie>) -> bool {
    forall|root: crate::matching::spec::CanonicalHost| root_count(rules, jar, root) <= max_cookies_per_root()
}

// ---------------------------------------------------------------------
// Reading the cookie-attribute-list.
// ---------------------------------------------------------------------

/// The attribute-value of the last Max-Age attribute, if there is one.
pub open spec fn last_max_age(list: Seq<crate::set_cookie::spec::Attribute>) -> Option<int>
    decreases list.len(),
{
    if list.len() == 0 {
        None
    } else {
        match list[list.len() - 1] {
            crate::set_cookie::spec::Attribute::MaxAge(t) => Some(t),
            _ => last_max_age(list.drop_last()),
        }
    }
}

/// The attribute-value of the last Expires attribute, if there is one.
pub open spec fn last_expires(list: Seq<crate::set_cookie::spec::Attribute>) -> Option<int>
    decreases list.len(),
{
    if list.len() == 0 {
        None
    } else {
        match list[list.len() - 1] {
            crate::set_cookie::spec::Attribute::Expires(t) => Some(t),
            _ => last_expires(list.drop_last()),
        }
    }
}

/// The attribute-value of the last Domain attribute whose value "length is
/// no more than 1024 octets" (step 7).
pub open spec fn last_domain_within_1024(list: Seq<crate::set_cookie::spec::Attribute>) -> Option<Seq<u8>>
    decreases list.len(),
{
    if list.len() == 0 {
        None
    } else {
        match list[list.len() - 1] {
            crate::set_cookie::spec::Attribute::Domain(d) => if d.len() <= 1024 {
                Some(d)
            } else {
                last_domain_within_1024(list.drop_last())
            },
            _ => last_domain_within_1024(list.drop_last()),
        }
    }
}

/// The attribute-value of the last Path attribute whose value "length is no
/// more than 1024 octets" (step 11).
pub open spec fn last_path_within_1024(list: Seq<crate::set_cookie::spec::Attribute>) -> Option<Seq<u8>>
    decreases list.len(),
{
    if list.len() == 0 {
        None
    } else {
        match list[list.len() - 1] {
            crate::set_cookie::spec::Attribute::Path(p) => if p.len() <= 1024 {
                Some(p)
            } else {
                last_path_within_1024(list.drop_last())
            },
            _ => last_path_within_1024(list.drop_last()),
        }
    }
}

/// The enforcement of the last SameSite attribute, if there is one (step
/// 17; see the modelling choices).
pub open spec fn last_same_site(list: Seq<crate::set_cookie::spec::Attribute>) -> Option<crate::set_cookie::spec::SameSite>
    decreases list.len(),
{
    if list.len() == 0 {
        None
    } else {
        match list[list.len() - 1] {
            crate::set_cookie::spec::Attribute::SameSite(e) => Some(e),
            _ => last_same_site(list.drop_last()),
        }
    }
}

/// The cookie-attribute-list contains an HttpOnly attribute (step 14).
pub open spec fn contains_http_only_attribute(list: Seq<crate::set_cookie::spec::Attribute>) -> bool {
    exists|i: int| 0 <= i < list.len() && (#[trigger] list[i]) is HttpOnly
}

// ---------------------------------------------------------------------
// §5.7 Storage model.
// ---------------------------------------------------------------------

/// §5.7 step 6: the persistent-flag and the expiry-time.
pub open spec fn persistent_flag_and_expiry_time(list: Seq<crate::set_cookie::spec::Attribute>) -> (bool, int) {
    match last_max_age(list) {
        // 6. "If the cookie-attribute-list contains an attribute with an
        //    attribute-name of 'Max-Age': 1. Set the cookie's persistent-flag
        //    to true. 2. Set the cookie's expiry-time to attribute-value of
        //    the last attribute in the cookie-attribute-list with an
        //    attribute-name of 'Max-Age'."
        Some(t) => (true, t),
        None => match last_expires(list) {
            // 6. "Otherwise, if the cookie-attribute-list contains an
            //    attribute with an attribute-name of 'Expires' (and does not
            //    contain an attribute with an attribute-name of 'Max-Age'):
            //    1. Set the cookie's persistent-flag to true. 2. Set the
            //    cookie's expiry-time to attribute-value of the last
            //    attribute [...] 'Expires'."
            Some(t) => (true, t),
            // 6. "Otherwise: 1. Set the cookie's persistent-flag to false.
            //    2. Set the cookie's expiry-time to the latest representable
            //    date."
            None => (false, latest_representable()),
        },
    }
}

/// §5.7 step 9: the domain-attribute after "If the user agent is configured
/// to reject 'public suffixes' and the domain-attribute is a public suffix".
/// `None` is "abort this algorithm and ignore the cookie entirely".
pub open spec fn step_9_domain_attribute(
    rules: Seq<clazel_psl::spec::Rule>,
    request_host_canonical: crate::matching::spec::CanonicalHost,
    domain_attribute: Seq<u8>,
) -> Option<Seq<u8>> {
    if is_public_suffix_string(rules, domain_attribute) {
        // 9.1. "Let request-host-canonical be the canonicalized
        //      request-host." (The argument.)
        // 9.2. "If request-host fails to be canonicalized then abort this
        //      algorithm and ignore the cookie entirely." (Done by the
        //      caller, for every cookie: see the erratum.)
        // 9.3. "If the domain-attribute is identical to the
        //      request-host-canonical: 1. Let the domain-attribute be the
        //      empty string. Otherwise: 1. Abort this algorithm and ignore
        //      the cookie entirely."
        if domain_attribute == request_host_canonical.name {
            Some(seq![])
        } else {
            None
        }
    } else {
        Some(domain_attribute)
    }
}

/// §5.7 step 10: the cookie's domain and host-only-flag. `None` is "abort".
pub open spec fn step_10_domain(
    request_host_canonical: crate::matching::spec::CanonicalHost,
    domain_attribute: Seq<u8>,
) -> Option<(crate::matching::spec::CanonicalHost, bool)> {
    // 10. "If the domain-attribute is non-empty:"
    if domain_attribute.len() > 0 {
        // 10.1. "If request-host-canonical does not domain-match (see
        //       Section 5.1.3) the domain-attribute: 1. Abort this
        //       algorithm and ignore the cookie entirely."
        if !crate::matching::spec::domain_matches(
            request_host_canonical.name,
            !request_host_canonical.is_ip_address,
            domain_attribute,
        ) {
            None
        } else {
            // 10.1. "Otherwise: 1. Set the cookie's host-only-flag to
            //       false. 2. Set the cookie's domain to the
            //       domain-attribute."
            Some((
                crate::matching::spec::CanonicalHost {
                    name: domain_attribute,
                    is_ip_address: request_host_canonical.is_ip_address,
                },
                false,
            ))
        }
    } else {
        // 10. "Otherwise: 1. Set the cookie's host-only-flag to true. 2. Set
        //     the cookie's domain to request-host-canonical."
        Some((request_host_canonical, true))
    }
}

/// §5.7 step 16, the cookie store contains a cookie that "meet[s] all of
/// the following criteria": its name matches `name`, its secure-only-flag is
/// true, its domain domain-matches the new cookie's `domain` or vice-versa,
/// and the new cookie's `path` path-matches its path.
pub open spec fn secure_cookie_would_be_overlaid(
    jar: Seq<Cookie>,
    name: Seq<u8>,
    domain: crate::matching::spec::CanonicalHost,
    path: Seq<u8>,
) -> bool {
    exists|i: int|
        0 <= i < jar.len() && (#[trigger] jar[i]).name == name && jar[i].secure_only_flag && (canonical_domain_matches(
            jar[i].domain,
            domain,
        ) || canonical_domain_matches(domain, jar[i].domain)) && crate::matching::spec::path_matches(path, jar[i].path)
}

/// §5.7 step 18, given the same-site-flag is not "None": the cookie is not
/// ignored for its SameSite context. Sub-steps 18.1 to 18.3 continue
/// processing; 18.4 is `false`.
pub open spec fn step_18_continues(rules: Seq<clazel_psl::spec::Rule>, ctx: RequestContext) -> bool {
    // 18.1. "If the cookie was received from a 'non-HTTP' API, and the API
    //       was called from a navigable's active document whose 'site for
    //       cookies' is not same-site with the top-level origin, then abort
    //       this algorithm and ignore the newly created cookie entirely."
    if is_non_http(ctx) && !is_same_site_request(rules, ctx) {
        false
    } else if is_same_site_request(rules, ctx) {
        // 18.2. "If the cookie was received from a 'same-site' request (as
        //       defined in Section 5.2), skip the remaining substeps and
        //       continue processing the cookie."
        true
    } else {
        match ctx {
            // 18.3. "If the cookie was received from a request which is
            //       navigating a top-level traversable [HTML] [...], skip
            //       the remaining substeps and continue processing the
            //       cookie." 18.4. "Abort this algorithm and ignore the
            //       newly created cookie entirely." (A non-HTTP call that
            //       reaches here was aborted by 18.1.)
            RequestContext::Http(request) => request.navigates_top_level_traversable,
            RequestContext::NonHttp(_) => false,
        }
    }
}

/// The index of the first cookie of `jar`, from `i` on, with the same name,
/// domain, host-only-flag and path as `new` (step 23).
pub open spec fn find_old_cookie_from(jar: Seq<Cookie>, new: Cookie, i: nat) -> Option<int>
    decreases jar.len() - i,
{
    if i >= jar.len() {
        None
    } else if same_key(jar[i as int], new) {
        Some(i as int)
    } else {
        find_old_cookie_from(jar, new, i + 1)
    }
}

/// The old-cookie of step 23, if there is one.
pub open spec fn find_old_cookie(jar: Seq<Cookie>, new: Cookie) -> Option<int> {
    find_old_cookie_from(jar, new, 0)
}

/// `cookie` with its creation-time replaced.
pub open spec fn with_creation_time(cookie: Cookie, creation_time: int) -> Cookie {
    Cookie {
        name: cookie.name,
        value: cookie.value,
        expiry_time: cookie.expiry_time,
        domain: cookie.domain,
        path: cookie.path,
        creation_time,
        last_access_time: cookie.last_access_time,
        persistent_flag: cookie.persistent_flag,
        host_only_flag: cookie.host_only_flag,
        secure_only_flag: cookie.secure_only_flag,
        http_only_flag: cookie.http_only_flag,
        same_site_flag: cookie.same_site_flag,
    }
}

/// `cookie` with its last-access-time replaced.
pub open spec fn with_last_access_time(cookie: Cookie, last_access_time: int) -> Cookie {
    Cookie {
        name: cookie.name,
        value: cookie.value,
        expiry_time: cookie.expiry_time,
        domain: cookie.domain,
        path: cookie.path,
        creation_time: cookie.creation_time,
        last_access_time,
        persistent_flag: cookie.persistent_flag,
        host_only_flag: cookie.host_only_flag,
        secure_only_flag: cookie.secure_only_flag,
        http_only_flag: cookie.http_only_flag,
        same_site_flag: cookie.same_site_flag,
    }
}

/// §5.7 steps 1 to 23.3: the newly-created cookie when the user agent
/// "receives a cookie" `received` (the §5.6 parse of a Set-Cookie string)
/// from a request to `url`, over the cookie store `jar`; `None` is "abort
/// this algorithm and ignore the cookie entirely". `jar` is a store with no
/// expired cookie ([`store_a_cookie`] evicts them first).
pub open spec fn create_a_cookie(
    rules: Seq<clazel_psl::spec::Rule>,
    jar: Seq<Cookie>,
    url: RequestUrl,
    ctx: RequestContext,
    received: crate::set_cookie::spec::SetCookie,
    now: int,
) -> Option<Cookie> {
    // 1. "A user agent MAY ignore a received cookie in its entirety. See
    //    Section 5.3." (Not ignored: see the modelling choices.)
    // 2. "If cookie-name is empty and cookie-value is empty, abort this
    //    algorithm and ignore the cookie entirely."
    if received.name.len() == 0 && received.value.len() == 0 {
        None
    // 3. "If the cookie-name or the cookie-value contains a %x00-08 /
    //    %x0A-1F / %x7F character (CTL characters excluding HTAB), abort
    //    this algorithm and ignore the cookie entirely."
    } else if crate::set_cookie::spec::contains_ctl_excluding_htab(received.name)
        || crate::set_cookie::spec::contains_ctl_excluding_htab(received.value) {
        None
    // 4. "If the sum of the lengths of cookie-name and cookie-value is more
    //    than 4096 octets, abort this algorithm and ignore the cookie
    //    entirely."
    } else if received.name.len() + received.value.len() > 4096 {
        None
    } else {
        // 5. "Create a new cookie with name cookie-name, value cookie-value.
        //    Set the creation-time and the last-access-time to the current
        //    date and time." (Below, once its fields are known.)
        // 6. persistent-flag and expiry-time.
        let (persistent_flag, expiry_time) = persistent_flag_and_expiry_time(received.attributes);
        // 7. "If the cookie-attribute-list contains an attribute with an
        //    attribute-name of 'Domain': 1. Let the domain-attribute be the
        //    attribute-value of the last attribute in the
        //    cookie-attribute-list with both an attribute-name of 'Domain'
        //    and an attribute-value whose length is no more than 1024
        //    octets. [...] Otherwise: 1. Let the domain-attribute be the
        //    empty string."
        let domain_attribute = match last_domain_within_1024(received.attributes) {
            Some(d) => d,
            None => seq![],
        };
        // 8. "If the domain-attribute contains a character that is not in
        //    CHAR, abort this algorithm and ignore the cookie entirely."
        if !all_char_from(domain_attribute, 0) {
            None
        } else {
            match url.host {
                // 9.2 and 10 (see the erratum): the request-host-canonical.
                None => None,
                Some(request_host_canonical) => {
                    // 9. "If the user agent is configured to reject 'public
                    //    suffixes' and the domain-attribute is a public
                    //    suffix: [...]"
                    match step_9_domain_attribute(rules, request_host_canonical, domain_attribute) {
                        None => None,
                        Some(domain_attribute) => {
                            // 10. "If the domain-attribute is non-empty: [...]"
                            match step_10_domain(request_host_canonical, domain_attribute) {
                                None => None,
                                Some((domain, host_only_flag)) => {
                                    // 11. "If the cookie-attribute-list contains an
                                    //     attribute with an attribute-name of 'Path',
                                    //     set the cookie's path to attribute-value of
                                    //     the last attribute in the
                                    //     cookie-attribute-list with both an
                                    //     attribute-name of 'Path' and an
                                    //     attribute-value whose length is no more than
                                    //     1024 octets. Otherwise, set the cookie's path
                                    //     to the default-path of the request-uri."
                                    let path = match last_path_within_1024(received.attributes) {
                                        Some(p) => p,
                                        None => crate::matching::spec::default_path(url.path),
                                    };
                                    // 12. "If the cookie-attribute-list contains an
                                    //     attribute with an attribute-name of 'Secure',
                                    //     set the cookie's secure-only-flag to true.
                                    //     Otherwise, set the cookie's secure-only-flag
                                    //     to false."
                                    let secure_only_flag = crate::set_cookie::spec::contains_secure_attribute(received.attributes);
                                    // 13. "If the request-uri does not denote a
                                    //     'secure' connection (as defined by the user
                                    //     agent), and the cookie's secure-only-flag is
                                    //     true, then abort these steps and ignore the
                                    //     cookie entirely."
                                    if !url_is_secure(url) && secure_only_flag {
                                        None
                                    } else {
                                        // 14. "If the cookie-attribute-list contains an
                                        //     attribute with an attribute-name of
                                        //     'HttpOnly', set the cookie's
                                        //     http-only-flag to true. Otherwise, set the
                                        //     cookie's http-only-flag to false."
                                        let http_only_flag = contains_http_only_attribute(received.attributes);
                                        // 15. "If the cookie was received from a
                                        //     'non-HTTP' API and the cookie's
                                        //     http-only-flag is true, abort this
                                        //     algorithm and ignore the cookie entirely."
                                        if is_non_http(ctx) && http_only_flag {
                                            None
                                        // 16. "If the cookie's secure-only-flag is false,
                                        //     and the request-uri does not denote a
                                        //     'secure' connection, then abort this
                                        //     algorithm and ignore the cookie entirely if
                                        //     the cookie store contains one or more
                                        //     cookies that meet all of the following
                                        //     criteria: [...]"
                                        } else if !secure_only_flag && !url_is_secure(url) && secure_cookie_would_be_overlaid(
                                            jar,
                                            received.name,
                                            domain,
                                            path,
                                        ) {
                                            None
                                        } else {
                                            // 17. same-site-flag.
                                            let same_site_flag = match last_same_site(received.attributes) {
                                                Some(e) => e,
                                                None => crate::set_cookie::spec::SameSite::Default,
                                            };
                                            // 18. "If the cookie's same-site-flag is not
                                            //     'None': [...]"
                                            if same_site_flag != crate::set_cookie::spec::SameSite::None && !step_18_continues(
                                                rules,
                                                ctx,
                                            ) {
                                                None
                                            // 19. "If the cookie's 'same-site-flag' is
                                            //     'None', abort this algorithm and ignore
                                            //     the cookie entirely unless the cookie's
                                            //     secure-only-flag is true."
                                            } else if same_site_flag == crate::set_cookie::spec::SameSite::None && !secure_only_flag {
                                                None
                                            // 20. to 22. The name prefix requirements
                                            //     (§5.4).
                                            } else if !crate::set_cookie::spec::name_prefix_requirements_met(
                                                received,
                                                secure_only_flag,
                                                host_only_flag,
                                            ) {
                                                None
                                            } else {
                                                let new = Cookie {
                                                    name: received.name,
                                                    value: received.value,
                                                    expiry_time,
                                                    domain,
                                                    path,
                                                    // 5. "Set the creation-time and the
                                                    //    last-access-time to the current
                                                    //    date and time."
                                                    creation_time: now,
                                                    last_access_time: now,
                                                    persistent_flag,
                                                    host_only_flag,
                                                    secure_only_flag,
                                                    http_only_flag,
                                                    same_site_flag,
                                                };
                                                // 23. "If the cookie store contains a
                                                //     cookie with the same name, domain,
                                                //     host-only-flag, and path as the
                                                //     newly-created cookie: [...]"
                                                match find_old_cookie(jar, new) {
                                                    None => Some(new),
                                                    // 23.1. "Let old-cookie be the
                                                    //       existing cookie [...]"
                                                    Some(i) => {
                                                        let old_cookie = jar[i];
                                                        // 23.2. "If the newly-created
                                                        //       cookie was received from a
                                                        //       'non-HTTP' API and the
                                                        //       old-cookie's http-only-flag
                                                        //       is true, abort this
                                                        //       algorithm and ignore the
                                                        //       newly created cookie
                                                        //       entirely."
                                                        if is_non_http(ctx) && old_cookie.http_only_flag {
                                                            None
                                                        } else {
                                                            // 23.3. "Update the
                                                            //       creation-time of the
                                                            //       newly-created cookie to
                                                            //       match the creation-time
                                                            //       of the old-cookie."
                                                            Some(with_creation_time(new, old_cookie.creation_time))
                                                        }
                                                    },
                                                }
                                            }
                                        }
                                    }
                                },
                            }
                        },
                    }
                },
            }
        }
    }
}

/// §5.7 steps 23.4 and 24: "Remove the old-cookie from the cookie store",
/// then "Insert the newly-created cookie into the cookie store".
pub open spec fn insert_a_cookie(jar: Seq<Cookie>, new: Cookie) -> Seq<Cookie> {
    // 23.4.
    let without_old = match find_old_cookie(jar, new) {
        Some(i) => jar.remove(i),
        None => jar,
    };
    // 24.
    without_old.push(new)
}

/// The cookie store after the user agent "receives a cookie" `received`
/// from a request to `url` at time `now` (§5.7 in full, with the eviction of
/// expired cookies and of the excess cookies of the new cookie's root).
pub open spec fn store_a_cookie(
    rules: Seq<clazel_psl::spec::Rule>,
    jar: Seq<Cookie>,
    url: RequestUrl,
    ctx: RequestContext,
    received: crate::set_cookie::spec::SetCookie,
    now: int,
) -> Seq<Cookie> {
    let live = evict_expired(jar, now);
    match create_a_cookie(rules, live, url, ctx, received, now) {
        None => live,
        Some(new) => evict_over_limit(rules, evict_expired(insert_a_cookie(live, new), now), cookie_root_of(rules, new)),
    }
}

/// The cookie store after a Set-Cookie string `s` is received from a request
/// to `url` at time `now`: §5.6's parse (an unparsable string is "ignore the
/// set-cookie-string entirely"), then [`store_a_cookie`]. This is what
/// `document.cookie`'s setter calls, with a `NonHttp` context.
pub open spec fn store_a_set_cookie_string(
    rules: Seq<clazel_psl::spec::Rule>,
    jar: Seq<Cookie>,
    s: Seq<u8>,
    url: RequestUrl,
    ctx: RequestContext,
    now: int,
) -> Seq<Cookie> {
    match crate::set_cookie::spec::parse_a_set_cookie_string(s, url.path, now) {
        None => evict_expired(jar, now),
        Some(received) => store_a_cookie(rules, jar, url, ctx, received, now),
    }
}

// ---------------------------------------------------------------------
// §5.8 Retrieval model.
// ---------------------------------------------------------------------

/// §5.8.3 step 3: the cookie "meets all of the following requirements" for a
/// retrieval of `url` over `ctx`, whose host is `retrieval_host_canonical`.
pub open spec fn cookie_is_retrieved(
    rules: Seq<clazel_psl::spec::Rule>,
    url: RequestUrl,
    ctx: RequestContext,
    retrieval_host_canonical: crate::matching::spec::CanonicalHost,
    cookie: Cookie,
) -> bool {
    // * "Either: The cookie's host-only-flag is true and
    //   retrieval-host-canonical is identical to the cookie's domain. Or:
    //   The cookie's host-only-flag is false and retrieval-host-canonical
    //   domain-matches (see Section 5.1.3) the cookie's domain. The
    //   cookie's domain is not a public suffix, for user agents configured
    //   to reject 'public suffixes'." (The last on the second alternative:
    //   see the modelling choices.)
    ((cookie.host_only_flag && retrieval_host_canonical == cookie.domain) || (!cookie.host_only_flag
        && canonical_domain_matches(retrieval_host_canonical, cookie.domain) && !(!cookie.domain.is_ip_address
        && is_public_suffix_string(rules, cookie.domain.name))))
    // * "The retrieval's URI's path path-matches the cookie's path."
    && crate::matching::spec::path_matches(url.path, cookie.path)
    // * "If the cookie's secure-only-flag is true, then the retrieval's URI
    //   must denote a 'secure' connection (as defined by the user agent)."
    && (cookie.secure_only_flag ==> url_is_secure(url))
    // * "If the cookie's http-only-flag is true, then exclude the cookie if
    //   the retrieval's type is 'non-HTTP'."
    && !(cookie.http_only_flag && is_non_http(ctx))
    // * "If the cookie's same-site-flag is not 'None' and the retrieval's
    //   same-site status is 'cross-site', then exclude the cookie unless
    //   all of the following conditions are met: The retrieval's type is
    //   'HTTP'. The same-site-flag is 'Lax' or 'Default'. The HTTP request
    //   associated with the retrieval uses a 'safe' method. The target
    //   browsing context of the HTTP request associated with the retrieval
    //   is the active browsing context or a top-level traversable."
    && ((cookie.same_site_flag != crate::set_cookie::spec::SameSite::None && !is_same_site_request(rules, ctx)) ==> (match ctx {
        RequestContext::Http(request) => (cookie.same_site_flag == crate::set_cookie::spec::SameSite::Lax
            || cookie.same_site_flag == crate::set_cookie::spec::SameSite::Default) && request.method_is_safe
            && request.target_is_active_or_top_level,
        RequestContext::NonHttp(_) => false,
    }))
}

/// Whether `a` is listed before `b` (step 4): "Cookies with longer paths are
/// listed before cookies with shorter paths. Among cookies that have equal-
/// length path fields, cookies with earlier creation-times are listed before
/// cookies with later creation-times."
pub open spec fn cookie_listed_before(a: Cookie, b: Cookie) -> bool {
    a.path.len() > b.path.len() || (a.path.len() == b.path.len() && a.creation_time < b.creation_time)
}

/// `cookie` inserted into the sorted list `sorted`, after every cookie not
/// listed after it (so a stable sort).
pub open spec fn insert_sorted(sorted: Seq<Cookie>, cookie: Cookie) -> Seq<Cookie>
    decreases sorted.len(),
{
    if sorted.len() == 0 {
        seq![cookie]
    } else if cookie_listed_before(cookie, sorted[0]) {
        seq![cookie] + sorted
    } else {
        seq![sorted[0]] + insert_sorted(sorted.skip(1), cookie)
    }
}

/// The cookies of `list` from `i` on inserted, in order, into `sorted`.
pub open spec fn sort_from(list: Seq<Cookie>, i: nat, sorted: Seq<Cookie>) -> Seq<Cookie>
    decreases list.len() - i,
{
    if i >= list.len() {
        sorted
    } else {
        sort_from(list, i + 1, insert_sorted(sorted, list[i as int]))
    }
}

/// Step 4: "The user agent SHOULD sort the cookie-list in the following
/// order" (stably).
pub open spec fn sort_cookie_list(list: Seq<Cookie>) -> Seq<Cookie> {
    sort_from(list, 0, seq![])
}

/// §5.8.3 steps 1 to 4: the sorted cookie-list for a retrieval of `url` over
/// `ctx`, from the store `jar` (which holds no expired cookie; see
/// [`retrieve_cookie_string`]).
pub open spec fn retrieval_cookie_list(
    rules: Seq<clazel_psl::spec::Rule>,
    jar: Seq<Cookie>,
    url: RequestUrl,
    ctx: RequestContext,
) -> Seq<Cookie> {
    match url.host {
        // 1. "Let retrieval-host-canonical be the canonicalized host of the
        //    retrieval's URI." 2. "If the host of the retrieval's URI fails
        //    to be canonicalized then abort this algorithm." (No cookies.)
        None => seq![],
        Some(retrieval_host_canonical) => {
            // 3. "Let cookie-list be the set of cookies from the cookie store
            //    that meets all of the following requirements: [...]"
            let cookie_list = jar.filter(|c: Cookie| cookie_is_retrieved(rules, url, ctx, retrieval_host_canonical, c));
            // 4. "The user agent SHOULD sort the cookie-list [...]"
            sort_cookie_list(cookie_list)
        },
    }
}

/// §5.8.3 step 6: serialize the cookies of `list` from index `i` on.
pub open spec fn serialize_cookie_list_from(list: Seq<Cookie>, i: nat) -> Seq<u8>
    decreases list.len() - i,
{
    if i >= list.len() {
        seq![]
    } else {
        let cookie = list[i as int];
        // 6.1. "If the cookies' name is not empty, output the cookie's name
        //      followed by the %x3D ("=") character."
        let name_part: Seq<u8> = if cookie.name.len() > 0 {
            cookie.name + seq![0x3Du8]
        } else {
            seq![]
        };
        // 6.2. "If the cookies' value is not empty, output the cookie's
        //      value." (An empty value outputs nothing.)
        // 6.3. "If the cookie was not the last cookie in the cookie-list,
        //      output the characters %x3B and %x20 ("; ")."
        let separator: Seq<u8> = if i + 1 < list.len() {
            seq![0x3Bu8, 0x20]
        } else {
            seq![]
        };
        name_part + cookie.value + separator + serialize_cookie_list_from(list, i + 1)
    }
}

/// The cookie-string of a retrieval of `url` over `ctx` at time `now` from the
/// cookie store `jar` (§5.8.3), after the eviction of expired cookies. For
/// `document.cookie`'s getter, `ctx` is `NonHttp`.
pub open spec fn retrieve_cookie_string(
    rules: Seq<clazel_psl::spec::Rule>,
    jar: Seq<Cookie>,
    url: RequestUrl,
    ctx: RequestContext,
    now: int,
) -> Seq<u8> {
    serialize_cookie_list_from(retrieval_cookie_list(rules, evict_expired(jar, now), url, ctx), 0)
}

/// Step 5 for one cookie: "Update the last-access-time of each cookie in
/// the cookie-list to the current date and time." A cookie is in the
/// cookie-list exactly when [`cookie_is_retrieved`].
pub open spec fn update_last_access_time(
    rules: Seq<clazel_psl::spec::Rule>,
    url: RequestUrl,
    ctx: RequestContext,
    retrieval_host_canonical: crate::matching::spec::CanonicalHost,
    now: int,
) -> spec_fn(Cookie) -> Cookie {
    |c: Cookie|
        if cookie_is_retrieved(rules, url, ctx, retrieval_host_canonical, c) {
            with_last_access_time(c, now)
        } else {
            c
        }
}

/// The cookie store after the retrieval: expired cookies are evicted, and
/// step 5 is applied.
pub open spec fn jar_after_retrieval(
    rules: Seq<clazel_psl::spec::Rule>,
    jar: Seq<Cookie>,
    url: RequestUrl,
    ctx: RequestContext,
    now: int,
) -> Seq<Cookie> {
    let live = evict_expired(jar, now);
    match url.host {
        None => live,
        Some(retrieval_host_canonical) => live.map_values(
            update_last_access_time(rules, url, ctx, retrieval_host_canonical, now),
        ),
    }
}

} // verus!
