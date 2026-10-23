//! The executable storage and retrieval models (RFC 6265bis §5.2, §5.7,
//! §5.8), proven to meet [`super::contract`]. The code mirrors the spec; the
//! step comments live in [`super::spec`].
//!
//! Where the spec says "the cookies of root r", the code needs the cookie
//! root of a domain, which is `clazel_psl::exec::cookie_root_of_domain_exec`
//! over the generated Public Suffix List tables. It is called only when the
//! per-root limit can be exceeded (the jar has more than 180 cookies): a jar
//! of at most 180 cookies has no root over the limit.

use super::spec::*;
use crate::matching::exec::{CanonicalHostName, domain_matches};
use crate::set_cookie::exec::{AttributeExec, SetCookieRecord};
use crate::set_cookie::spec::SameSite;
use crate::strings::{copy, slice_eq};
use clazel_origin::exec::{ParsedOrigin, same_site_exec};
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------
// Records.
// ---------------------------------------------------------------------

/// A stored cookie, viewed as [`Cookie`]. Times are seconds since
/// 1601-01-01T00:00:00Z.
pub struct CookieRecord {
    /// name.
    pub name: Vec<u8>,
    /// value.
    pub value: Vec<u8>,
    /// expiry-time.
    pub expiry_time: u64,
    /// domain.
    pub domain: CanonicalHostName,
    /// path.
    pub path: Vec<u8>,
    /// creation-time.
    pub creation_time: u64,
    /// last-access-time.
    pub last_access_time: u64,
    /// persistent-flag.
    pub persistent_flag: bool,
    /// host-only-flag.
    pub host_only_flag: bool,
    /// secure-only-flag.
    pub secure_only_flag: bool,
    /// http-only-flag.
    pub http_only_flag: bool,
    /// same-site-flag.
    pub same_site_flag: SameSite,
}

impl View for CookieRecord {
    type V = Cookie;

    open spec fn view(&self) -> Cookie {
        Cookie {
            name: self.name@,
            value: self.value@,
            expiry_time: self.expiry_time as int,
            domain: self.domain@,
            path: self.path@,
            creation_time: self.creation_time as int,
            last_access_time: self.last_access_time as int,
            persistent_flag: self.persistent_flag,
            host_only_flag: self.host_only_flag,
            secure_only_flag: self.secure_only_flag,
            http_only_flag: self.http_only_flag,
            same_site_flag: self.same_site_flag,
        }
    }
}

/// The view of a jar.
pub open spec fn jar_view(v: Seq<CookieRecord>) -> Seq<Cookie> {
    v.map_values(|c: CookieRecord| c@)
}

/// The request URL (scheme, canonical host, path), viewed as [`RequestUrl`].
pub struct RequestUrlRecord {
    /// The URL's scheme.
    pub scheme: Vec<u8>,
    /// The URL's canonicalized host; `None` if it failed to canonicalize.
    pub host: Option<CanonicalHostName>,
    /// The URL's path.
    pub path: Vec<u8>,
}

impl View for RequestUrlRecord {
    type V = RequestUrl;

    open spec fn view(&self) -> RequestUrl {
        RequestUrl { scheme: self.scheme@, host: crate::matching::exec::option_view(self.host), path: self.path@ }
    }
}

/// The view of an optional origin.
pub open spec fn origin_option_view(o: Option<ParsedOrigin>) -> Option<clazel_origin::spec::Origin> {
    match o {
        Some(o) => Some(o@),
        None => None,
    }
}

/// An HTTP request's cookie-relevant state, viewed as [`HttpRequest`].
pub struct HttpRequestRecord {
    /// The request's current url's origin.
    pub url_origin: ParsedOrigin,
    /// The request's client's "site for cookies".
    pub site_for_cookies: Option<ParsedOrigin>,
    /// See [`HttpRequest`].
    pub is_reload_navigation: bool,
    /// See [`HttpRequest`].
    pub reloaded_document_was_same_site: bool,
    /// See [`HttpRequest`].
    pub navigates_top_level_traversable: bool,
    /// See [`HttpRequest`].
    pub method_is_safe: bool,
    /// See [`HttpRequest`].
    pub target_is_active_or_top_level: bool,
}

impl View for HttpRequestRecord {
    type V = HttpRequest;

    open spec fn view(&self) -> HttpRequest {
        HttpRequest {
            url_origin: self.url_origin@,
            site_for_cookies: origin_option_view(self.site_for_cookies),
            is_reload_navigation: self.is_reload_navigation,
            reloaded_document_was_same_site: self.reloaded_document_was_same_site,
            navigates_top_level_traversable: self.navigates_top_level_traversable,
            method_is_safe: self.method_is_safe,
            target_is_active_or_top_level: self.target_is_active_or_top_level,
        }
    }
}

/// A call to a "non-HTTP" API from a document, viewed as [`DocumentCall`].
pub struct DocumentCallRecord {
    /// The calling document's "site for cookies".
    pub site_for_cookies: ParsedOrigin,
    /// The "top-level origin".
    pub top_level_origin: ParsedOrigin,
}

impl View for DocumentCallRecord {
    type V = DocumentCall;

    open spec fn view(&self) -> DocumentCall {
        DocumentCall { site_for_cookies: self.site_for_cookies@, top_level_origin: self.top_level_origin@ }
    }
}

/// Where a cookie is received from, or a retrieval is for, viewed as
/// [`RequestContext`].
pub enum RequestContextRecord {
    /// An HTTP request or response.
    Http(HttpRequestRecord),
    /// A "non-HTTP" API.
    NonHttp(DocumentCallRecord),
}

impl View for RequestContextRecord {
    type V = RequestContext;

    open spec fn view(&self) -> RequestContext {
        match self {
            RequestContextRecord::Http(r) => RequestContext::Http(r@),
            RequestContextRecord::NonHttp(c) => RequestContext::NonHttp(c@),
        }
    }
}

// ---------------------------------------------------------------------
// Small helpers.
// ---------------------------------------------------------------------

/// A copy of a canonical host.
pub fn clone_host(h: &CanonicalHostName) -> (r: CanonicalHostName)
    ensures
        r@ == h@,
{
    CanonicalHostName { name: copy(h.name.as_slice()), is_ip_address: h.is_ip_address }
}

/// A copy of a SameSite enforcement.
pub fn clone_same_site(s: &SameSite) -> (r: SameSite)
    ensures
        r == *s,
{
    match s {
        SameSite::Default => SameSite::Default,
        SameSite::None => SameSite::None,
        SameSite::Strict => SameSite::Strict,
        SameSite::Lax => SameSite::Lax,
    }
}

/// A copy of a cookie.
pub fn clone_cookie(c: &CookieRecord) -> (r: CookieRecord)
    ensures
        r@ == c@,
{
    CookieRecord {
        name: copy(c.name.as_slice()),
        value: copy(c.value.as_slice()),
        expiry_time: c.expiry_time,
        domain: clone_host(&c.domain),
        path: copy(c.path.as_slice()),
        creation_time: c.creation_time,
        last_access_time: c.last_access_time,
        persistent_flag: c.persistent_flag,
        host_only_flag: c.host_only_flag,
        secure_only_flag: c.secure_only_flag,
        http_only_flag: c.http_only_flag,
        same_site_flag: clone_same_site(&c.same_site_flag),
    }
}

/// The code points of an ASCII string of octets.
pub fn widen_exec(s: &[u8]) -> (out: Vec<u32>)
    ensures
        out@ == widen(s@),
{
    let mut v: Vec<u32> = Vec::new();
    let mut i: usize = 0;
    while i < s.len()
        invariant
            i <= s.len(),
            v@ == widen(s@).subrange(0, i as int),
        decreases s.len() - i,
    {
        let c = match s.get(i) {
            Some(c) => *c,
            None => 0,
        };
        v.push(c as u32);
        assert(widen(s@).subrange(0, i as int).push(widen(s@)[i as int]) =~= widen(s@).subrange(0, i as int + 1));
        // Never saturates: i < s.len().
        i = i.saturating_add(1);
    }
    assert(widen(s@).subrange(0, s.len() as int) =~= widen(s@));
    v
}

/// The octets of a string of code points, each cut to its low 8 bits
/// ([`crate::matching::spec::narrow`]).
pub fn narrow_exec(s: &[u32]) -> (out: Vec<u8>)
    ensures
        out@ == crate::matching::spec::narrow(s@),
{
    let mut v: Vec<u8> = Vec::new();
    let mut i: usize = 0;
    while i < s.len()
        invariant
            i <= s.len(),
            v@ == crate::matching::spec::narrow(s@).subrange(0, i as int),
        decreases s.len() - i,
    {
        let c = match s.get(i) {
            Some(c) => *c,
            None => 0,
        };
        v.push(c as u8);
        assert(crate::matching::spec::narrow(s@).subrange(0, i as int).push(crate::matching::spec::narrow(s@)[i as int])
            =~= crate::matching::spec::narrow(s@).subrange(0, i as int + 1));
        // Never saturates: i < s.len().
        i = i.saturating_add(1);
    }
    assert(crate::matching::spec::narrow(s@).subrange(0, s.len() as int) =~= crate::matching::spec::narrow(s@));
    v
}

/// Is `s` a public suffix, over the generated Public Suffix List?
pub fn is_public_suffix_string_exec(s: &[u8]) -> (r: bool)
    ensures
        r == is_public_suffix_string(clazel_psl::table::psl_rules(), s@),
{
    let w = widen_exec(s);
    clazel_psl::exec::is_public_suffix_exec(w.as_slice())
}

/// The cookie root of a canonical host ([`cookie_root`]), over the
/// generated Public Suffix List.
pub fn cookie_root_exec(h: &CanonicalHostName) -> (r: CanonicalHostName)
    ensures
        r@ == cookie_root(clazel_psl::table::psl_rules(), h@),
{
    if h.is_ip_address {
        clone_host(h)
    } else {
        let w = widen_exec(h.name.as_slice());
        let root = clazel_psl::exec::cookie_root_of_domain_exec(w.as_slice());
        CanonicalHostName { name: narrow_exec(root.as_slice()), is_ip_address: false }
    }
}

/// Two canonical hosts are identical.
pub fn hosts_equal(a: &CanonicalHostName, b: &CanonicalHostName) -> (r: bool)
    ensures
        r == (a@ == b@),
{
    a.is_ip_address == b.is_ip_address && slice_eq(a.name.as_slice(), b.name.as_slice())
}

/// [`canonical_domain_matches`].
pub fn canonical_domain_matches_exec(string: &CanonicalHostName, domain: &CanonicalHostName) -> (r: bool)
    ensures
        r == canonical_domain_matches(string@, domain@),
{
    if hosts_equal(string, domain) {
        return true;
    }
    !string.is_ip_address && !domain.is_ip_address && domain_matches(string.name.as_slice(), true, domain.name.as_slice())
}

/// [`url_is_secure`]: the scheme is `https` or `wss`.
pub fn url_is_secure_exec(url: &RequestUrlRecord) -> (r: bool)
    ensures
        r == url_is_secure(url@),
{
    let https: Vec<u8> = vec![0x68u8, 0x74, 0x74, 0x70, 0x73];
    let wss: Vec<u8> = vec![0x77u8, 0x73, 0x73];
    assert(https@ =~= lit_https());
    assert(wss@ =~= lit_wss());
    slice_eq(url.scheme.as_slice(), https.as_slice()) || slice_eq(url.scheme.as_slice(), wss.as_slice())
}

/// [`is_same_site_request`] over the generated Public Suffix List.
pub fn is_same_site_request_exec(ctx: &RequestContextRecord) -> (r: bool)
    ensures
        r == is_same_site_request(clazel_psl::table::psl_rules(), ctx@),
{
    match ctx {
        RequestContextRecord::Http(request) => {
            if request.is_reload_navigation {
                request.reloaded_document_was_same_site
            } else {
                match &request.site_for_cookies {
                    None => true,
                    Some(site_for_cookies) => same_site_exec(&request.url_origin, site_for_cookies),
                }
            }
        },
        RequestContextRecord::NonHttp(call) => same_site_exec(&call.site_for_cookies, &call.top_level_origin),
    }
}

/// [`is_non_http`].
pub fn is_non_http_exec(ctx: &RequestContextRecord) -> (r: bool)
    ensures
        r == is_non_http(ctx@),
{
    match ctx {
        RequestContextRecord::Http(_) => false,
        RequestContextRecord::NonHttp(_) => true,
    }
}

// ---------------------------------------------------------------------
// Reading the cookie-attribute-list.
// ---------------------------------------------------------------------

/// [`last_max_age`]: the attribute-value of the last Max-Age attribute.
pub fn last_max_age_exec(attrs: &[AttributeExec]) -> (r: Option<u64>)
    ensures
        last_max_age(crate::set_cookie::exec::attributes_view(attrs@)) == (match r {
            Some(t) => Some(t as int),
            None => None::<int>,
        }),
{
    let ghost av = crate::set_cookie::exec::attributes_view(attrs@);
    let mut acc: Option<u64> = None;
    let mut i: usize = 0;
    assert(av.take(0) =~= Seq::<crate::set_cookie::spec::Attribute>::empty());
    while i < attrs.len()
        invariant
            i <= attrs.len(),
            av == crate::set_cookie::exec::attributes_view(attrs@),
            last_max_age(av.take(i as int)) == (match acc {
                Some(t) => Some(t as int),
                None => None::<int>,
            }),
        decreases attrs.len() - i,
    {
        let ghost t1 = av.take(i as int + 1);
        assert(t1.drop_last() =~= av.take(i as int));
        assert(t1.last() == av[i as int]);
        assert(av[i as int] == attrs@[i as int]@);
        if let Some(AttributeExec::MaxAge(t)) = attrs.get(i) {
            acc = Some(*t);
        }
        // Never saturates: i < attrs.len().
        i = i.saturating_add(1);
    }
    assert(av.take(attrs.len() as int) =~= av);
    acc
}

/// [`last_expires`]: the attribute-value of the last Expires attribute.
pub fn last_expires_exec(attrs: &[AttributeExec]) -> (r: Option<u64>)
    ensures
        last_expires(crate::set_cookie::exec::attributes_view(attrs@)) == (match r {
            Some(t) => Some(t as int),
            None => None::<int>,
        }),
{
    let ghost av = crate::set_cookie::exec::attributes_view(attrs@);
    let mut acc: Option<u64> = None;
    let mut i: usize = 0;
    assert(av.take(0) =~= Seq::<crate::set_cookie::spec::Attribute>::empty());
    while i < attrs.len()
        invariant
            i <= attrs.len(),
            av == crate::set_cookie::exec::attributes_view(attrs@),
            last_expires(av.take(i as int)) == (match acc {
                Some(t) => Some(t as int),
                None => None::<int>,
            }),
        decreases attrs.len() - i,
    {
        let ghost t1 = av.take(i as int + 1);
        assert(t1.drop_last() =~= av.take(i as int));
        assert(t1.last() == av[i as int]);
        assert(av[i as int] == attrs@[i as int]@);
        if let Some(AttributeExec::Expires(t)) = attrs.get(i) {
            acc = Some(*t);
        }
        // Never saturates: i < attrs.len().
        i = i.saturating_add(1);
    }
    assert(av.take(attrs.len() as int) =~= av);
    acc
}

/// [`last_domain_within_1024`].
pub fn last_domain_within_1024_exec(attrs: &[AttributeExec]) -> (r: Option<Vec<u8>>)
    ensures
        last_domain_within_1024(crate::set_cookie::exec::attributes_view(attrs@)) == (match r {
            Some(d) => Some(d@),
            None => None::<Seq<u8>>,
        }),
{
    let ghost av = crate::set_cookie::exec::attributes_view(attrs@);
    let mut acc: Option<Vec<u8>> = None;
    let mut i: usize = 0;
    assert(av.take(0) =~= Seq::<crate::set_cookie::spec::Attribute>::empty());
    while i < attrs.len()
        invariant
            i <= attrs.len(),
            av == crate::set_cookie::exec::attributes_view(attrs@),
            last_domain_within_1024(av.take(i as int)) == (match acc {
                Some(d) => Some(d@),
                None => None::<Seq<u8>>,
            }),
        decreases attrs.len() - i,
    {
        let ghost t1 = av.take(i as int + 1);
        assert(t1.drop_last() =~= av.take(i as int));
        assert(t1.last() == av[i as int]);
        assert(av[i as int] == attrs@[i as int]@);
        match attrs.get(i) {
            Some(AttributeExec::Domain(d)) if d.len() <= 1024 => {
                acc = Some(copy(d.as_slice()));
            },
            _ => {},
        }
        // Never saturates: i < attrs.len().
        i = i.saturating_add(1);
    }
    assert(av.take(attrs.len() as int) =~= av);
    acc
}

/// [`last_path_within_1024`].
pub fn last_path_within_1024_exec(attrs: &[AttributeExec]) -> (r: Option<Vec<u8>>)
    ensures
        last_path_within_1024(crate::set_cookie::exec::attributes_view(attrs@)) == (match r {
            Some(p) => Some(p@),
            None => None::<Seq<u8>>,
        }),
{
    let ghost av = crate::set_cookie::exec::attributes_view(attrs@);
    let mut acc: Option<Vec<u8>> = None;
    let mut i: usize = 0;
    assert(av.take(0) =~= Seq::<crate::set_cookie::spec::Attribute>::empty());
    while i < attrs.len()
        invariant
            i <= attrs.len(),
            av == crate::set_cookie::exec::attributes_view(attrs@),
            last_path_within_1024(av.take(i as int)) == (match acc {
                Some(p) => Some(p@),
                None => None::<Seq<u8>>,
            }),
        decreases attrs.len() - i,
    {
        let ghost t1 = av.take(i as int + 1);
        assert(t1.drop_last() =~= av.take(i as int));
        assert(t1.last() == av[i as int]);
        assert(av[i as int] == attrs@[i as int]@);
        match attrs.get(i) {
            Some(AttributeExec::Path(p)) if p.len() <= 1024 => {
                acc = Some(copy(p.as_slice()));
            },
            _ => {},
        }
        // Never saturates: i < attrs.len().
        i = i.saturating_add(1);
    }
    assert(av.take(attrs.len() as int) =~= av);
    acc
}

/// [`last_same_site`].
pub fn last_same_site_exec(attrs: &[AttributeExec]) -> (r: Option<SameSite>)
    ensures
        last_same_site(crate::set_cookie::exec::attributes_view(attrs@)) == r,
{
    let ghost av = crate::set_cookie::exec::attributes_view(attrs@);
    let mut acc: Option<SameSite> = None;
    let mut i: usize = 0;
    assert(av.take(0) =~= Seq::<crate::set_cookie::spec::Attribute>::empty());
    while i < attrs.len()
        invariant
            i <= attrs.len(),
            av == crate::set_cookie::exec::attributes_view(attrs@),
            last_same_site(av.take(i as int)) == acc,
        decreases attrs.len() - i,
    {
        let ghost t1 = av.take(i as int + 1);
        assert(t1.drop_last() =~= av.take(i as int));
        assert(t1.last() == av[i as int]);
        assert(av[i as int] == attrs@[i as int]@);
        if let Some(AttributeExec::SameSite(e)) = attrs.get(i) {
            acc = Some(clone_same_site(e));
        }
        // Never saturates: i < attrs.len().
        i = i.saturating_add(1);
    }
    assert(av.take(attrs.len() as int) =~= av);
    acc
}

/// [`crate::set_cookie::spec::contains_secure_attribute`].
pub fn contains_secure_attribute_exec(attrs: &[AttributeExec]) -> (r: bool)
    ensures
        r == crate::set_cookie::spec::contains_secure_attribute(crate::set_cookie::exec::attributes_view(attrs@)),
{
    let ghost av = crate::set_cookie::exec::attributes_view(attrs@);
    let mut found = false;
    let mut i: usize = 0;
    while i < attrs.len()
        invariant
            i <= attrs.len(),
            av == crate::set_cookie::exec::attributes_view(attrs@),
            found == exists|j: int| 0 <= j < i as int && (#[trigger] av[j]) is Secure,
        decreases attrs.len() - i,
    {
        assert(av[i as int] == attrs@[i as int]@);
        if let Some(AttributeExec::Secure) = attrs.get(i) {
            found = true;
            assert(av[i as int] is Secure);
        }
        // Never saturates: i < attrs.len().
        i = i.saturating_add(1);
    }
    found
}

/// [`contains_http_only_attribute`].
pub fn contains_http_only_attribute_exec(attrs: &[AttributeExec]) -> (r: bool)
    ensures
        r == contains_http_only_attribute(crate::set_cookie::exec::attributes_view(attrs@)),
{
    let ghost av = crate::set_cookie::exec::attributes_view(attrs@);
    let mut found = false;
    let mut i: usize = 0;
    while i < attrs.len()
        invariant
            i <= attrs.len(),
            av == crate::set_cookie::exec::attributes_view(attrs@),
            found == exists|j: int| 0 <= j < i as int && (#[trigger] av[j]) is HttpOnly,
        decreases attrs.len() - i,
    {
        assert(av[i as int] == attrs@[i as int]@);
        if let Some(AttributeExec::HttpOnly) = attrs.get(i) {
            found = true;
            assert(av[i as int] is HttpOnly);
        }
        // Never saturates: i < attrs.len().
        i = i.saturating_add(1);
    }
    found
}

// ---------------------------------------------------------------------
// §5.7 steps 8 to 18 and the old-cookie.
// ---------------------------------------------------------------------

/// [`all_char_from`] from the start: every octet is in CHAR.
pub fn all_char_exec(s: &[u8]) -> (r: bool)
    ensures
        r == all_char_from(s@, 0),
{
    let mut i: usize = 0;
    while i < s.len()
        invariant
            i <= s.len(),
            all_char_from(s@, 0) == all_char_from(s@, i as nat),
        decreases s.len() - i,
    {
        let c = crate::strings::at(s, i).unwrap_or(0);
        if c >= 0x80 {
            assert(s@[i as int] >= 0x80);
            return false;
        }
        // Never saturates: i < s.len().
        i = i.saturating_add(1);
    }
    true
}

/// [`step_9_domain_attribute`] over the generated Public Suffix List.
pub fn step_9_exec(request_host_canonical: &CanonicalHostName, domain_attribute: &[u8]) -> (r: Option<Vec<u8>>)
    ensures
        step_9_domain_attribute(clazel_psl::table::psl_rules(), request_host_canonical@, domain_attribute@) == (match r {
            Some(d) => Some(d@),
            None => None::<Seq<u8>>,
        }),
{
    if is_public_suffix_string_exec(domain_attribute) {
        if slice_eq(domain_attribute, request_host_canonical.name.as_slice()) {
            let empty: Vec<u8> = Vec::new();
            Some(empty)
        } else {
            None
        }
    } else {
        Some(copy(domain_attribute))
    }
}

/// [`step_10_domain`].
pub fn step_10_exec(request_host_canonical: &CanonicalHostName, domain_attribute: &[u8]) -> (r: Option<(CanonicalHostName, bool)>)
    ensures
        step_10_domain(request_host_canonical@, domain_attribute@) == (match r {
            Some((d, b)) => Some((d@, b)),
            None => None::<(crate::matching::spec::CanonicalHost, bool)>,
        }),
{
    if !domain_attribute.is_empty() {
        if !domain_matches(
            request_host_canonical.name.as_slice(),
            !request_host_canonical.is_ip_address,
            domain_attribute,
        ) {
            None
        } else {
            Some((
                CanonicalHostName { name: copy(domain_attribute), is_ip_address: request_host_canonical.is_ip_address },
                false,
            ))
        }
    } else {
        Some((clone_host(request_host_canonical), true))
    }
}

/// [`secure_cookie_would_be_overlaid`] (step 16's criteria).
pub fn secure_cookie_would_be_overlaid_exec(jar: &[CookieRecord], name: &[u8], domain: &CanonicalHostName, path: &[u8]) -> (r: bool)
    ensures
        r == secure_cookie_would_be_overlaid(jar_view(jar@), name@, domain@, path@),
{
    let ghost jv = jar_view(jar@);
    let mut found = false;
    let mut i: usize = 0;
    while i < jar.len()
        invariant
            i <= jar.len(),
            jv == jar_view(jar@),
            found == exists|j: int|
                0 <= j < i as int && (#[trigger] jv[j]).name == name@ && jv[j].secure_only_flag && (canonical_domain_matches(
                    jv[j].domain,
                    domain@,
                ) || canonical_domain_matches(domain@, jv[j].domain)) && crate::matching::spec::path_matches(path@, jv[j].path),
        decreases jar.len() - i,
    {
        if let Some(c) = jar.get(i) {
            assert(jv[i as int] == c@);
            let m = slice_eq(c.name.as_slice(), name) && c.secure_only_flag && (canonical_domain_matches_exec(&c.domain, domain)
                || canonical_domain_matches_exec(domain, &c.domain)) && crate::matching::exec::path_matches(
                path,
                c.path.as_slice(),
            );
            if m {
                found = true;
            }
        }
        // Never saturates: i < jar.len().
        i = i.saturating_add(1);
    }
    found
}

/// [`step_18_continues`] over the generated Public Suffix List.
pub fn step_18_continues_exec(ctx: &RequestContextRecord) -> (r: bool)
    ensures
        r == step_18_continues(clazel_psl::table::psl_rules(), ctx@),
{
    let same_site = is_same_site_request_exec(ctx);
    if is_non_http_exec(ctx) && !same_site {
        false
    } else if same_site {
        true
    } else {
        match ctx {
            RequestContextRecord::Http(request) => request.navigates_top_level_traversable,
            RequestContextRecord::NonHttp(_) => false,
        }
    }
}

/// [`same_key`].
pub fn same_key_exec(a: &CookieRecord, b: &CookieRecord) -> (r: bool)
    ensures
        r == same_key(a@, b@),
{
    slice_eq(a.name.as_slice(), b.name.as_slice()) && hosts_equal(&a.domain, &b.domain) && a.host_only_flag == b.host_only_flag
        && slice_eq(a.path.as_slice(), b.path.as_slice())
}

/// [`find_old_cookie`]: the index of the first cookie with the same key.
pub fn find_old_cookie_exec(jar: &[CookieRecord], new: &CookieRecord) -> (r: Option<usize>)
    ensures
        find_old_cookie(jar_view(jar@), new@) == (match r {
            Some(i) => Some(i as int),
            None => None::<int>,
        }),
        r matches Some(i) ==> i < jar.len(),
{
    let ghost jv = jar_view(jar@);
    let mut i: usize = 0;
    while i < jar.len()
        invariant
            i <= jar.len(),
            jv == jar_view(jar@),
            find_old_cookie(jv, new@) == find_old_cookie_from(jv, new@, i as nat),
        decreases jar.len() - i,
    {
        if let Some(c) = jar.get(i) {
            assert(jv[i as int] == c@);
            if same_key_exec(c, new) {
                return Some(i);
            }
        }
        // Never saturates: i < jar.len().
        i = i.saturating_add(1);
    }
    None
}

/// The enforcement is "None".
pub fn same_site_is_none(s: &SameSite) -> (r: bool)
    ensures
        r == (*s == SameSite::None),
{
    matches!(s, SameSite::None)
}

/// The view of an optional cookie; `None` is "ignore the cookie entirely".
pub open spec fn cookie_option_view(c: Option<CookieRecord>) -> Option<Cookie> {
    match c {
        Some(c) => Some(c@),
        None => None,
    }
}

/// §5.7 steps 1 to 23.3: the newly-created cookie, if the cookie is not
/// ignored ([`create_a_cookie`] over the generated Public Suffix List).
pub fn create_a_cookie_exec(
    jar: &[CookieRecord],
    url: &RequestUrlRecord,
    ctx: &RequestContextRecord,
    received: &SetCookieRecord,
    now: u64,
) -> (r: Option<CookieRecord>)
    ensures
        create_a_cookie(clazel_psl::table::psl_rules(), jar_view(jar@), url@, ctx@, received@, now as int) == cookie_option_view(r),
{
    let ghost rules = clazel_psl::table::psl_rules();
    let attrs = received.attributes.as_slice();
    // 2.
    if received.name.is_empty() && received.value.is_empty() {
        return None;
    }
    // 3.
    if crate::set_cookie::exec::contains_ctl_exec(received.name.as_slice()) || crate::set_cookie::exec::contains_ctl_exec(
        received.value.as_slice(),
    ) {
        return None;
    }
    // 4.
    if received.name.len().saturating_add(received.value.len()) > 4096 {
        return None;
    }
    // 6.
    let (persistent_flag, expiry_time) = match last_max_age_exec(attrs) {
        Some(t) => (true, t),
        None => match last_expires_exec(attrs) {
            Some(t) => (true, t),
            None => (false, u64::MAX),
        },
    };
    // 7.
    let domain_attribute: Vec<u8> = match last_domain_within_1024_exec(attrs) {
        Some(d) => d,
        None => {
            let empty: Vec<u8> = Vec::new();
            empty
        },
    };
    proof {
        if last_domain_within_1024(received@.attributes) is None {
            assert(domain_attribute@ =~= Seq::<u8>::empty());
        }
    }
    // 8.
    if !all_char_exec(domain_attribute.as_slice()) {
        return None;
    }
    let host = match &url.host {
        None => {
            return None;
        },
        Some(h) => h,
    };
    // 9.
    let domain_attribute_9 = match step_9_exec(host, domain_attribute.as_slice()) {
        None => {
            return None;
        },
        Some(d) => d,
    };
    // 10.
    let (domain, host_only_flag) = match step_10_exec(host, domain_attribute_9.as_slice()) {
        None => {
            return None;
        },
        Some(x) => x,
    };
    // 11.
    let path: Vec<u8> = match last_path_within_1024_exec(attrs) {
        Some(p) => p,
        None => crate::matching::exec::default_path(url.path.as_slice()),
    };
    // 12.
    let secure_only_flag = contains_secure_attribute_exec(attrs);
    let secure_url = url_is_secure_exec(url);
    // 13.
    if !secure_url && secure_only_flag {
        return None;
    }
    // 14.
    let http_only_flag = contains_http_only_attribute_exec(attrs);
    let non_http = is_non_http_exec(ctx);
    // 15.
    if non_http && http_only_flag {
        return None;
    }
    // 16.
    if !secure_only_flag && !secure_url && secure_cookie_would_be_overlaid_exec(
        jar,
        received.name.as_slice(),
        &domain,
        path.as_slice(),
    ) {
        return None;
    }
    // 17.
    let same_site_flag = match last_same_site_exec(attrs) {
        Some(e) => e,
        None => SameSite::Default,
    };
    let same_site_none = same_site_is_none(&same_site_flag);
    // 18.
    if !same_site_none && !step_18_continues_exec(ctx) {
        return None;
    }
    // 19.
    if same_site_none && !secure_only_flag {
        return None;
    }
    // 20. to 22.
    if !crate::set_cookie::exec::name_prefix_requirements_met(received, secure_only_flag, host_only_flag) {
        return None;
    }
    let mut new = CookieRecord {
        name: copy(received.name.as_slice()),
        value: copy(received.value.as_slice()),
        expiry_time,
        domain,
        path,
        creation_time: now,
        last_access_time: now,
        persistent_flag,
        host_only_flag,
        secure_only_flag,
        http_only_flag,
        same_site_flag,
    };
    // 23.
    match find_old_cookie_exec(jar, &new) {
        None => Some(new),
        Some(i) => {
            let old_cookie = match jar.get(i) {
                Some(c) => c,
                None => {
                    return None;
                },
            };
            proof {
                assert(jar_view(jar@)[i as int] == old_cookie@);
            }
            // 23.2.
            if non_http && old_cookie.http_only_flag {
                None
            } else {
                // 23.3.
                new.creation_time = old_cookie.creation_time;
                proof {
                    assert(new@ == with_creation_time(Cookie { creation_time: now as int, ..new@ }, old_cookie.creation_time as int));
                }
                Some(new)
            }
        },
    }
}

// ---------------------------------------------------------------------
// Eviction, insertion and storage.
// ---------------------------------------------------------------------

/// Every cookie of an exec jar is in range, since its instants are `u64`.
pub proof fn lemma_jar_view_in_range(v: Seq<CookieRecord>)
    ensures
        super::contract::jar_in_range(jar_view(v)),
{
    assert forall|i: int| 0 <= i < jar_view(v).len() implies super::contract::cookie_in_range(#[trigger] jar_view(v)[i]) by {
        assert(jar_view(v)[i] == v[i]@);
    }
}

/// [`evict_expired`]: "The user agent MUST evict all expired cookies".
pub fn evict_expired_exec(jar: &[CookieRecord], now: u64) -> (out: Vec<CookieRecord>)
    ensures
        jar_view(out@) == evict_expired(jar_view(jar@), now as int),
{
    let ghost jv = jar_view(jar@);
    let mut out: Vec<CookieRecord> = Vec::new();
    let mut i: usize = 0;
    assert(jv.take(0) =~= Seq::<Cookie>::empty());
    reveal(Seq::filter);
    assert(Seq::<Cookie>::empty().filter(not_expired(now as int)) =~= Seq::<Cookie>::empty());
    while i < jar.len()
        invariant
            i <= jar.len(),
            jv == jar_view(jar@),
            jar_view(out@) == jv.take(i as int).filter(not_expired(now as int)),
        decreases jar.len() - i,
    {
        if let Some(c) = jar.get(i) {
            assert(jv[i as int] == c@);
            assert(jv.take(i as int + 1) =~= jv.take(i as int).push(c@));
            proof {
                super::lemmas::lemma_filter_push(jv.take(i as int), c@, not_expired(now as int));
            }
            if c.expiry_time >= now {
                let ghost before = jar_view(out@);
                out.push(clone_cookie(c));
                assert(jar_view(out@) =~= before.push(c@));
            }
        }
        // Never saturates: i < jar.len().
        i = i.saturating_add(1);
    }
    assert(jv.take(jar.len() as int) =~= jv);
    out
}

/// [`insert_a_cookie`]: steps 23.4 and 24.
pub fn insert_a_cookie_exec(jar: Vec<CookieRecord>, new: CookieRecord) -> (out: Vec<CookieRecord>)
    ensures
        jar_view(out@) == insert_a_cookie(jar_view(jar@), new@),
{
    let mut jar = jar;
    let ghost before = jar_view(jar@);
    if let Some(i) = find_old_cookie_exec(jar.as_slice(), &new) {
        let _removed = jar.remove(i);
        assert(jar_view(jar@) =~= before.remove(i as int));
    }
    let ghost mid = jar_view(jar@);
    jar.push(new);
    assert(jar_view(jar@) =~= mid.push(new@));
    jar
}

/// A jar of at most [`max_cookies_per_root`] cookies has no root over the
/// limit.
pub proof fn lemma_small_jar_within_limit(rules: Seq<clazel_psl::spec::Rule>, jar: Seq<Cookie>, root: crate::matching::spec::CanonicalHost)
    requires
        jar.len() <= max_cookies_per_root(),
    ensures
        evict_over_limit(rules, jar, root) == jar,
{
    jar.lemma_filter_len(in_root(rules, root));
}

/// [`evicted_before`].
pub fn evicted_before_exec(a: &CookieRecord, b: &CookieRecord) -> (r: bool)
    ensures
        r == evicted_before(a@, b@),
{
    let ca: u8 = if !a.secure_only_flag { 0 } else { 1 };
    let cb: u8 = if !b.secure_only_flag { 0 } else { 1 };
    ca < cb || (ca == cb && a.last_access_time < b.last_access_time)
}

/// [`evict_over_limit`] over the generated Public Suffix List: while the
/// cookie root `root` has more than 180 cookies, remove the one the
/// priority picks.
pub fn evict_over_limit_exec(jar: &mut Vec<CookieRecord>, root: &CanonicalHostName)
    ensures
        jar_view(final(jar)@) == evict_over_limit(clazel_psl::table::psl_rules(), jar_view(old(jar)@), root@),
{
    let ghost rules = clazel_psl::table::psl_rules();
    let ghost jv0 = jar_view(jar@);
    if jar.len() <= 180 {
        proof {
            lemma_small_jar_within_limit(rules, jv0, root@);
        }
        return;
    }
    loop
        invariant
            rules == clazel_psl::table::psl_rules(),
            jv0 == jar_view(old(jar)@),
            evict_over_limit(rules, jv0, root@) == evict_over_limit(rules, jar_view(jar@), root@),
        decreases jar.len(),
    {
        let ghost jv = jar_view(jar@);
        // How many cookies are under the root.
        let mut flags: Vec<bool> = Vec::new();
        let mut count: usize = 0;
        let mut i: usize = 0;
        assert(jv.take(0) =~= Seq::<Cookie>::empty());
        reveal(Seq::filter);
        assert(Seq::<Cookie>::empty().filter(in_root(rules, root@)) =~= Seq::<Cookie>::empty());
        while i < jar.len()
            invariant
                i <= jar.len(),
                jv == jar_view(jar@),
                rules == clazel_psl::table::psl_rules(),
                flags.len() == i,
                forall|k: int| 0 <= k < i ==> #[trigger] flags@[k] == (cookie_root_of(rules, jv[k]) == root@),
                count == jv.take(i as int).filter(in_root(rules, root@)).len(),
                count <= i,
            decreases jar.len() - i,
        {
            if let Some(c) = jar.get(i) {
                assert(jv[i as int] == c@);
                let r = cookie_root_exec(&c.domain);
                let f = hosts_equal(&r, root);
                assert(jv.take(i as int + 1) =~= jv.take(i as int).push(c@));
                proof {
                    super::lemmas::lemma_filter_push(jv.take(i as int), c@, in_root(rules, root@));
                }
                assert(f == (cookie_root_of(rules, jv[i as int]) == root@));
                flags.push(f);
                if f {
                    // Never saturates: count <= i < jar.len().
                    count = count.saturating_add(1);
                }
            }
            // Never saturates: i < jar.len().
            i = i.saturating_add(1);
        }
        assert(jv.take(jar.len() as int) =~= jv);
        assert(count == root_count(rules, jv, root@));
        if count <= 180 {
            proof {
                assert(root_count(rules, jv, root@) <= max_cookies_per_root());
                assert(evict_over_limit(rules, jv, root@) == jv);
                assert(jar_view(jar@) == jv);
                assert(evict_over_limit(rules, jv0, root@) == jv);
                assert(rules == clazel_psl::table::psl_rules());
            }
            return;
        }
        // The cookie to remove first.
        let mut best: Option<usize> = None;
        let mut j: usize = 0;
        while j < jar.len()
            invariant
                j <= jar.len(),
                jv == jar_view(jar@),
                rules == clazel_psl::table::psl_rules(),
                flags.len() == jar.len(),
                forall|k: int| 0 <= k < flags.len() ==> #[trigger] flags@[k] == (cookie_root_of(rules, jv[k]) == root@),
                victim_from(rules, jv, root@, j as nat) == (match best {
                    Some(b) => Some(b as int),
                    None => None::<int>,
                }),
                best matches Some(b) ==> b < j,
            decreases jar.len() - j,
        {
            if let (Some(c), Some(f)) = (jar.get(j), flags.get(j)) {
                assert(jv[j as int] == c@);
                if *f {
                    match best {
                        None => {
                            best = Some(j);
                        },
                        Some(b) => {
                            if let Some(cb) = jar.get(b) {
                                assert(jv[b as int] == cb@);
                                if evicted_before_exec(c, cb) {
                                    best = Some(j);
                                }
                            }
                        },
                    }
                }
            }
            // Never saturates: j < jar.len().
            j = j.saturating_add(1);
        }
        match best {
            Some(i) => {
                let _removed = jar.remove(i);
                proof {
                    assert(jar_view(jar@) =~= jv.remove(i as int));
                }
            },
            None => {
                // Unreachable: a root over the limit has a cookie to remove.
                proof {
                    super::isolation::lemma_filter_nonempty(jv, in_root(rules, root@));
                    super::isolation::lemma_victim_from_some(rules, jv, root@, jv.len());
                    assert(false);
                }
                return;
            },
        }
    }
}

/// §5.7 in full ([`store_a_cookie`]): the jar after the user agent
/// "receives a cookie" `received` from a request to `url` at time `now`.
pub fn store_a_cookie_exec(
    jar: &[CookieRecord],
    url: &RequestUrlRecord,
    ctx: &RequestContextRecord,
    received: &SetCookieRecord,
    now: u64,
) -> (out: Vec<CookieRecord>)
    requires
        super::contract::store_a_cookie_requires(jar_view(jar@), url@, ctx@, received@, now as int),
    ensures
        super::contract::store_a_cookie_ensures(jar_view(jar@), url@, ctx@, received@, now as int, jar_view(out@)),
{
    let live = evict_expired_exec(jar, now);
    let ghost live_view = jar_view(live@);
    match create_a_cookie_exec(live.as_slice(), url, ctx, received, now) {
        None => live,
        Some(new) => {
            let domain = clone_host(&new.domain);
            let ghost new_view = new@;
            let inserted = insert_a_cookie_exec(live, new);
            let mut evicted = evict_expired_exec(inserted.as_slice(), now);
            if evicted.len() <= 180 {
                proof {
                    lemma_small_jar_within_limit(clazel_psl::table::psl_rules(), jar_view(evicted@), cookie_root_of(clazel_psl::table::psl_rules(), new_view));
                }
                evicted
            } else {
                let root = cookie_root_exec(&domain);
                evict_over_limit_exec(&mut evicted, &root);
                evicted
            }
        },
    }
}

/// The jar after a Set-Cookie string is received ([`store_a_set_cookie_string`]):
/// §5.6's parse, then §5.7. This is `document.cookie`'s setter when `ctx` is
/// `NonHttp`.
pub fn store_a_set_cookie_string_exec(
    jar: &[CookieRecord],
    s: &[u8],
    url: &RequestUrlRecord,
    ctx: &RequestContextRecord,
    now: u64,
) -> (out: Vec<CookieRecord>)
    requires
        super::contract::store_a_set_cookie_string_requires(jar_view(jar@), s@, url@, ctx@, now as int),
    ensures
        super::contract::store_a_set_cookie_string_ensures(jar_view(jar@), s@, url@, ctx@, now as int, jar_view(out@)),
{
    match crate::set_cookie::exec::parse_a_set_cookie_string(s, url.path.as_slice(), now) {
        None => evict_expired_exec(jar, now),
        Some(received) => store_a_cookie_exec(jar, url, ctx, &received, now),
    }
}

// ---------------------------------------------------------------------
// §5.8 Retrieval.
// ---------------------------------------------------------------------

/// The predicate of §5.8.3 step 3 as a function of the cookie.
pub open spec fn retrieved_pred(
    rules: Seq<clazel_psl::spec::Rule>,
    url: RequestUrl,
    ctx: RequestContext,
    host: crate::matching::spec::CanonicalHost,
) -> spec_fn(Cookie) -> bool {
    |c: Cookie| cookie_is_retrieved(rules, url, ctx, host, c)
}

/// The cookie-list of a retrieval is the sorted filter by
/// [`retrieved_pred`].
pub proof fn lemma_retrieval_list_is_filter(
    rules: Seq<clazel_psl::spec::Rule>,
    jar: Seq<Cookie>,
    url: RequestUrl,
    ctx: RequestContext,
    host: crate::matching::spec::CanonicalHost,
)
    requires
        url.host == Some(host),
    ensures
        retrieval_cookie_list(rules, jar, url, ctx) == sort_cookie_list(jar.filter(retrieved_pred(rules, url, ctx, host))),
{
    assert((|c: Cookie| cookie_is_retrieved(rules, url, ctx, host, c)) =~= retrieved_pred(rules, url, ctx, host));
}

/// [`cookie_is_retrieved`] (§5.8.3 step 3) over the generated Public Suffix
/// List.
pub fn cookie_is_retrieved_exec(
    url: &RequestUrlRecord,
    ctx: &RequestContextRecord,
    host: &CanonicalHostName,
    c: &CookieRecord,
) -> (r: bool)
    ensures
        r == cookie_is_retrieved(clazel_psl::table::psl_rules(), url@, ctx@, host@, c@),
{
    let host_ok = if c.host_only_flag {
        hosts_equal(host, &c.domain)
    } else {
        canonical_domain_matches_exec(host, &c.domain) && !(!c.domain.is_ip_address && is_public_suffix_string_exec(
            c.domain.name.as_slice(),
        ))
    };
    if !host_ok {
        return false;
    }
    if !crate::matching::exec::path_matches(url.path.as_slice(), c.path.as_slice()) {
        return false;
    }
    if c.secure_only_flag && !url_is_secure_exec(url) {
        return false;
    }
    if c.http_only_flag && is_non_http_exec(ctx) {
        return false;
    }
    if same_site_is_none(&c.same_site_flag) {
        return true;
    }
    if is_same_site_request_exec(ctx) {
        return true;
    }
    match ctx {
        RequestContextRecord::Http(request) => {
            let lax_or_default = matches!(&c.same_site_flag, SameSite::Lax | SameSite::Default);
            lax_or_default && request.method_is_safe && request.target_is_active_or_top_level
        },
        RequestContextRecord::NonHttp(_) => false,
    }
}

/// [`cookie_listed_before`].
pub fn cookie_listed_before_exec(a: &CookieRecord, b: &CookieRecord) -> (r: bool)
    ensures
        r == cookie_listed_before(a@, b@),
{
    a.path.len() > b.path.len() || (a.path.len() == b.path.len() && a.creation_time < b.creation_time)
}

/// Inserting at the first position whose cookie `c` is listed before is
/// [`insert_sorted`].
pub proof fn lemma_insert_sorted_at(sorted: Seq<Cookie>, c: Cookie, j: int)
    requires
        0 <= j <= sorted.len(),
        forall|k: int| 0 <= k < j ==> !cookie_listed_before(c, #[trigger] sorted[k]),
        j == sorted.len() || cookie_listed_before(c, sorted[j]),
    ensures
        insert_sorted(sorted, c) == sorted.insert(j, c),
    decreases sorted.len(),
{
    if sorted.len() == 0 {
        assert(sorted.insert(0, c) =~= seq![c]);
    } else if cookie_listed_before(c, sorted[0]) {
        assert(j == 0);
        assert(sorted.insert(0, c) =~= seq![c] + sorted);
    } else {
        assert(j >= 1);
        let rest = sorted.skip(1);
        assert forall|k: int| 0 <= k < j - 1 implies !cookie_listed_before(c, #[trigger] rest[k]) by {
            assert(rest[k] == sorted[k + 1]);
        }
        if j < sorted.len() {
            assert(rest[j - 1] == sorted[j]);
        }
        lemma_insert_sorted_at(rest, c, j - 1);
        assert(sorted.insert(j, c) =~= seq![sorted[0]] + rest.insert(j - 1, c));
    }
}

/// [`insert_sorted`]: `c` inserted into the sorted list, after every cookie
/// not listed after it.
pub fn insert_sorted_exec(sorted: &mut Vec<CookieRecord>, c: CookieRecord)
    ensures
        jar_view(final(sorted)@) == insert_sorted(jar_view(old(sorted)@), c@),
{
    let ghost sv = jar_view(sorted@);
    let mut j: usize = 0;
    let mut found = false;
    while j < sorted.len() && !found
        invariant
            j <= sorted.len(),
            sv == jar_view(sorted@),
            forall|k: int| 0 <= k < j ==> !cookie_listed_before(c@, #[trigger] sv[k]),
            found ==> (j < sorted.len() && cookie_listed_before(c@, sv[j as int])),
        decreases sorted.len() - j, if found { 0int } else { 1int },
    {
        if let Some(s) = sorted.get(j) {
            assert(sv[j as int] == s@);
            if cookie_listed_before_exec(&c, s) {
                found = true;
            }
        }
        if !found {
            // Never saturates: j < sorted.len().
            j = j.saturating_add(1);
        }
    }
    proof {
        lemma_insert_sorted_at(sv, c@, j as int);
    }
    sorted.insert(j, c);
    proof {
        assert(jar_view(sorted@) =~= sv.insert(j as int, c@));
    }
}

/// [`sort_cookie_list`]: "The user agent SHOULD sort the cookie-list" (step
/// 4), stably.
pub fn sort_cookie_list_exec(list: &[CookieRecord]) -> (out: Vec<CookieRecord>)
    ensures
        jar_view(out@) == sort_cookie_list(jar_view(list@)),
{
    let ghost lv = jar_view(list@);
    let mut sorted: Vec<CookieRecord> = Vec::new();
    let mut i: usize = 0;
    assert(jar_view(sorted@) =~= Seq::<Cookie>::empty());
    while i < list.len()
        invariant
            i <= list.len(),
            lv == jar_view(list@),
            sort_from(lv, 0, seq![]) == sort_from(lv, i as nat, jar_view(sorted@)),
        decreases list.len() - i,
    {
        if let Some(c) = list.get(i) {
            assert(lv[i as int] == c@);
            let cc = clone_cookie(c);
            insert_sorted_exec(&mut sorted, cc);
        }
        // Never saturates: i < list.len().
        i = i.saturating_add(1);
    }
    sorted
}

/// The serialization of the first `k` cookies of `list`, with the
/// separators after each but the last cookie of the whole list.
pub open spec fn ser_part(list: Seq<Cookie>, i: nat) -> Seq<u8> {
    let cookie = list[i as int];
    let name_part: Seq<u8> = if cookie.name.len() > 0 {
        cookie.name + seq![0x3Du8]
    } else {
        seq![]
    };
    let separator: Seq<u8> = if i + 1 < list.len() {
        seq![0x3Bu8, 0x20]
    } else {
        seq![]
    };
    name_part + cookie.value + separator
}

/// See [`ser_part`].
pub open spec fn ser_prefix(list: Seq<Cookie>, k: nat) -> Seq<u8>
    decreases k,
{
    if k == 0 {
        seq![]
    } else {
        ser_prefix(list, (k - 1) as nat) + ser_part(list, (k - 1) as nat)
    }
}

/// The serialization is the prefix and the rest.
pub proof fn lemma_serialize_split(list: Seq<Cookie>, k: nat)
    requires
        k <= list.len(),
    ensures
        ser_prefix(list, k) + serialize_cookie_list_from(list, k) == serialize_cookie_list_from(list, 0),
    decreases k,
{
    if k > 0 {
        lemma_serialize_split(list, (k - 1) as nat);
        let i = (k - 1) as nat;
        assert(serialize_cookie_list_from(list, i) == ser_part(list, i) + serialize_cookie_list_from(list, k));
        assert(ser_prefix(list, k) + serialize_cookie_list_from(list, k) =~= ser_prefix(list, i) + serialize_cookie_list_from(list, i));
    }
}

/// Step 6 of §5.8.3: the cookie-string of `list`.
pub fn serialize_cookie_list_exec(list: &[CookieRecord]) -> (out: Vec<u8>)
    ensures
        out@ == serialize_cookie_list_from(jar_view(list@), 0),
{
    let ghost lv = jar_view(list@);
    let mut out: Vec<u8> = Vec::new();
    let mut i: usize = 0;
    assert(ser_prefix(lv, 0) =~= Seq::<u8>::empty());
    while i < list.len()
        invariant
            i <= list.len(),
            lv == jar_view(list@),
            out@ == ser_prefix(lv, i as nat),
        decreases list.len() - i,
    {
        if let Some(c) = list.get(i) {
            assert(lv[i as int] == c@);
            let ghost before = out@;
            // 6.1.
            if !c.name.is_empty() {
                crate::strings::append(&mut out, c.name.as_slice());
                out.push(0x3D);
            }
            // 6.2.
            crate::strings::append(&mut out, c.value.as_slice());
            // 6.3.
            if i.saturating_add(1) < list.len() {
                out.push(0x3B);
                out.push(0x20);
            }
            assert(out@ =~= before + ser_part(lv, i as nat));
        }
        // Never saturates: i < list.len().
        i = i.saturating_add(1);
    }
    proof {
        lemma_serialize_split(lv, lv.len());
    }
    assert(serialize_cookie_list_from(lv, lv.len()) == Seq::<u8>::empty());
    out
}

/// §5.8.3 ([`retrieve_cookie_string`] and [`jar_after_retrieval`]): the
/// cookie-string for a retrieval of `url` over `ctx` at time `now`, and the
/// jar after step 5. This is `document.cookie`'s getter when `ctx` is
/// `NonHttp`.
pub fn retrieve_a_cookie_string_exec(
    jar: &mut Vec<CookieRecord>,
    url: &RequestUrlRecord,
    ctx: &RequestContextRecord,
    now: u64,
) -> (output: Vec<u8>)
    requires
        super::contract::retrieve_a_cookie_string_requires(jar_view(old(jar)@), url@, ctx@, now as int),
    ensures
        super::contract::retrieve_a_cookie_string_ensures(
            jar_view(old(jar)@),
            url@,
            ctx@,
            now as int,
            jar_view(final(jar)@),
            output@,
        ),
{
    let ghost rules = clazel_psl::table::psl_rules();
    let live = evict_expired_exec(jar.as_slice(), now);
    let ghost lv = jar_view(live@);
    let host = match &url.host {
        None => {
            *jar = live;
            let empty: Vec<u8> = Vec::new();
            proof {
                assert(retrieval_cookie_list(rules, lv, url@, ctx@) == Seq::<Cookie>::empty());
                assert(serialize_cookie_list_from(Seq::<Cookie>::empty(), 0) == Seq::<u8>::empty());
            }
            return empty;
        },
        Some(h) => h,
    };
    proof {
        lemma_retrieval_list_is_filter(rules, lv, url@, ctx@, host@);
    }
    // 3. and 5.
    let mut list: Vec<CookieRecord> = Vec::new();
    let mut updated: Vec<CookieRecord> = Vec::new();
    let ghost p = retrieved_pred(rules, url@, ctx@, host@);
    let ghost f = update_last_access_time(rules, url@, ctx@, host@, now as int);
    let mut i: usize = 0;
    proof {
        assert(lv.take(0) =~= Seq::<Cookie>::empty());
        reveal(Seq::filter);
        assert(Seq::<Cookie>::empty().filter(p) =~= Seq::<Cookie>::empty());
        assert(jar_view(list@) =~= Seq::<Cookie>::empty());
        assert(jar_view(updated@) =~= Seq::<Cookie>::empty());
        assert(Seq::<Cookie>::empty().map_values(f) =~= Seq::<Cookie>::empty());
    }
    while i < live.len()
        invariant
            i <= live.len(),
            lv == jar_view(live@),
            rules == clazel_psl::table::psl_rules(),
            p == retrieved_pred(rules, url@, ctx@, host@),
            f == update_last_access_time(rules, url@, ctx@, host@, now as int),
            jar_view(list@) == lv.take(i as int).filter(p),
            jar_view(updated@) == lv.take(i as int).map_values(f),
        decreases live.len() - i,
    {
        if let Some(c) = live.get(i) {
            assert(lv[i as int] == c@);
            let retrieved = cookie_is_retrieved_exec(url, ctx, host, c);
            proof {
                assert(lv.take(i as int + 1) =~= lv.take(i as int).push(c@));
                super::lemmas::lemma_filter_push(lv.take(i as int), c@, p);
                assert(lv.take(i as int + 1).map_values(f) =~= lv.take(i as int).map_values(f).push(f(c@)));
            }
            let mut copy_of = clone_cookie(c);
            if retrieved {
                list.push(clone_cookie(c));
                copy_of.last_access_time = now;
                proof {
                    assert(f(c@) == with_last_access_time(c@, now as int));
                    assert(copy_of@ =~= with_last_access_time(c@, now as int));
                }
            } else {
                proof {
                    assert(f(c@) == c@);
                }
            }
            let ghost before_list = jar_view(list@);
            let ghost before_updated = jar_view(updated@);
            updated.push(copy_of);
            proof {
                assert(jar_view(updated@) =~= before_updated.push(f(c@)));
                if retrieved {
                    assert(jar_view(list@) =~= jar_view(list@));
                }
            }
        }
        // Never saturates: i < live.len().
        i = i.saturating_add(1);
    }
    proof {
        assert(lv.take(live.len() as int) =~= lv);
    }
    // 4.
    let sorted = sort_cookie_list_exec(list.as_slice());
    let output = serialize_cookie_list_exec(sorted.as_slice());
    *jar = updated;
    output
}

} // verus!
