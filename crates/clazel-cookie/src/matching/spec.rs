//! RFC 6265bis §5.1.2 to §5.1.4: canonicalized host names, domain
//! matching, default-path and path-match, transcribed. Nothing here runs;
//! it defines what "correct" means. Each `// N.` comment is the step
//! number in the cited algorithm.
//!
//! Source (pinned; a review is against exactly this text):
//! - draft-ietf-httpbis-rfc6265bis-22, "Cookies: HTTP State Management
//!   Mechanism", 1 December 2025 (the latest revision on 21 October 2026;
//!   it has not been published as an RFC),
//!   <https://www.ietf.org/archive/id/draft-ietf-httpbis-rfc6265bis-22.txt>:
//!   §5.1.2 Canonicalized Host Names, §5.1.3 Domain Matching, §5.1.4 Paths
//!   and Path-Match.
//!
//! Modelling choices (each one a deliberate deviation in form, never in
//! meaning):
//! - **Canonicalization is the URL Standard's host parser and serializer.**
//!   §5.1.2 describes label checks and a U-label to A-label conversion (RFC
//!   5890, IDNA2008). Browsers do not run bare IDNA2008 on a host: the
//!   request-host is a URL's host, which the URL Standard's host parser has
//!   already turned into a domain (UTS #46 ToASCII with the URL Standard's
//!   flags), an IPv4 or IPv6 address, an opaque host or the empty host.
//!   [`canonicalize_a_host_name`] takes that host record. A domain
//!   canonicalizes to itself, an IP address to its serialization (flagged,
//!   so that §5.1.3's "the string is a host name (i.e., not an IP address)"
//!   can be decided), and an opaque or empty host fails: opaque hosts only
//!   arise from URLs of non-special schemes, which are never sent cookies.
//!   A domain is ASCII (URL §3.1), so each code point narrows to one
//!   octet; the narrowing is checked rather than assumed.
//!   [`canonicalize_a_host_name_string`] composes the host parser on a
//!   host string. This differs from the draft's letter in what an
//!   accepted label is (for instance, UTS #46 with UseSTD3ASCIIRules false
//!   accepts underscores, as every browser does).
//! - A string is a `Seq<u8>` of octets (see [`crate::ascii`]). The request
//!   path is the URL's path serialized (URL §4.5): ASCII, because the
//!   path percent-encode set covers every non-ASCII code point, so a
//!   sequence of octets is the sequence of code points.
//! - §5.1.3 "The string is a host name (i.e., not an IP address)" is the
//!   argument `string_is_host_name`; the caller decides it from the
//!   [`CanonicalHost`] it holds.
//! - §5.1.4 "the path portion of the request-uri if such a portion exists
//!   (and empty otherwise)" is the argument `uri_path`: a URL always has a
//!   path (possibly empty for non-special schemes), so the caller passes
//!   it directly.

#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------
// §5.1.2 Canonicalized host names.
// ---------------------------------------------------------------------

/// A canonicalized host name, with whether it is an IP address.
pub struct CanonicalHost {
    /// The canonicalized host name: the domain, or the IP address
    /// serialization.
    pub name: Seq<u8>,
    /// The host is an IPv4 or IPv6 address, not a host name.
    pub is_ip_address: bool,
}

/// Every code point is ASCII.
pub open spec fn all_ascii(s: Seq<u32>) -> bool {
    forall|i: int| 0 <= i < s.len() ==> #[trigger] s[i] < 0x80
}

/// The octets of an ASCII string of code points.
pub open spec fn narrow(s: Seq<u32>) -> Seq<u8> {
    s.map_values(|c: u32| c as u8)
}

/// §5.1.2 "canonicalized host name" of a host record (the URL Standard's
/// result of host parsing); `None` is failure. See the modelling choices.
pub open spec fn canonicalize_a_host_name(host: Option<clazel_url::host::spec::Host>) -> Option<CanonicalHost> {
    match host {
        Some(clazel_url::host::spec::Host::Domain(domain)) => if all_ascii(domain) {
            Some(CanonicalHost { name: narrow(domain), is_ip_address: false })
        } else {
            None
        },
        Some(clazel_url::host::spec::Host::Ipv4(address)) => {
            let text = clazel_url::host::spec::host_serializer(clazel_url::host::spec::Host::Ipv4(address));
            if all_ascii(text) { Some(CanonicalHost { name: narrow(text), is_ip_address: true }) } else { None }
        },
        Some(clazel_url::host::spec::Host::Ipv6(address)) => {
            let text = clazel_url::host::spec::host_serializer(clazel_url::host::spec::Host::Ipv6(address));
            if all_ascii(text) { Some(CanonicalHost { name: narrow(text), is_ip_address: true }) } else { None }
        },
        Some(clazel_url::host::spec::Host::Opaque(_)) => None,
        Some(clazel_url::host::spec::Host::Empty) => None,
        None => None,
    }
}

/// §5.1.2 on a host string: the URL Standard's host parser (not opaque,
/// with the URL domain parser), then [`canonicalize_a_host_name`].
pub open spec fn canonicalize_a_host_name_string(host: Seq<u32>) -> Option<CanonicalHost> {
    canonicalize_a_host_name(
        clazel_url::host::spec::host_parser(host, false, clazel_url::host::contract::url_domain_parser()),
    )
}

// ---------------------------------------------------------------------
// §5.1.3 Domain matching.
// ---------------------------------------------------------------------

/// §5.1.3: "A string domain-matches a given domain string if at least one
/// of the following conditions hold". Both inputs are canonicalized.
pub open spec fn domain_matches(string: Seq<u8>, string_is_host_name: bool, domain: Seq<u8>) -> bool {
    // "The domain string and the string are identical."
    string == domain
    // "All of the following conditions hold:"
    || (
        // "The domain string is a suffix of the string."
        domain.is_suffix_of(string)
        // "The last character of the string that is not included in the
        // domain string is a %x2E (".") character."
        && string.len() > domain.len()
        && string[string.len() - domain.len() - 1] == 0x2E
        // "The string is a host name (i.e., not an IP address)."
        && string_is_host_name
    )
}

// ---------------------------------------------------------------------
// §5.1.4 Paths and path-match.
// ---------------------------------------------------------------------

/// The number of %x2F ("/") characters of `s`.
pub open spec fn slash_count(s: Seq<u8>) -> nat
    decreases s.len()
{
    if s.len() == 0 { 0 } else { slash_count(s.drop_last()) + if s[s.len() - 1] == 0x2F { 1nat } else { 0nat } }
}

/// The index of the right-most %x2F ("/") of `s`, or -1 if there is none.
pub open spec fn rightmost_slash(s: Seq<u8>) -> int
    decreases s.len()
{
    if s.len() == 0 { -1 } else if s[s.len() - 1] == 0x2F { s.len() - 1 } else { rightmost_slash(s.drop_last()) }
}

/// §5.1.4 "default-path" of a cookie, from `uri_path`.
pub open spec fn default_path(uri_path: Seq<u8>) -> Seq<u8> {
    // 1. "Let uri-path be the path portion of the request-uri if such a
    //    portion exists (and empty otherwise)." (The argument.)
    // 2. "If the uri-path is empty or if the first character of the
    //    uri-path is not a %x2F ("/") character, output %x2F ("/") and
    //    skip the remaining steps."
    if uri_path.len() == 0 || uri_path[0] != 0x2F {
        seq![0x2Fu8]
    // 3. "If the uri-path contains no more than one %x2F ("/") character,
    //    output %x2F ("/") and skip the remaining step."
    } else if slash_count(uri_path) <= 1 {
        seq![0x2Fu8]
    } else {
        // 4. "Output the characters of the uri-path from the first
        //    character up to, but not including, the right-most %x2F ("/")."
        uri_path.take(rightmost_slash(uri_path))
    }
}

/// §5.1.4: "A request-path path-matches a given cookie-path if at least
/// one of the following conditions holds".
pub open spec fn path_matches(request_path: Seq<u8>, cookie_path: Seq<u8>) -> bool {
    // "The cookie-path and the request-path are identical."
    cookie_path == request_path
    // "The cookie-path is a prefix of the request-path, and the last
    // character of the cookie-path is %x2F ("/")."
    || (cookie_path.is_prefix_of(request_path) && cookie_path.len() > 0 && cookie_path[cookie_path.len() - 1] == 0x2F)
    // "The cookie-path is a prefix of the request-path, and the first
    // character of the request-path that is not included in the
    // cookie-path is a %x2F ("/") character."
    || (cookie_path.is_prefix_of(request_path) && request_path.len() > cookie_path.len()
        && request_path[cookie_path.len() as int] == 0x2F)
}

} // verus!
