//! Examples evaluated on the spec: Verus computes the spec on concrete
//! origins, sites and URL records, so a transcription error shows up here
//! as a failed proof. Sites use the small Public Suffix List of
//! `clazel_psl::examples` (`com`, `uk`, `co.uk`, `*.ck`, `!www.ck`). They
//! also serve as the certificates of `mutations.json`.
//!
//! The blob case of URL §4.7 is evaluated from step 3, on a URL record
//! given directly ([`url_origin_of_blob_path_url`]): steps 1 and 2 need
//! Verus to evaluate `all_scalar_values` (a quantifier) and the basic URL
//! parser, which `tests/conformance_origin.rs` runs through the real parser.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The domain host with these labels.
pub open spec fn host_of(labels: Seq<Seq<u32>>) -> clazel_url::host::spec::Host {
    clazel_url::host::spec::Host::Domain(clazel_psl::examples::dom(labels))
}

/// `www.a.com`.
pub open spec fn www_a_com() -> clazel_url::host::spec::Host {
    host_of(seq![clazel_psl::examples::l_www(), clazel_psl::examples::l_a(), clazel_psl::examples::l_com()])
}

/// `b.a.com`.
pub open spec fn b_a_com() -> clazel_url::host::spec::Host {
    host_of(seq![clazel_psl::examples::l_b(), clazel_psl::examples::l_a(), clazel_psl::examples::l_com()])
}

/// `a.com`.
pub open spec fn a_com() -> clazel_url::host::spec::Host {
    host_of(seq![clazel_psl::examples::l_a(), clazel_psl::examples::l_com()])
}

/// `b.com`.
pub open spec fn b_com() -> clazel_url::host::spec::Host {
    host_of(seq![clazel_psl::examples::l_b(), clazel_psl::examples::l_com()])
}

/// `com`.
pub open spec fn com() -> clazel_url::host::spec::Host {
    host_of(seq![clazel_psl::examples::l_com()])
}

/// `uk`.
pub open spec fn uk() -> clazel_url::host::spec::Host {
    host_of(seq![clazel_psl::examples::l_uk()])
}

/// `x.co.uk`.
pub open spec fn x_co_uk() -> clazel_url::host::spec::Host {
    host_of(seq![seq![0x78u32], clazel_psl::examples::l_co(), clazel_psl::examples::l_uk()])
}

/// `y.co.uk`.
pub open spec fn y_co_uk() -> clazel_url::host::spec::Host {
    host_of(seq![seq![0x79u32], clazel_psl::examples::l_co(), clazel_psl::examples::l_uk()])
}

/// The tuple origin `(scheme, host, port, null)`.
pub open spec fn tup(scheme: Seq<u32>, host: clazel_url::host::spec::Host, port: Option<nat>) -> Origin {
    tuple_origin(scheme, host, port)
}

/// The same with a domain.
pub open spec fn tup_domain(scheme: Seq<u32>, host: clazel_url::host::spec::Host, domain: clazel_url::host::spec::Host) -> Origin {
    Origin::Tuple { scheme, host, port: None, domain: Some(domain) }
}

/// A URL record with these components (and no credentials, query or
/// fragment).
pub open spec fn url_of(scheme: Seq<u32>, host: Option<clazel_url::host::spec::Host>, port: Option<nat>) -> clazel_url::url::spec::Url {
    clazel_url::url::spec::Url {
        scheme,
        username: seq![],
        password: seq![],
        host,
        port,
        path: clazel_url::url::spec::UrlPath::List(seq![]),
        query: None,
        fragment: None,
    }
}

/// The scheme `https`.
pub open spec fn https() -> Seq<u32> {
    clazel_url::url::spec::https_str()
}

/// The scheme `http`.
pub open spec fn http() -> Seq<u32> {
    clazel_url::url::spec::http_str()
}

// ---------------------------------------------------------------------
// HTML §7.1.1: origins.
// ---------------------------------------------------------------------

/// Same origin compares scheme, host and port, and nothing else.
pub proof fn example_same_origin()
    ensures
        same_origin(tup(https(), a_com(), None), tup(https(), a_com(), None)),
        !same_origin(tup(https(), a_com(), None), tup(http(), a_com(), None)),
        !same_origin(tup(https(), a_com(), None), tup(https(), a_com(), Some(8080nat))),
        !same_origin(tup(https(), a_com(), None), tup(https(), b_com(), None)),
        !same_origin(tup(https(), a_com(), Some(80nat)), tup(https(), a_com(), Some(81nat))),
        // The domain does not matter.
        same_origin(tup(https(), a_com(), None), tup_domain(https(), a_com(), com())),
{
    assert(same_origin(tup(https(), a_com(), None), tup(https(), a_com(), None))) by (compute_only);
    assert(!same_origin(tup(https(), a_com(), None), tup(http(), a_com(), None))) by (compute_only);
    assert(!same_origin(tup(https(), a_com(), None), tup(https(), a_com(), Some(8080nat)))) by (compute_only);
    assert(!same_origin(tup(https(), a_com(), None), tup(https(), b_com(), None))) by (compute_only);
    assert(!same_origin(tup(https(), a_com(), Some(80nat)), tup(https(), a_com(), Some(81nat)))) by (compute_only);
    assert(same_origin(tup(https(), a_com(), None), tup_domain(https(), a_com(), com()))) by (compute_only);
}

/// Opaque origins are the same exactly when they are the same opaque
/// origin, and never the same as a tuple origin.
pub proof fn example_same_origin_opaque()
    ensures
        same_origin(Origin::Opaque(1nat), Origin::Opaque(1nat)),
        !same_origin(Origin::Opaque(1nat), Origin::Opaque(2nat)),
        !same_origin(Origin::Opaque(1nat), tup(https(), a_com(), None)),
        !same_origin(tup(https(), a_com(), None), Origin::Opaque(1nat)),
{
    assert(same_origin(Origin::Opaque(1nat), Origin::Opaque(1nat))) by (compute_only);
    assert(!same_origin(Origin::Opaque(1nat), Origin::Opaque(2nat))) by (compute_only);
    assert(!same_origin(Origin::Opaque(1nat), tup(https(), a_com(), None))) by (compute_only);
    assert(!same_origin(tup(https(), a_com(), None), Origin::Opaque(1nat))) by (compute_only);
}

/// Same origin-domain: equal non-null domains with the same scheme are the
/// same origin-domain whatever the hosts (2.1); null domains need the same
/// origin (2.2); a domain on one side only never matches.
pub proof fn example_same_origin_domain()
    ensures
        // 2.1: both set `document.domain` to `a.com`.
        same_origin_domain(tup_domain(https(), www_a_com(), a_com()), tup_domain(https(), b_a_com(), a_com())),
        // 2.1 needs the same scheme.
        !same_origin_domain(tup_domain(https(), www_a_com(), a_com()), tup_domain(http(), b_a_com(), a_com())),
        // 2.1 needs equal domains.
        !same_origin_domain(tup_domain(https(), www_a_com(), a_com()), tup_domain(https(), b_a_com(), com())),
        // 2.2: null domains, different hosts.
        !same_origin_domain(tup(https(), www_a_com(), None), tup(https(), b_a_com(), None)),
        // 2.2: null domains, same origin.
        same_origin_domain(tup(https(), www_a_com(), None), tup(https(), www_a_com(), None)),
        // A domain on one side only: not the same origin-domain, although
        // they are the same origin.
        !same_origin_domain(tup(https(), www_a_com(), None), tup_domain(https(), www_a_com(), a_com())),
        same_origin_domain(Origin::Opaque(1nat), Origin::Opaque(1nat)),
        !same_origin_domain(Origin::Opaque(1nat), Origin::Opaque(2nat)),
        !same_origin_domain(Origin::Opaque(1nat), tup(https(), a_com(), None)),
{
    assert(same_origin_domain(tup_domain(https(), www_a_com(), a_com()), tup_domain(https(), b_a_com(), a_com()))) by (compute_only);
    assert(!same_origin_domain(tup_domain(https(), www_a_com(), a_com()), tup_domain(http(), b_a_com(), a_com()))) by (compute_only);
    assert(!same_origin_domain(tup_domain(https(), www_a_com(), a_com()), tup_domain(https(), b_a_com(), com()))) by (compute_only);
    assert(!same_origin_domain(tup(https(), www_a_com(), None), tup(https(), b_a_com(), None))) by (compute_only);
    assert(same_origin_domain(tup(https(), www_a_com(), None), tup(https(), www_a_com(), None))) by (compute_only);
    assert(!same_origin_domain(tup(https(), www_a_com(), None), tup_domain(https(), www_a_com(), a_com()))) by (compute_only);
    assert(same_origin_domain(Origin::Opaque(1nat), Origin::Opaque(1nat))) by (compute_only);
    assert(!same_origin_domain(Origin::Opaque(1nat), Origin::Opaque(2nat))) by (compute_only);
    assert(!same_origin_domain(Origin::Opaque(1nat), tup(https(), a_com(), None))) by (compute_only);
}

/// The effective domain is the domain if set, else the host; null for an
/// opaque origin.
pub proof fn example_effective_domain()
    ensures
        effective_domain(tup(https(), www_a_com(), None)) == Some(www_a_com()),
        effective_domain(tup_domain(https(), www_a_com(), a_com())) == Some(a_com()),
        effective_domain(Origin::Opaque(1nat)) is None,
        // The two hosts differ (for the proofs that use them).
        a_com() != www_a_com(),
{
    assert(effective_domain(tup(https(), www_a_com(), None)) == Some(www_a_com())) by (compute_only);
    assert(effective_domain(tup_domain(https(), www_a_com(), a_com())) == Some(a_com())) by (compute_only);
    assert(effective_domain(Origin::Opaque(1nat)) is None) by (compute_only);
    assert(a_com() != www_a_com()) by (compute_only);
}

/// Serialization: `scheme://host[:port]`, and "null" for an opaque origin.
pub proof fn example_serialization_of_origin()
    ensures
        serialization_of_origin(tup(https(), a_com(), None)) == seq![0x68u32, 0x74, 0x74, 0x70, 0x73, 0x3A, 0x2F, 0x2F, 0x61, 0x2E, 0x63, 0x6F, 0x6D],
        serialization_of_origin(tup(https(), a_com(), Some(8080nat))) == seq![0x68u32, 0x74, 0x74, 0x70, 0x73, 0x3A, 0x2F, 0x2F, 0x61, 0x2E, 0x63, 0x6F, 0x6D, 0x3A, 0x38, 0x30, 0x38, 0x30],
        serialization_of_origin(Origin::Opaque(1nat)) == seq![0x6Eu32, 0x75, 0x6C, 0x6C],
        serialization_of_origin(Origin::Opaque(2nat)) == seq![0x6Eu32, 0x75, 0x6C, 0x6C],
        // The two serializations differ (for the proofs that use them).
        seq![0x68u32, 0x74, 0x74, 0x70, 0x73, 0x3A, 0x2F, 0x2F, 0x61, 0x2E, 0x63, 0x6F, 0x6D] != seq![0x68u32, 0x74, 0x74, 0x70, 0x73, 0x3A, 0x2F, 0x2F, 0x61, 0x2E, 0x63, 0x6F, 0x6D, 0x3A, 0x38, 0x30, 0x38, 0x30],
{
    assert(serialization_of_origin(tup(https(), a_com(), None)) == seq![0x68u32, 0x74, 0x74, 0x70, 0x73, 0x3A, 0x2F, 0x2F, 0x61, 0x2E, 0x63, 0x6F, 0x6D]) by (compute_only);
    assert(serialization_of_origin(tup(https(), a_com(), Some(8080nat))) == seq![0x68u32, 0x74, 0x74, 0x70, 0x73, 0x3A, 0x2F, 0x2F, 0x61, 0x2E, 0x63, 0x6F, 0x6D, 0x3A, 0x38, 0x30, 0x38, 0x30]) by (compute_only);
    assert(serialization_of_origin(Origin::Opaque(1nat)) == seq![0x6Eu32, 0x75, 0x6C, 0x6C]) by (compute_only);
    assert(serialization_of_origin(Origin::Opaque(2nat)) == seq![0x6Eu32, 0x75, 0x6C, 0x6C]) by (compute_only);
    assert(seq![0x68u32, 0x74, 0x74, 0x70, 0x73, 0x3A, 0x2F, 0x2F, 0x61, 0x2E, 0x63, 0x6F, 0x6D] != seq![0x68u32, 0x74, 0x74, 0x70, 0x73, 0x3A, 0x2F, 0x2F, 0x61, 0x2E, 0x63, 0x6F, 0x6D, 0x3A, 0x38, 0x30, 0x38, 0x30]) by (compute_only);
}

// ---------------------------------------------------------------------
// HTML §7.1.1.1: sites.
// ---------------------------------------------------------------------

/// A site is the scheme and the registrable domain; a host with none is
/// its own; an opaque origin is its own.
pub proof fn example_obtain_a_site()
    ensures
        obtain_a_site(clazel_psl::examples::rules(), tup(https(), www_a_com(), Some(8080nat))) == Site::SchemeAndHost(https(), a_com()),
        obtain_a_site(clazel_psl::examples::rules(), tup(http(), x_co_uk(), None)) == Site::SchemeAndHost(http(), x_co_uk()),
        obtain_a_site(clazel_psl::examples::rules(), tup(https(), com(), None)) == Site::SchemeAndHost(https(), com()),
        obtain_a_site(clazel_psl::examples::rules(), tup(https(), clazel_url::host::spec::Host::Ipv4(1), None)) == Site::SchemeAndHost(https(), clazel_url::host::spec::Host::Ipv4(1)),
        obtain_a_site(clazel_psl::examples::rules(), Origin::Opaque(3nat)) == Site::Opaque(3nat),
{
    assert(obtain_a_site(clazel_psl::examples::rules(), tup(https(), www_a_com(), Some(8080nat))) == Site::SchemeAndHost(https(), a_com())) by (compute_only);
    assert(obtain_a_site(clazel_psl::examples::rules(), tup(http(), x_co_uk(), None)) == Site::SchemeAndHost(http(), x_co_uk())) by (compute_only);
    assert(obtain_a_site(clazel_psl::examples::rules(), tup(https(), com(), None)) == Site::SchemeAndHost(https(), com())) by (compute_only);
    assert(obtain_a_site(clazel_psl::examples::rules(), tup(https(), clazel_url::host::spec::Host::Ipv4(1), None)) == Site::SchemeAndHost(https(), clazel_url::host::spec::Host::Ipv4(1))) by (compute_only);
    assert(obtain_a_site(clazel_psl::examples::rules(), Origin::Opaque(3nat)) == Site::Opaque(3nat)) by (compute_only);
}

/// Same site: same scheme and registrable domain, ports ignored; different
/// schemes are not the same site; sites below a public suffix are not the
/// same site as their siblings.
pub proof fn example_same_site()
    ensures
        same_site(clazel_psl::examples::rules(), tup(https(), www_a_com(), None), tup(https(), b_a_com(), Some(8080nat))),
        !same_site(clazel_psl::examples::rules(), tup(https(), www_a_com(), None), tup(http(), b_a_com(), None)),
        !same_site(clazel_psl::examples::rules(), tup(https(), a_com(), None), tup(https(), b_com(), None)),
        !same_site(clazel_psl::examples::rules(), tup(https(), x_co_uk(), None), tup(https(), y_co_uk(), None)),
        same_site(clazel_psl::examples::rules(), tup(https(), x_co_uk(), None), tup(https(), x_co_uk(), None)),
        same_site(clazel_psl::examples::rules(), Origin::Opaque(1nat), Origin::Opaque(1nat)),
        !same_site(clazel_psl::examples::rules(), Origin::Opaque(1nat), Origin::Opaque(2nat)),
        !same_site(clazel_psl::examples::rules(), Origin::Opaque(1nat), tup(https(), a_com(), None)),
        !same_site(clazel_psl::examples::rules(), tup(https(), a_com(), None), Origin::Opaque(1nat)),
{
    assert(same_site(clazel_psl::examples::rules(), tup(https(), www_a_com(), None), tup(https(), b_a_com(), Some(8080nat)))) by (compute_only);
    assert(!same_site(clazel_psl::examples::rules(), tup(https(), www_a_com(), None), tup(http(), b_a_com(), None))) by (compute_only);
    assert(!same_site(clazel_psl::examples::rules(), tup(https(), a_com(), None), tup(https(), b_com(), None))) by (compute_only);
    assert(!same_site(clazel_psl::examples::rules(), tup(https(), x_co_uk(), None), tup(https(), y_co_uk(), None))) by (compute_only);
    assert(same_site(clazel_psl::examples::rules(), tup(https(), x_co_uk(), None), tup(https(), x_co_uk(), None))) by (compute_only);
    assert(same_site(clazel_psl::examples::rules(), Origin::Opaque(1nat), Origin::Opaque(1nat))) by (compute_only);
    assert(!same_site(clazel_psl::examples::rules(), Origin::Opaque(1nat), Origin::Opaque(2nat))) by (compute_only);
    assert(!same_site(clazel_psl::examples::rules(), Origin::Opaque(1nat), tup(https(), a_com(), None))) by (compute_only);
    assert(!same_site(clazel_psl::examples::rules(), tup(https(), a_com(), None), Origin::Opaque(1nat))) by (compute_only);
}

/// Schemelessly same site: the scheme does not matter; two hosts that have
/// no registrable domain are the same only when equal.
pub proof fn example_schemelessly_same_site()
    ensures
        schemelessly_same_site(clazel_psl::examples::rules(), tup(https(), www_a_com(), None), tup(http(), b_a_com(), None)),
        !schemelessly_same_site(clazel_psl::examples::rules(), tup(https(), a_com(), None), tup(https(), b_com(), None)),
        !schemelessly_same_site(clazel_psl::examples::rules(), tup(https(), com(), None), tup(https(), uk(), None)),
        schemelessly_same_site(clazel_psl::examples::rules(), tup(https(), com(), None), tup(http(), com(), None)),
        !schemelessly_same_site(clazel_psl::examples::rules(), tup(https(), x_co_uk(), None), tup(https(), y_co_uk(), None)),
        schemelessly_same_site(clazel_psl::examples::rules(), Origin::Opaque(1nat), Origin::Opaque(1nat)),
        !schemelessly_same_site(clazel_psl::examples::rules(), Origin::Opaque(1nat), Origin::Opaque(2nat)),
        !schemelessly_same_site(clazel_psl::examples::rules(), Origin::Opaque(1nat), tup(https(), a_com(), None)),
{
    assert(schemelessly_same_site(clazel_psl::examples::rules(), tup(https(), www_a_com(), None), tup(http(), b_a_com(), None))) by (compute_only);
    assert(!schemelessly_same_site(clazel_psl::examples::rules(), tup(https(), a_com(), None), tup(https(), b_com(), None))) by (compute_only);
    assert(!schemelessly_same_site(clazel_psl::examples::rules(), tup(https(), com(), None), tup(https(), uk(), None))) by (compute_only);
    assert(schemelessly_same_site(clazel_psl::examples::rules(), tup(https(), com(), None), tup(http(), com(), None))) by (compute_only);
    assert(!schemelessly_same_site(clazel_psl::examples::rules(), tup(https(), x_co_uk(), None), tup(https(), y_co_uk(), None))) by (compute_only);
    assert(schemelessly_same_site(clazel_psl::examples::rules(), Origin::Opaque(1nat), Origin::Opaque(1nat))) by (compute_only);
    assert(!schemelessly_same_site(clazel_psl::examples::rules(), Origin::Opaque(1nat), Origin::Opaque(2nat))) by (compute_only);
    assert(!schemelessly_same_site(clazel_psl::examples::rules(), Origin::Opaque(1nat), tup(https(), a_com(), None))) by (compute_only);
}

/// Two sites are the same when scheme and host are, and opaque sites by
/// identity only.
pub proof fn example_same_site_sites()
    ensures
        same_site_sites(Site::SchemeAndHost(https(), a_com()), Site::SchemeAndHost(https(), a_com())),
        !same_site_sites(Site::SchemeAndHost(https(), a_com()), Site::SchemeAndHost(http(), a_com())),
        !same_site_sites(Site::SchemeAndHost(https(), a_com()), Site::SchemeAndHost(https(), b_com())),
        same_site_sites(Site::Opaque(1nat), Site::Opaque(1nat)),
        !same_site_sites(Site::Opaque(1nat), Site::Opaque(2nat)),
        !same_site_sites(Site::Opaque(1nat), Site::SchemeAndHost(https(), a_com())),
        !same_site_sites(Site::SchemeAndHost(https(), a_com()), Site::Opaque(1nat)),
{
    assert(same_site_sites(Site::SchemeAndHost(https(), a_com()), Site::SchemeAndHost(https(), a_com()))) by (compute_only);
    assert(!same_site_sites(Site::SchemeAndHost(https(), a_com()), Site::SchemeAndHost(http(), a_com()))) by (compute_only);
    assert(!same_site_sites(Site::SchemeAndHost(https(), a_com()), Site::SchemeAndHost(https(), b_com()))) by (compute_only);
    assert(same_site_sites(Site::Opaque(1nat), Site::Opaque(1nat))) by (compute_only);
    assert(!same_site_sites(Site::Opaque(1nat), Site::Opaque(2nat))) by (compute_only);
    assert(!same_site_sites(Site::Opaque(1nat), Site::SchemeAndHost(https(), a_com()))) by (compute_only);
    assert(!same_site_sites(Site::SchemeAndHost(https(), a_com()), Site::Opaque(1nat))) by (compute_only);
}

/// Serialization of a site: `scheme://host`, "null" for an opaque origin.
pub proof fn example_serialization_of_site()
    ensures
        serialization_of_site(Site::SchemeAndHost(https(), a_com())) == seq![0x68u32, 0x74, 0x74, 0x70, 0x73, 0x3A, 0x2F, 0x2F, 0x61, 0x2E, 0x63, 0x6F, 0x6D],
        serialization_of_site(Site::Opaque(1nat)) == seq![0x6Eu32, 0x75, 0x6C, 0x6C],
{
    assert(serialization_of_site(Site::SchemeAndHost(https(), a_com())) == seq![0x68u32, 0x74, 0x74, 0x70, 0x73, 0x3A, 0x2F, 0x2F, 0x61, 0x2E, 0x63, 0x6F, 0x6D]) by (compute_only);
    assert(serialization_of_site(Site::Opaque(1nat)) == seq![0x6Eu32, 0x75, 0x6C, 0x6C]) by (compute_only);
}

// ---------------------------------------------------------------------
// URL §4.7: the origin of a URL.
// ---------------------------------------------------------------------

/// The five schemes with a tuple origin give one, with the URL's host and
/// port; the others (`file:`, `data:`) a new opaque origin.
pub proof fn example_url_origin()
    ensures
        url_origin(url_of(https(), Some(a_com()), Some(8080nat)), clazel_url::url::examples::identity_domain_parser(), 7nat) == tup(https(), a_com(), Some(8080nat)),
        url_origin(url_of(http(), Some(a_com()), None), clazel_url::url::examples::identity_domain_parser(), 7nat) == tup(http(), a_com(), None),
        url_origin(url_of(clazel_url::url::spec::ftp_str(), Some(a_com()), None), clazel_url::url::examples::identity_domain_parser(), 7nat) == tup(clazel_url::url::spec::ftp_str(), a_com(), None),
        url_origin(url_of(clazel_url::url::spec::ws_str(), Some(a_com()), None), clazel_url::url::examples::identity_domain_parser(), 7nat) == tup(clazel_url::url::spec::ws_str(), a_com(), None),
        url_origin(url_of(clazel_url::url::spec::wss_str(), Some(a_com()), None), clazel_url::url::examples::identity_domain_parser(), 7nat) == tup(clazel_url::url::spec::wss_str(), a_com(), None),
        url_origin(url_of(clazel_url::url::spec::file_str(), Some(clazel_url::host::spec::Host::Empty), None), clazel_url::url::examples::identity_domain_parser(), 7nat) == Origin::Opaque(7nat),
        url_origin(url_of(seq![0x64u32, 0x61, 0x74, 0x61], None, None), clazel_url::url::examples::identity_domain_parser(), 7nat) == Origin::Opaque(7nat),
        url_origin(url_of(https(), None, None), clazel_url::url::examples::identity_domain_parser(), 7nat) == Origin::Opaque(7nat),
{
    assert(url_origin(url_of(https(), Some(a_com()), Some(8080nat)), clazel_url::url::examples::identity_domain_parser(), 7nat) == tup(https(), a_com(), Some(8080nat))) by (compute_only);
    assert(url_origin(url_of(http(), Some(a_com()), None), clazel_url::url::examples::identity_domain_parser(), 7nat) == tup(http(), a_com(), None)) by (compute_only);
    assert(url_origin(url_of(clazel_url::url::spec::ftp_str(), Some(a_com()), None), clazel_url::url::examples::identity_domain_parser(), 7nat) == tup(clazel_url::url::spec::ftp_str(), a_com(), None)) by (compute_only);
    assert(url_origin(url_of(clazel_url::url::spec::ws_str(), Some(a_com()), None), clazel_url::url::examples::identity_domain_parser(), 7nat) == tup(clazel_url::url::spec::ws_str(), a_com(), None)) by (compute_only);
    assert(url_origin(url_of(clazel_url::url::spec::wss_str(), Some(a_com()), None), clazel_url::url::examples::identity_domain_parser(), 7nat) == tup(clazel_url::url::spec::wss_str(), a_com(), None)) by (compute_only);
    assert(url_origin(url_of(clazel_url::url::spec::file_str(), Some(clazel_url::host::spec::Host::Empty), None), clazel_url::url::examples::identity_domain_parser(), 7nat) == Origin::Opaque(7nat)) by (compute_only);
    assert(url_origin(url_of(seq![0x64u32, 0x61, 0x74, 0x61], None, None), clazel_url::url::examples::identity_domain_parser(), 7nat) == Origin::Opaque(7nat)) by (compute_only);
    assert(url_origin(url_of(https(), None, None), clazel_url::url::examples::identity_domain_parser(), 7nat) == Origin::Opaque(7nat)) by (compute_only);
}

/// A blob URL's origin is its path's, when that is an `http`, `https` or
/// `file` URL (steps 3 to 5): `blob:https://a.com/` has the tuple origin
/// of `https://a.com/`, `blob:file:///` and `blob:ftp://a.com/` a new
/// opaque one, and so does a path that does not parse.
pub proof fn example_url_origin_of_blob_path_url()
    ensures
        url_origin_of_blob_path_url(Some(url_of(https(), Some(a_com()), None)), 7nat) == tup(https(), a_com(), None),
        url_origin_of_blob_path_url(Some(url_of(http(), Some(a_com()), Some(8080nat))), 7nat) == tup(http(), a_com(), Some(8080nat)),
        url_origin_of_blob_path_url(Some(url_of(clazel_url::url::spec::file_str(), Some(clazel_url::host::spec::Host::Empty), None)), 7nat) == Origin::Opaque(7nat),
        url_origin_of_blob_path_url(Some(url_of(clazel_url::url::spec::ftp_str(), Some(a_com()), None)), 7nat) == Origin::Opaque(7nat),
        url_origin_of_blob_path_url(Some(url_of(clazel_url::url::spec::wss_str(), Some(a_com()), None)), 7nat) == Origin::Opaque(7nat),
        url_origin_of_blob_path_url(None, 7nat) == Origin::Opaque(7nat),
{
    assert(url_origin_of_blob_path_url(Some(url_of(https(), Some(a_com()), None)), 7nat) == tup(https(), a_com(), None)) by (compute_only);
    assert(url_origin_of_blob_path_url(Some(url_of(http(), Some(a_com()), Some(8080nat))), 7nat) == tup(http(), a_com(), Some(8080nat))) by (compute_only);
    assert(url_origin_of_blob_path_url(Some(url_of(clazel_url::url::spec::file_str(), Some(clazel_url::host::spec::Host::Empty), None)), 7nat) == Origin::Opaque(7nat)) by (compute_only);
    assert(url_origin_of_blob_path_url(Some(url_of(clazel_url::url::spec::ftp_str(), Some(a_com()), None)), 7nat) == Origin::Opaque(7nat)) by (compute_only);
    assert(url_origin_of_blob_path_url(Some(url_of(clazel_url::url::spec::wss_str(), Some(a_com()), None)), 7nat) == Origin::Opaque(7nat)) by (compute_only);
    assert(url_origin_of_blob_path_url(None, 7nat) == Origin::Opaque(7nat)) by (compute_only);
}

} // verus!
