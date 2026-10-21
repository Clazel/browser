//! The executable origin and site types and functions, each proven to meet
//! its contract in [`super::contract`].

use clazel_psl::exec::registrable_domain_exec;
use clazel_url::host::record::{ParsedHost, append, at16, copy};
use clazel_url::host::serialize::push_decimal;
use clazel_url::url::parse::basic_url_parser;
use clazel_url::url::record::{ParsedUrl, clone_host};
use clazel_url::url::serialize::url_path_serializer;
#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// An origin (HTML §7.1.1), viewed as [`Origin`]. An opaque origin is a
/// `u64` id.
pub enum ParsedOrigin {
    /// An opaque origin.
    Opaque(u64),
    /// A tuple origin.
    Tuple {
        /// The scheme.
        scheme: Vec<u32>,
        /// The host.
        host: ParsedHost,
        /// The port.
        port: Option<u16>,
        /// The domain.
        domain: Option<ParsedHost>,
    },
}

/// The view of an optional host.
pub open spec fn opt_host_view(h: Option<ParsedHost>) -> Option<clazel_url::host::spec::Host> {
    match h {
        Some(h) => Some(h@),
        None => None,
    }
}

impl View for ParsedOrigin {
    type V = Origin;

    open spec fn view(&self) -> Origin {
        match self {
            ParsedOrigin::Opaque(id) => Origin::Opaque(*id as nat),
            ParsedOrigin::Tuple { scheme, host, port, domain } => Origin::Tuple {
                scheme: scheme@,
                host: host@,
                port: clazel_url::url::record::port_view(*port),
                domain: opt_host_view(*domain),
            },
        }
    }
}

/// A site (HTML §7.1.1.1), viewed as [`Site`].
pub enum ParsedSite {
    /// An opaque origin.
    Opaque(u64),
    /// A scheme-and-host.
    SchemeAndHost(Vec<u32>, ParsedHost),
}

impl View for ParsedSite {
    type V = Site;

    open spec fn view(&self) -> Site {
        match self {
            ParsedSite::Opaque(id) => Site::Opaque(*id as nat),
            ParsedSite::SchemeAndHost(s, h) => Site::SchemeAndHost(s@, h@),
        }
    }
}

/// Whether two code point strings are equal.
fn equal_exec(a: &[u32], b: &[u32]) -> (r: bool)
    ensures
        r == (a@ == b@),
{
    if a.len() != b.len() {
        return false;
    }
    let mut i: usize = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            a.len() == b.len(),
            forall|k: int| 0 <= k < i ==> a@[k] == b@[k],
        decreases a.len() - i,
    {
        match (a.get(i), b.get(i)) {
            (Some(x), Some(y)) if *x != *y => {
                return false;
            },
            _ => {},
        }
        i = i.saturating_add(1);
    }
    proof {
        assert(a@ =~= b@);
    }
    true
}

/// Whether two IPv6 addresses' pieces are equal.
fn ipv6_equals(x: &[u16; 8], y: &[u16; 8]) -> (r: bool)
    ensures
        r == (clazel_url::host::contract::pieces_view(x@) == clazel_url::host::contract::pieces_view(y@)),
{
    let mut i: usize = 0;
    while i < 8
        invariant
            i <= 8,
            x@.len() == 8,
            y@.len() == 8,
            forall|k: int| 0 <= k < i ==> x@[k] == y@[k],
        decreases 8 - i,
    {
        let xi = at16(x.as_slice(), i);
        let yi = at16(y.as_slice(), i);
        proof {
            assert(xi == x@[i as int]);
            assert(yi == y@[i as int]);
        }
        if xi != yi {
            proof {
                let px = clazel_url::host::contract::pieces_view(x@);
                let py = clazel_url::host::contract::pieces_view(y@);
                assert(px[i as int] == x@[i as int] as nat);
                assert(py[i as int] == y@[i as int] as nat);
                assert(px != py);
            }
            return false;
        }
        i = i.saturating_add(1);
    }
    proof {
        assert(x@ =~= y@);
    }
    true
}

/// Whether two hosts are equal.
pub fn host_equals(a: &ParsedHost, b: &ParsedHost) -> (r: bool)
    ensures
        r == (a@ == b@),
{
    match (a, b) {
        (ParsedHost::Domain(x), ParsedHost::Domain(y)) => equal_exec(x.as_slice(), y.as_slice()),
        (ParsedHost::Opaque(x), ParsedHost::Opaque(y)) => equal_exec(x.as_slice(), y.as_slice()),
        (ParsedHost::Ipv4(x), ParsedHost::Ipv4(y)) => *x == *y,
        (ParsedHost::Empty, ParsedHost::Empty) => true,
        (ParsedHost::Ipv6(x), ParsedHost::Ipv6(y)) => ipv6_equals(x, y),
        _ => false,
    }
}

/// Whether two optional hosts are equal (both null, or both hosts that
/// are).
fn opt_host_equals(a: &Option<ParsedHost>, b: &Option<ParsedHost>) -> (r: bool)
    ensures
        r == (opt_host_view(*a) == opt_host_view(*b)),
{
    match (a, b) {
        (None, None) => true,
        (Some(x), Some(y)) => host_equals(x, y),
        _ => false,
    }
}

/// Whether two optional ports are equal.
fn port_equals(a: Option<u16>, b: Option<u16>) -> (r: bool)
    ensures
        r == (clazel_url::url::record::port_view(a) == clazel_url::url::record::port_view(b)),
{
    match (a, b) {
        (None, None) => true,
        (Some(x), Some(y)) => x == y,
        _ => false,
    }
}

/// HTML §7.1.1 "same origin".
pub fn same_origin_exec(a: &ParsedOrigin, b: &ParsedOrigin) -> (output: bool)
    ensures
        super::contract::same_origin_ensures(a@, b@, output),
{
    match (a, b) {
        (ParsedOrigin::Opaque(x), ParsedOrigin::Opaque(y)) => *x == *y,
        (
            ParsedOrigin::Tuple { scheme: sa, host: ha, port: pa, .. },
            ParsedOrigin::Tuple { scheme: sb, host: hb, port: pb, .. },
        ) => equal_exec(sa.as_slice(), sb.as_slice()) && port_equals(*pa, *pb) && host_equals(ha, hb),
        _ => false,
    }
}

/// HTML §7.1.1 "same origin-domain".
pub fn same_origin_domain_exec(a: &ParsedOrigin, b: &ParsedOrigin) -> (output: bool)
    ensures
        super::contract::same_origin_domain_ensures(a@, b@, output),
{
    match (a, b) {
        (ParsedOrigin::Opaque(x), ParsedOrigin::Opaque(y)) => *x == *y,
        (
            ParsedOrigin::Tuple { scheme: sa, domain: da, .. },
            ParsedOrigin::Tuple { scheme: sb, domain: db, .. },
        ) => {
            if equal_exec(sa.as_slice(), sb.as_slice()) && opt_host_equals(da, db) && da.is_some() {
                true
            } else {
                same_origin_exec(a, b) && da.is_none() && db.is_none()
            }
        },
        _ => false,
    }
}

/// HTML §7.1.1 "serialization of an origin".
pub fn serialization_of_origin_exec(origin: &ParsedOrigin) -> (output: Vec<u32>)
    ensures
        super::contract::serialization_of_origin_ensures(origin@, output@),
{
    match origin {
        ParsedOrigin::Opaque(_) => {
            let lit: [u32; 4] = [0x6E, 0x75, 0x6C, 0x6C];
            let out = copy(lit.as_slice());
            proof {
                assert(out@ =~= serialization_of_origin(origin@));
            }
            out
        },
        ParsedOrigin::Tuple { scheme, host, port, .. } => {
            let mut out = copy(scheme.as_slice());
            out.push(0x3A);
            out.push(0x2F);
            out.push(0x2F);
            let h = host.serialize();
            append(&mut out, h.as_slice());
            if let Some(p) = port {
                out.push(0x3A);
                push_decimal(*p as u32, &mut out);
            }
            proof {
                assert(out@ =~= serialization_of_origin(origin@));
            }
            out
        },
    }
}

/// HTML §7.1.1.1 "obtain a site".
pub fn obtain_a_site_exec(origin: &ParsedOrigin) -> (output: ParsedSite)
    ensures
        super::contract::obtain_a_site_ensures(origin@, output@),
{
    match origin {
        ParsedOrigin::Opaque(id) => ParsedSite::Opaque(*id),
        ParsedOrigin::Tuple { scheme, host, .. } => match registrable_domain_exec(host) {
            None => ParsedSite::SchemeAndHost(copy(scheme.as_slice()), clone_host(host)),
            Some(rd) => ParsedSite::SchemeAndHost(copy(scheme.as_slice()), ParsedHost::Domain(rd)),
        },
    }
}

/// HTML §7.1.1.1 "same site" for two sites.
pub fn same_site_sites_exec(a: &ParsedSite, b: &ParsedSite) -> (output: bool)
    ensures
        output == same_site_sites(a@, b@),
{
    match (a, b) {
        (ParsedSite::Opaque(x), ParsedSite::Opaque(y)) => *x == *y,
        (ParsedSite::SchemeAndHost(sa, ha), ParsedSite::SchemeAndHost(sb, hb)) => {
            equal_exec(sa.as_slice(), sb.as_slice()) && host_equals(ha, hb)
        },
        _ => false,
    }
}

/// HTML §7.1.1.1 "serialization of a site".
pub fn serialization_of_site_exec(site: &ParsedSite) -> (output: Vec<u32>)
    ensures
        super::contract::serialization_of_site_ensures(site@, output@),
{
    match site {
        ParsedSite::Opaque(_) => {
            let lit: [u32; 4] = [0x6E, 0x75, 0x6C, 0x6C];
            let out = copy(lit.as_slice());
            proof {
                assert(out@ =~= serialization_of_site(site@));
            }
            out
        },
        ParsedSite::SchemeAndHost(scheme, host) => {
            let mut out = copy(scheme.as_slice());
            out.push(0x3A);
            out.push(0x2F);
            out.push(0x2F);
            let h = host.serialize();
            append(&mut out, h.as_slice());
            proof {
                assert(out@ =~= serialization_of_site(site@));
            }
            out
        },
    }
}

/// HTML §7.1.1.1 "same site" for two origins.
pub fn same_site_exec(a: &ParsedOrigin, b: &ParsedOrigin) -> (output: bool)
    ensures
        super::contract::same_site_ensures(a@, b@, output),
{
    let sa = obtain_a_site_exec(a);
    let sb = obtain_a_site_exec(b);
    same_site_sites_exec(&sa, &sb)
}

/// Whether two optional strings are equal.
fn opt_vec_equals(a: &Option<Vec<u32>>, b: &Option<Vec<u32>>) -> (r: bool)
    ensures
        r == (clazel_url::host::record::opt_seq(*a) == clazel_url::host::record::opt_seq(*b)),
{
    match (a, b) {
        (None, None) => true,
        (Some(x), Some(y)) => equal_exec(x.as_slice(), y.as_slice()),
        _ => false,
    }
}

/// HTML §7.1.1.1 "schemelessly same site".
pub fn schemelessly_same_site_exec(a: &ParsedOrigin, b: &ParsedOrigin) -> (output: bool)
    ensures
        super::contract::schemelessly_same_site_ensures(a@, b@, output),
{
    match (a, b) {
        (ParsedOrigin::Opaque(x), ParsedOrigin::Opaque(y)) => *x == *y,
        (ParsedOrigin::Tuple { host: host_a, .. }, ParsedOrigin::Tuple { host: host_b, .. }) => {
            let ra = registrable_domain_exec(host_a);
            let rb = registrable_domain_exec(host_b);
            if host_equals(host_a, host_b) && ra.is_none() {
                true
            } else {
                opt_vec_equals(&ra, &rb) && ra.is_some()
            }
        },
        _ => false,
    }
}

/// "`blob`".
fn blob_exec() -> (v: Vec<u32>)
    ensures
        v@ == blob_str(),
{
    let lit: [u32; 4] = [0x62, 0x6C, 0x6F, 0x62];
    let v = copy(lit.as_slice());
    proof {
        assert(v@ =~= blob_str());
    }
    v
}

/// Whether `s` is the ASCII string `lit`'s code points.
fn is_scheme(s: &[u32], lit: &[u32]) -> (r: bool)
    ensures
        r == (s@ == lit@),
{
    equal_exec(s, lit)
}

/// Whether `s` is a scalar value string.
fn all_scalar_values_exec(s: &[u32]) -> (r: bool)
    ensures
        r == clazel_encoding::utf8::spec::all_scalar_values(s@),
{
    let mut i: usize = 0;
    while i < s.len()
        invariant
            i <= s.len(),
            forall|k: int| 0 <= k < i ==> clazel_encoding::utf8::spec::is_scalar_value(s@[k]),
        decreases s.len() - i,
    {
        match s.get(i) {
            Some(c) if *c > 0x10FFFF || (0xD800 <= *c && *c <= 0xDFFF) => {
                proof {
                    assert(!clazel_encoding::utf8::spec::is_scalar_value(s@[i as int]));
                }
                return false;
            },
            _ => {},
        }
        i = i.saturating_add(1);
    }
    true
}

/// URL §4.7 "origin" of a URL whose scheme is not "blob".
fn url_origin_not_blob_exec(url: &ParsedUrl, fresh: u64) -> (output: ParsedOrigin)
    ensures
        output@ == url_origin_not_blob(url@, fresh as nat),
{
    let tuple_scheme = is_scheme(url.scheme.as_slice(), &[0x66, 0x74, 0x70])
        || is_scheme(url.scheme.as_slice(), &[0x68, 0x74, 0x74, 0x70])
        || is_scheme(url.scheme.as_slice(), &[0x68, 0x74, 0x74, 0x70, 0x73])
        || is_scheme(url.scheme.as_slice(), &[0x77, 0x73])
        || is_scheme(url.scheme.as_slice(), &[0x77, 0x73, 0x73]);
    proof {
        assert(tuple_scheme == has_tuple_origin_scheme(url.scheme@)) by {
            assert(clazel_url::url::spec::ftp_str() =~= seq![0x66u32, 0x74, 0x70]);
            assert(clazel_url::url::spec::http_str() =~= seq![0x68u32, 0x74, 0x74, 0x70]);
            assert(clazel_url::url::spec::https_str() =~= seq![0x68u32, 0x74, 0x74, 0x70, 0x73]);
            assert(clazel_url::url::spec::ws_str() =~= seq![0x77u32, 0x73]);
            assert(clazel_url::url::spec::wss_str() =~= seq![0x77u32, 0x73, 0x73]);
        }
    }
    if tuple_scheme {
        match &url.host {
            Some(h) => ParsedOrigin::Tuple {
                scheme: copy(url.scheme.as_slice()),
                host: clone_host(h),
                port: url.port,
                domain: None,
            },
            None => ParsedOrigin::Opaque(fresh),
        }
    } else {
        ParsedOrigin::Opaque(fresh)
    }
}

/// URL §4.7 "origin" of a URL, with `fresh` the id of "a new opaque
/// origin".
pub fn url_origin_exec(url: &ParsedUrl, fresh: u64) -> (output: ParsedOrigin)
    ensures
        super::contract::url_origin_ensures(url@, fresh as nat, output@),
{
    let blob = blob_exec();
    if equal_exec(url.scheme.as_slice(), blob.as_slice()) {
        let path = url_path_serializer(&url.path);
        if !all_scalar_values_exec(path.as_slice()) {
            return ParsedOrigin::Opaque(fresh);
        }
        match basic_url_parser(path.as_slice(), None) {
            None => ParsedOrigin::Opaque(fresh),
            Some(path_url) => {
                let http_like = is_scheme(path_url.scheme.as_slice(), &[0x68, 0x74, 0x74, 0x70])
                    || is_scheme(path_url.scheme.as_slice(), &[0x68, 0x74, 0x74, 0x70, 0x73])
                    || is_scheme(path_url.scheme.as_slice(), &[0x66, 0x69, 0x6C, 0x65]);
                proof {
                    assert(clazel_url::url::spec::http_str() =~= seq![0x68u32, 0x74, 0x74, 0x70]);
                    assert(clazel_url::url::spec::https_str() =~= seq![0x68u32, 0x74, 0x74, 0x70, 0x73]);
                    assert(clazel_url::url::spec::file_str() =~= seq![0x66u32, 0x69, 0x6C, 0x65]);
                }
                if http_like {
                    url_origin_not_blob_exec(&path_url, fresh)
                } else {
                    ParsedOrigin::Opaque(fresh)
                }
            },
        }
    } else {
        url_origin_not_blob_exec(url, fresh)
    }
}

} // verus!
