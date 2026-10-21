//! The executable §5.1.2 to §5.1.4 algorithms, proven to meet
//! [`super::contract`]. The code mirrors the spec; the step comments live
//! in [`super::spec`].

#[allow(unused_imports)]
use super::spec::*;
use crate::strings::{at, copy, slice_eq, sub};
use clazel_url::host::record::ParsedHost;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// A canonicalized host name (§5.1.2), viewed as [`CanonicalHost`].
pub struct CanonicalHostName {
    /// The canonicalized host name: the domain, or the IP address
    /// serialization.
    pub name: Vec<u8>,
    /// The host is an IPv4 or IPv6 address, not a host name.
    pub is_ip_address: bool,
}

impl View for CanonicalHostName {
    type V = CanonicalHost;

    open spec fn view(&self) -> CanonicalHost {
        CanonicalHost { name: self.name@, is_ip_address: self.is_ip_address }
    }
}

/// The view of an optional canonical host name; `None` is failure.
pub open spec fn option_view(h: Option<CanonicalHostName>) -> Option<CanonicalHost> {
    match h {
        Some(h) => Some(h@),
        None => None,
    }
}

/// The octets of `s` if every code point is ASCII.
fn narrow_exec(s: &[u32]) -> (out: Option<Vec<u8>>)
    ensures
        all_ascii(s@) ==> (out is Some && out->Some_0@ == narrow(s@)),
        !all_ascii(s@) ==> out is None,
{
    let mut v: Vec<u8> = Vec::new();
    let mut i: usize = 0;
    while i < s.len()
        invariant
            i <= s.len(),
            forall|k: int| 0 <= k < i ==> #[trigger] s@[k] < 0x80,
            v@ == narrow(s@).subrange(0, i as int),
        decreases s.len() - i,
    {
        let c = match s.get(i) {
            Some(c) => *c,
            None => 0,
        };
        if c >= 0x80 {
            assert(!all_ascii(s@)) by {
                assert(s@[i as int] >= 0x80);
            }
            return None;
        }
        v.push(c as u8);
        assert(narrow(s@).subrange(0, i as int).push(narrow(s@)[i as int]) =~= narrow(s@).subrange(0, i as int + 1));
        // Never saturates: i < s.len().
        i = i.saturating_add(1);
    }
    assert(narrow(s@).subrange(0, s.len() as int) =~= narrow(s@));
    assert(all_ascii(s@));
    Some(v)
}

/// §5.1.2: the canonicalized host name of a host record. `None` is failure.
pub fn canonicalize_a_host_name(host: &Option<ParsedHost>) -> (output: Option<CanonicalHostName>)
    ensures
        super::contract::canonicalize_a_host_name_ensures(
            clazel_url::host::record::option_view(*host),
            option_view(output),
        ),
{
    match host {
        Some(ParsedHost::Domain(domain)) => {
            match narrow_exec(domain.as_slice()) {
                Some(name) => Some(CanonicalHostName { name, is_ip_address: false }),
                None => None,
            }
        },
        Some(h @ (ParsedHost::Ipv4(_) | ParsedHost::Ipv6(_))) => {
            let text = h.serialize();
            match narrow_exec(text.as_slice()) {
                Some(name) => Some(CanonicalHostName { name, is_ip_address: true }),
                None => None,
            }
        },
        Some(ParsedHost::Opaque(_)) => None,
        Some(ParsedHost::Empty) => None,
        None => None,
    }
}

/// §5.1.2 on a host string: the URL host parser, then
/// [`canonicalize_a_host_name`].
pub fn canonicalize_a_host_name_string(host: &[u32]) -> (output: Option<CanonicalHostName>)
    requires
        super::contract::canonicalize_a_host_name_string_requires(host@),
    ensures
        super::contract::canonicalize_a_host_name_string_ensures(host@, option_view(output)),
{
    let parsed = clazel_url::host::parse::host_parser_full(host, false);
    canonicalize_a_host_name(&parsed)
}

/// §5.1.3: does `string` domain-match `domain`?
pub fn domain_matches(string: &[u8], string_is_host_name: bool, domain: &[u8]) -> (output: bool)
    ensures
        super::contract::domain_matches_ensures(string@, string_is_host_name, domain@, output),
{
    if slice_eq(string, domain) {
        return true;
    }
    if !string_is_host_name || string.len() <= domain.len() {
        return false;
    }
    // Never saturates: string.len() > domain.len().
    let boundary = string.len().saturating_sub(domain.len());
    let suffix = vstd::slice::slice_subrange(string, boundary, string.len());
    if !slice_eq(suffix, domain) {
        return false;
    }
    assert(domain@.is_suffix_of(string@)) by {
        assert(string@.skip(boundary as int) =~= suffix@);
    }
    // Never saturates: boundary > 0.
    at(string, boundary.saturating_sub(1)) == Some(0x2E)
}

/// The number of "/" in `s`.
fn slash_count_exec(s: &[u8]) -> (r: usize)
    ensures
        r == slash_count(s@),
{
    let mut count: usize = 0;
    let mut i: usize = 0;
    assert(s@.subrange(0, 0) =~= Seq::<u8>::empty());
    while i < s.len()
        invariant
            i <= s.len(),
            count <= i,
            count == slash_count(s@.subrange(0, i as int)),
        decreases s.len() - i,
    {
        let c = at(s, i);
        assert(s@.subrange(0, i as int + 1).drop_last() =~= s@.subrange(0, i as int));
        assert(s@.subrange(0, i as int + 1).last() == s@[i as int]);
        if c == Some(0x2F) {
            // Never saturates: count <= i < s.len().
            count = count.saturating_add(1);
        }
        // Never saturates: i < s.len().
        i = i.saturating_add(1);
    }
    assert(s@.subrange(0, s.len() as int) =~= s@);
    count
}

/// The index of the right-most "/" in `s`, if any.
fn rightmost_slash_exec(s: &[u8]) -> (r: Option<usize>)
    ensures
        r is Some ==> (r->Some_0 as int == rightmost_slash(s@) && r->Some_0 < s.len()),
        r is None ==> rightmost_slash(s@) == -1,
{
    let mut end = s.len();
    assert(s@.subrange(0, end as int) =~= s@);
    while end > 0
        invariant
            end <= s.len(),
            rightmost_slash(s@) == rightmost_slash(s@.subrange(0, end as int)),
        decreases end,
    {
        // Never saturates: end > 0.
        let last = end.saturating_sub(1);
        assert(s@.subrange(0, end as int).last() == s@[last as int]);
        assert(s@.subrange(0, end as int).drop_last() =~= s@.subrange(0, last as int));
        if at(s, last) == Some(0x2F) {
            return Some(last);
        }
        end = last;
    }
    None
}

/// §5.1.4: the default-path of a cookie.
pub fn default_path(uri_path: &[u8]) -> (output: Vec<u8>)
    ensures
        super::contract::default_path_ensures(uri_path@, output@),
{
    let mut slash: Vec<u8> = Vec::new();
    slash.push(0x2F);
    assert(slash@ =~= seq![0x2Fu8]);
    if uri_path.is_empty() || at(uri_path, 0) != Some(0x2F) {
        return slash;
    }
    if slash_count_exec(uri_path) <= 1 {
        return slash;
    }
    proof {
        super::lemmas::lemma_rightmost_slash(uri_path@);
    }
    match rightmost_slash_exec(uri_path) {
        Some(k) => {
            assert(uri_path@.take(k as int) =~= uri_path@.subrange(0, k as int));
            sub(uri_path, 0, k)
        },
        None => slash,
    }
}

/// §5.1.4: does `request_path` path-match `cookie_path`?
pub fn path_matches(request_path: &[u8], cookie_path: &[u8]) -> (output: bool)
    ensures
        super::contract::path_matches_ensures(request_path@, cookie_path@, output),
{
    if slice_eq(request_path, cookie_path) {
        return true;
    }
    if cookie_path.len() > request_path.len() {
        return false;
    }
    let head = vstd::slice::slice_subrange(request_path, 0, cookie_path.len());
    if !slice_eq(head, cookie_path) {
        return false;
    }
    assert(cookie_path@.is_prefix_of(request_path@));
    // The cookie-path is a prefix of the request-path.
    if cookie_path.len() > 0 {
        // Never saturates: cookie_path.len() > 0.
        if at(cookie_path, cookie_path.len().saturating_sub(1)) == Some(0x2F) {
            return true;
        }
    }
    at(request_path, cookie_path.len()) == Some(0x2F)
}

} // verus!
