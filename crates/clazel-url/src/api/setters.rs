//! The executable URL API setters (URL §6.1), each proven to meet its
//! contract in [`super::contract`]: a function that changes an exec URL
//! record in place. The step comments live in [`super::spec`].

#[allow(unused_imports)]
use super::spec::*;
use crate::host::record::{ParsedHost, at32, copy};
use crate::url::parse::{basic_url_parse_in_place, basic_url_parser};
use crate::url::record::{ParsedPath, ParsedUrl, is_file};
use crate::url::spec::State;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// "Cannot have a username/password/port" (URL §4.2).
fn cannot_have_username_password_port_exec(url: &ParsedUrl) -> (r: bool)
    ensures
        r == crate::url::spec::cannot_have_username_password_port(url@),
{
    url.host.is_none() || matches!(url.host, Some(ParsedHost::Empty)) || is_file(url.scheme.as_slice())
}

/// "Has an opaque path" (URL §4.2).
fn has_opaque_path_exec(url: &ParsedUrl) -> (r: bool)
    ensures
        r == crate::url::spec::has_opaque_path(url@),
{
    matches!(url.path, ParsedPath::Opaque(_))
}

/// `value` with a single leading `c` removed, if any.
fn remove_single_leading_exec(value: &[u32], c: u32) -> (out: Vec<u32>)
    requires
        clazel_encoding::utf8::spec::all_scalar_values(value@),
    ensures
        out@ == remove_single_leading(value@, c),
        clazel_encoding::utf8::spec::all_scalar_values(out@),
{
    if value.is_empty() || at32(value, 0) != c {
        return copy(value);
    }
    let n = value.len();
    let mut out: Vec<u32> = Vec::new();
    let mut k: usize = 1;
    while k < n
        invariant
            1 <= k <= n,
            n == value.len(),
            out@ == value@.subrange(1, k as int),
        decreases n - k,
    {
        out.push(at32(value, k));
        // Never saturates: k is below a length.
        k = k.saturating_add(1);
        assert(out@ =~= value@.subrange(1, k as int));
    }
    out
}

/// The `href` setter; false is "throw a TypeError" (the URL is
/// unchanged).
pub fn set_href(url: &mut ParsedUrl, value: &[u32]) -> (ok: bool)
    requires
        super::contract::setter_requires(value@),
    ensures
        super::contract::href_setter_ensures(old(url)@, value@, ok, final(url)@),
{
    // 1.
    match basic_url_parser(value, None) {
        // 2.
        None => false,
        // 3.
        Some(parsed) => {
            *url = parsed;
            true
        },
    }
}

/// The `protocol` setter.
pub fn set_protocol(url: &mut ParsedUrl, value: &[u32])
    requires
        super::contract::setter_requires(value@),
    ensures
        super::contract::protocol_setter_ensures(old(url)@, value@, final(url)@),
{
    let mut input = copy(value);
    input.push(0x3A);
    assert(clazel_encoding::utf8::spec::all_scalar_values(input@)) by {
        assert forall|k: int| 0 <= k < input@.len() implies clazel_encoding::utf8::spec::is_scalar_value(#[trigger] input@[k]) by {
            if k < value@.len() {
                assert(input@[k] == value@[k]);
            }
        }
    }
    basic_url_parse_in_place(input.as_slice(), url, State::SchemeStart);
}

/// The `username` setter.
pub fn set_username(url: &mut ParsedUrl, value: &[u32])
    requires
        super::contract::setter_requires(value@),
    ensures
        super::contract::username_setter_ensures(old(url)@, value@, final(url)@),
{
    if cannot_have_username_password_port_exec(url) {
        // 1.
        return;
    }
    // 2.
    url.username = clazel_percent::encode::utf8_percent_encode(value, clazel_percent::spec::PercentEncodeSet::Userinfo);
}

/// The `password` setter.
pub fn set_password(url: &mut ParsedUrl, value: &[u32])
    requires
        super::contract::setter_requires(value@),
    ensures
        super::contract::password_setter_ensures(old(url)@, value@, final(url)@),
{
    if cannot_have_username_password_port_exec(url) {
        // 1.
        return;
    }
    // 2.
    url.password = clazel_percent::encode::utf8_percent_encode(value, clazel_percent::spec::PercentEncodeSet::Userinfo);
}

/// The `host` setter.
pub fn set_host(url: &mut ParsedUrl, value: &[u32])
    requires
        super::contract::setter_requires(value@),
    ensures
        super::contract::host_setter_ensures(old(url)@, value@, final(url)@),
{
    if has_opaque_path_exec(url) {
        // 1.
        return;
    }
    // 2.
    basic_url_parse_in_place(value, url, State::Host);
}

/// The `hostname` setter.
pub fn set_hostname(url: &mut ParsedUrl, value: &[u32])
    requires
        super::contract::setter_requires(value@),
    ensures
        super::contract::hostname_setter_ensures(old(url)@, value@, final(url)@),
{
    if has_opaque_path_exec(url) {
        // 1.
        return;
    }
    // 2.
    basic_url_parse_in_place(value, url, State::Hostname);
}

/// The `port` setter.
pub fn set_port(url: &mut ParsedUrl, value: &[u32])
    requires
        super::contract::setter_requires(value@),
    ensures
        super::contract::port_setter_ensures(old(url)@, value@, final(url)@),
{
    if cannot_have_username_password_port_exec(url) {
        // 1.
        return;
    }
    if value.is_empty() {
        // 2.
        url.port = None;
    } else {
        // 3.
        basic_url_parse_in_place(value, url, State::Port);
    }
}

/// The `pathname` setter.
pub fn set_pathname(url: &mut ParsedUrl, value: &[u32])
    requires
        super::contract::setter_requires(value@),
    ensures
        super::contract::pathname_setter_ensures(old(url)@, value@, final(url)@),
{
    if has_opaque_path_exec(url) {
        // 1.
        return;
    }
    // 2.
    url.path = ParsedPath::List(Vec::new());
    assert(crate::url::record::segments_view(Seq::<Vec<u32>>::empty()) =~= Seq::<Seq<u32>>::empty());
    // 3.
    basic_url_parse_in_place(value, url, State::PathStart);
}

/// The `search` setter.
pub fn set_search(url: &mut ParsedUrl, value: &[u32])
    requires
        super::contract::setter_requires(value@),
    ensures
        super::contract::search_setter_ensures(old(url)@, value@, final(url)@),
{
    if value.is_empty() {
        // 2.
        url.query = None;
        return;
    }
    // 3.
    let input = remove_single_leading_exec(value, 0x3F);
    // 4.
    url.query = Some(Vec::new());
    assert(crate::host::record::opt_seq(url.query) == Some(Seq::<u32>::empty()));
    // 5.
    basic_url_parse_in_place(input.as_slice(), url, State::Query);
}

/// The `hash` setter.
pub fn set_hash(url: &mut ParsedUrl, value: &[u32])
    requires
        super::contract::setter_requires(value@),
    ensures
        super::contract::hash_setter_ensures(old(url)@, value@, final(url)@),
{
    if value.is_empty() {
        // 1.
        url.fragment = None;
        return;
    }
    // 2.
    let input = remove_single_leading_exec(value, 0x23);
    // 3.
    url.fragment = Some(Vec::new());
    assert(crate::host::record::opt_seq(url.fragment) == Some(Seq::<u32>::empty()));
    // 4.
    basic_url_parse_in_place(input.as_slice(), url, State::Fragment);
}

} // verus!
