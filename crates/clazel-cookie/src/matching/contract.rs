//! Contracts the executable matching functions must be proven to meet.
//! Each exec function's `ensures` clause is exactly one of these
//! predicates, so reviewing these (and [`super::spec`]) is enough to know
//! what the implementation guarantees.
//!
//! Octet strings are `&[u8]`; host strings are scalar values as `u32`, as
//! in `clazel-url`. An exec canonical host is viewed as a
//! [`CanonicalHost`]; `None` is failure.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Contract for `canonicalize_a_host_name(Option<&ParsedHost>) ->
/// Option<CanonicalHostName>`.
pub open spec fn canonicalize_a_host_name_ensures(host: Option<clazel_url::host::spec::Host>, output: Option<CanonicalHost>) -> bool {
    output == canonicalize_a_host_name(host)
}

/// Precondition of `canonicalize_a_host_name_string(&[u32])`: the host
/// parser's.
pub open spec fn canonicalize_a_host_name_string_requires(host: Seq<u32>) -> bool {
    clazel_url::host::contract::host_parser_full_requires(host, false)
}

/// Contract for `canonicalize_a_host_name_string(&[u32]) ->
/// Option<CanonicalHostName>`: the host parser, then the canonicalization.
pub open spec fn canonicalize_a_host_name_string_ensures(host: Seq<u32>, output: Option<CanonicalHost>) -> bool {
    output == canonicalize_a_host_name_string(host)
}

/// Contract for `domain_matches(&[u8], bool, &[u8]) -> bool`.
pub open spec fn domain_matches_ensures(string: Seq<u8>, string_is_host_name: bool, domain: Seq<u8>, output: bool) -> bool {
    output == domain_matches(string, string_is_host_name, domain)
}

/// Contract for `default_path(&[u8]) -> Vec<u8>`.
pub open spec fn default_path_ensures(uri_path: Seq<u8>, output: Seq<u8>) -> bool {
    output == default_path(uri_path)
}

/// Contract for `path_matches(&[u8], &[u8]) -> bool`.
pub open spec fn path_matches_ensures(request_path: Seq<u8>, cookie_path: Seq<u8>, output: bool) -> bool {
    output == path_matches(request_path, cookie_path)
}

} // verus!
