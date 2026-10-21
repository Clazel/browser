//! Contracts the executable URL functions must be proven to meet. Each
//! exec function's `ensures` clause is exactly one of these predicates (and
//! its `requires`, where it has one), so reviewing these and
//! [`super::spec`] is enough to know what the implementation guarantees.
//!
//! Strings are code points as `u32`, as elsewhere in this crate. The exec
//! URL record, `ParsedUrl`, views as [`Url`]: its port is a `u16` (so a
//! viewed port is below 2^16) and its host a `ParsedHost`
//! (`crate::host::record`).
//!
//! **The domain parser is `clazel-idna`'s**: the exec parser runs the host
//! parser through `crate::host::parse::host_parser_full`, so its contract
//! is the spec instantiated with [`url_domain_parser`], exactly as for the
//! host parser alone.
//!
//! State override (item 1.11) is not part of these contracts: the exec
//! parser is the basic URL parser with no url and no state override.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The URL §3.3 domain parser, `clazel-idna`'s, which the host parser's
/// step 6 runs (the same as `crate::host::contract::url_domain_parser`).
pub open spec fn url_domain_parser() -> crate::host::spec::DomainParser {
    crate::host::contract::url_domain_parser()
}

/// Precondition of `basic_url_parser(&[u32], Option<&ParsedUrl>) ->
/// Option<ParsedUrl>`: "a scalar value string input".
pub open spec fn basic_url_parser_requires(input: Seq<u32>) -> bool {
    clazel_encoding::utf8::spec::all_scalar_values(input)
}

/// Contract for `basic_url_parser(&[u32], Option<&ParsedUrl>) ->
/// Option<ParsedUrl>`: the basic URL parser on input with base (`None` is
/// null), no url and no state override; `None` is failure.
pub open spec fn basic_url_parser_ensures(input: Seq<u32>, base: Option<Url>, output: Option<Url>) -> bool {
    output == basic_url_parser(input, base, url_domain_parser())
}

/// Contract for `url_path_serializer(&ParsedPath) -> Vec<u32>`: the URL
/// path serializer.
pub open spec fn url_path_serializer_ensures(path: UrlPath, output: Seq<u32>) -> bool {
    output == url_path_serializer(path)
}

/// Contract for `ParsedUrl::serialize(&self, bool) -> Vec<u32>`: the URL
/// serializer, with exclude fragment.
pub open spec fn url_serializer_ensures(url: Url, exclude_fragment: bool, output: Seq<u32>) -> bool {
    output == url_serializer(url, exclude_fragment)
}

} // verus!
