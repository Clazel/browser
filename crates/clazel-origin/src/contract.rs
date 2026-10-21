//! Contracts the executable functions must be proven to meet. Each exec
//! function's `ensures` clause is exactly one of these predicates, so
//! reviewing these and [`super::spec`] is enough to know what the
//! implementation guarantees. Sites are computed over the generated Public
//! Suffix List ([`clazel_psl::table::psl_rules`]), and the origin of a URL
//! with `clazel-idna`'s domain parser, as `clazel-url`'s parser does.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Contract for `same_origin_exec(&ParsedOrigin, &ParsedOrigin) -> bool`.
pub open spec fn same_origin_ensures(a: Origin, b: Origin, output: bool) -> bool {
    output == same_origin(a, b)
}

/// Contract for `same_origin_domain_exec(&ParsedOrigin, &ParsedOrigin) ->
/// bool`.
pub open spec fn same_origin_domain_ensures(a: Origin, b: Origin, output: bool) -> bool {
    output == same_origin_domain(a, b)
}

/// Contract for `serialization_of_origin_exec(&ParsedOrigin) -> Vec<u32>`.
pub open spec fn serialization_of_origin_ensures(origin: Origin, output: Seq<u32>) -> bool {
    output == serialization_of_origin(origin)
}

/// Contract for `obtain_a_site_exec(&ParsedOrigin) -> ParsedSite`.
pub open spec fn obtain_a_site_ensures(origin: Origin, output: Site) -> bool {
    output == obtain_a_site(clazel_psl::table::psl_rules(), origin)
}

/// Contract for `same_site_exec(&ParsedOrigin, &ParsedOrigin) -> bool`.
pub open spec fn same_site_ensures(a: Origin, b: Origin, output: bool) -> bool {
    output == same_site(clazel_psl::table::psl_rules(), a, b)
}

/// Contract for `schemelessly_same_site_exec(&ParsedOrigin, &ParsedOrigin)
/// -> bool`.
pub open spec fn schemelessly_same_site_ensures(a: Origin, b: Origin, output: bool) -> bool {
    output == schemelessly_same_site(clazel_psl::table::psl_rules(), a, b)
}

/// Contract for `serialization_of_site_exec(&ParsedSite) -> Vec<u32>`.
pub open spec fn serialization_of_site_ensures(site: Site, output: Seq<u32>) -> bool {
    output == serialization_of_site(site)
}

/// Contract for `url_origin_exec(&ParsedUrl, u64) -> ParsedOrigin`: URL §4.7
/// with the new opaque origin's id `fresh`.
pub open spec fn url_origin_ensures(url: clazel_url::url::spec::Url, fresh: nat, output: Origin) -> bool {
    output == url_origin(url, clazel_url::url::contract::url_domain_parser(), fresh)
}

} // verus!
