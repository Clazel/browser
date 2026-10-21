//! Contracts the executable host functions must be proven to meet. Each
//! exec function's `ensures` clause is exactly one of these predicates (and
//! its `requires`, where it has one), so reviewing these and
//! [`super::spec`] is enough to know what the implementation guarantees.
//!
//! Strings are code points as `u32`, as in `clazel-encoding` (see its
//! `utf8/contract.rs` for why not `char`). An IPv4 address is a `u32` and
//! an IPv6 address `[u16; 8]`; [`pieces_view`] maps the latter to the
//! spec's `Seq<nat>`.
//!
//! **The host parser is two functions around the domain parser, and a third
//! that joins them.** Host parser step 6 runs the domain parser (URL §3.3),
//! which `clazel-idna` provides. `host_parser_start` runs steps 1 to 5: it either returns the
//! host parser's result (the input is bracketed or opaque), or the string
//! step 6 passes to the domain parser. `host_parser_finish` takes the
//! domain parser's result and runs steps 7 to 9. Both contracts quantify
//! over every possible domain parser, so they assume nothing about it; the
//! full host parser is `start`, then the domain parser, then `finish`, which
//! `host_parser_full` does with `clazel-idna`'s domain parser ([`url_domain_parser`]).

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The spec view of an IPv6 address's pieces.
pub open spec fn pieces_view(a: Seq<u16>) -> Seq<nat> {
    a.map_values(|p: u16| p as nat)
}

/// `n`, or 2^32 if `n` is larger: what the executable IPv4 number parser
/// returns for a number the spec computes exactly.
pub open spec fn saturate_u32(n: nat) -> nat {
    if n > 0xFFFF_FFFF {
        0x1_0000_0000
    } else {
        n
    }
}

/// Contract for `ipv4_number_parser(&[u32]) -> Option<(u64, bool)>`: the
/// IPv4 number parser, with the number saturated at 2^32 (every caller only
/// compares it with 2^32 or less).
pub open spec fn ipv4_number_parser_ensures(input: Seq<u32>, output: Option<(u64, bool)>) -> bool {
    match (ipv4_number_parser(input), output) {
        (None, None) => true,
        (Some((n, e)), Some((v, f))) => v as nat == saturate_u32(n) && e == f,
        _ => false,
    }
}

/// Precondition of `ends_in_a_number(&[u32]) -> bool`: step 1's assertion.
pub open spec fn ends_in_a_number_requires(input: Seq<u32>) -> bool {
    input.len() > 0
}

/// Contract for `ends_in_a_number(&[u32]) -> bool`: the ends in a number
/// checker.
pub open spec fn ends_in_a_number_ensures(input: Seq<u32>, output: bool) -> bool {
    output == ends_in_a_number(input)
}

/// Contract for `ipv4_parser(&[u32]) -> Option<u32>`: the IPv4 parser.
pub open spec fn ipv4_parser_ensures(input: Seq<u32>, output: Option<u32>) -> bool {
    match output {
        Some(a) => ipv4_parser(input) == Some(a as nat),
        None => ipv4_parser(input) is None,
    }
}

/// Contract for `ipv6_parser(&[u32]) -> Option<[u16; 8]>`: the IPv6
/// parser.
pub open spec fn ipv6_parser_ensures(input: Seq<u32>, output: Option<Seq<u16>>) -> bool {
    match output {
        Some(a) => ipv6_parser(input) == Some(pieces_view(a)),
        None => ipv6_parser(input) is None,
    }
}

/// Precondition of `opaque_host_parser(&[u32]) -> Option<Vec<u32>>`: the
/// input is a scalar value string.
pub open spec fn opaque_host_parser_requires(input: Seq<u32>) -> bool {
    clazel_encoding::utf8::spec::all_scalar_values(input)
}

/// Contract for `opaque_host_parser(&[u32]) -> Option<Vec<u32>>`: the
/// opaque-host parser.
pub open spec fn opaque_host_parser_ensures(input: Seq<u32>, output: Option<Seq<u32>>) -> bool {
    output == opaque_host_parser(input)
}

/// The host parser reaches step 3 (and so the domain parser, step 6) on
/// `input`: it neither starts with U+005B ([) nor is opaque.
pub open spec fn reaches_domain_parser(input: Seq<u32>, is_opaque: bool) -> bool {
    !is_opaque && !(input.len() > 0 && input[0] == 0x5B)
}

/// The string host parser step 5 computes, "domain", which step 6 passes
/// to the domain parser.
pub open spec fn host_parser_domain(input: Seq<u32>) -> Seq<u32> {
    clazel_encoding::utf8::spec::utf8_decode_without_bom(clazel_percent::spec::percent_decode_string(input))
}

/// What `host_parser_start` returns, viewed.
pub enum HostParserStart {
    /// The host parser's result, which does not involve the domain parser.
    Done(Option<Host>),
    /// The host parser reaches step 6 with this "domain".
    Domain(Seq<u32>),
}

/// Precondition of `host_parser_start(&[u32], bool)`: the input is a
/// scalar value string, and step 3's assertion holds if it is reached.
pub open spec fn host_parser_start_requires(input: Seq<u32>, is_opaque: bool) -> bool {
    clazel_encoding::utf8::spec::all_scalar_values(input) && (is_opaque || input.len() > 0)
}

/// Contract for `host_parser_start(&[u32], bool)`: either the host
/// parser's result for every domain parser, or the "domain" its step 6
/// passes to the domain parser.
pub open spec fn host_parser_start_ensures(input: Seq<u32>, is_opaque: bool, output: HostParserStart) -> bool {
    match output {
        HostParserStart::Done(h) => !reaches_domain_parser(input, is_opaque)
            && forall|dp: DomainParser| #[trigger] host_parser(input, is_opaque, dp) == h,
        HostParserStart::Domain(d) => reaches_domain_parser(input, is_opaque) && d == host_parser_domain(input),
    }
}

/// Precondition of `host_parser_finish(Ghost(input), Ghost(is_opaque),
/// Ghost(domain), Option<&[u32]>)`: the host parser reaches step 6 on
/// `input` with `domain`, and the domain parser's result, if not failure,
/// is non-empty (§3.3 step 7 returns failure otherwise; the ends in a
/// number checker asserts it).
pub open spec fn host_parser_finish_requires(input: Seq<u32>, is_opaque: bool, domain: Seq<u32>, ascii_domain: Option<Seq<u32>>) -> bool {
    input.len() > 0 && reaches_domain_parser(input, is_opaque) && domain == host_parser_domain(input) && (
    ascii_domain matches Some(a) ==> a.len() > 0)
}

/// Contract for `host_parser_finish`: for every domain parser that returns
/// `ascii_domain` on `domain`, the host parser's result.
pub open spec fn host_parser_finish_ensures(input: Seq<u32>, is_opaque: bool, domain: Seq<u32>, ascii_domain: Option<Seq<u32>>, output: Option<Host>) -> bool {
    forall|dp: DomainParser| dp(domain, false) == ascii_domain ==> #[trigger] host_parser(input, is_opaque, dp) == output
}

/// The URL §3.3 domain parser, `clazel-idna`'s `domain_parser`, as the
/// [`DomainParser`] that host parser step 6 runs.
pub open spec fn url_domain_parser() -> DomainParser {
    |domain: Seq<u32>, be_strict: bool| clazel_idna::uts46::spec::domain_parser(domain, be_strict)
}

/// Precondition of `host_parser_full(&[u32], bool)`: the same as
/// `host_parser_start`'s.
pub open spec fn host_parser_full_requires(input: Seq<u32>, is_opaque: bool) -> bool {
    host_parser_start_requires(input, is_opaque)
}

/// Contract for `host_parser_full(&[u32], bool) -> Option<ParsedHost>`: the
/// whole host parser (steps 1 to 9), with step 6 running the real domain
/// parser.
pub open spec fn host_parser_full_ensures(input: Seq<u32>, is_opaque: bool, output: Option<Host>) -> bool {
    output == host_parser(input, is_opaque, url_domain_parser())
}

/// Contract for `ipv4_serializer(u32) -> Vec<u32>`: the IPv4 serializer.
pub open spec fn ipv4_serializer_ensures(address: u32, output: Seq<u32>) -> bool {
    output == ipv4_serializer(address as nat)
}

/// Contract for `ipv6_serializer(&[u16; 8]) -> Vec<u32>`: the IPv6
/// serializer.
pub open spec fn ipv6_serializer_ensures(address: Seq<u16>, output: Seq<u32>) -> bool {
    output == ipv6_serializer(pieces_view(address))
}

/// Contract for `ParsedHost::serialize(&self) -> Vec<u32>`: the host
/// serializer.
pub open spec fn host_serializer_ensures(host: Host, output: Seq<u32>) -> bool {
    output == host_serializer(host)
}

} // verus!
