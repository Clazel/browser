//! The executable opaque-host parser and host parser (URL §3.5), proven to
//! meet [`super::contract`]. The step comments live in [`super::spec`].
//!
//! The host parser is two functions until item 1.8 provides the domain
//! parser (URL §3.3) that its step 6 runs: [`host_parser_start`] runs steps
//! 1 to 5, and [`host_parser_finish`] steps 7 to 9 on the domain parser's
//! result. See [`super::contract`].

use super::record::{ParsedHost, at32};
#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Whether `s` contains a forbidden host code point (URL §3.2).
fn contains_forbidden_host_code_point(s: &[u32]) -> (r: bool)
    ensures
        r == contains_forbidden_host_code_point_from(s@, 0),
{
    let mut i: usize = 0;
    while i < s.len()
        invariant
            i <= s.len(),
            contains_forbidden_host_code_point_from(s@, 0) == contains_forbidden_host_code_point_from(s@, i as nat),
        decreases s.len() - i,
    {
        let c = at32(s, i);
        if c == 0x00 || c == 0x09 || c == 0x0A || c == 0x0D || c == 0x20 || c == 0x23 || c == 0x2F || c == 0x3A
            || c == 0x3C || c == 0x3E || c == 0x3F || c == 0x40 || c == 0x5B || c == 0x5C || c == 0x5D || c
            == 0x5E || c == 0x7C {
            return true;
        }
        i = i.saturating_add(1);
    }
    false
}

/// The opaque-host parser (URL §3.5).
pub fn opaque_host_parser(input: &[u32]) -> (output: Option<Vec<u32>>)
    requires
        super::contract::opaque_host_parser_requires(input@),
    ensures
        super::contract::opaque_host_parser_ensures(
            input@,
            super::record::opt_seq(output),
        ),
{
    if contains_forbidden_host_code_point(input) {
        None
    } else {
        Some(
            clazel_percent::encode::utf8_percent_encode(
                input,
                clazel_percent::spec::PercentEncodeSet::C0Control,
            ),
        )
    }
}

/// What [`host_parser_start`] returns.
pub enum HostParserStart {
    /// The host parser's result, which does not involve the domain parser.
    Done(Option<ParsedHost>),
    /// The host parser reaches step 6 with this "domain": pass it to the
    /// domain parser, and its result to [`host_parser_finish`].
    Domain(Vec<u32>),
}

impl View for HostParserStart {
    type V = super::contract::HostParserStart;

    open spec fn view(&self) -> super::contract::HostParserStart {
        match self {
            HostParserStart::Done(h) => super::contract::HostParserStart::Done(super::record::option_view(*h)),
            HostParserStart::Domain(d) => super::contract::HostParserStart::Domain(d@),
        }
    }
}

/// The host parser (URL §3.5), steps 1 to 5.
pub fn host_parser_start(input: &[u32], is_opaque: bool) -> (output: HostParserStart)
    requires
        super::contract::host_parser_start_requires(input@, is_opaque),
    ensures
        super::contract::host_parser_start_ensures(input@, is_opaque, output@),
{
    if !input.is_empty() && at32(input, 0) == 0x5B {
        // Never saturates: input.len() > 0.
        let last = input.len().saturating_sub(1);
        if at32(input, last) != 0x5D {
            let output = HostParserStart::Done(None);
            assert forall|dp: DomainParser| #[trigger] host_parser(input@, is_opaque, dp) == super::record::option_view(None) by {}
            return output;
        }
        // input.len() >= 2: its first code point is [ and its last ].
        let inner = vstd::slice::slice_subrange(input, 1, last);
        assert(inner@ =~= input@.subrange(1, input@.len() - 1));
        match super::ipv6::ipv6_parser(inner) {
            Some(address) => {
                let result = Some(ParsedHost::Ipv6(address));
                assert forall|dp: DomainParser| #[trigger] host_parser(input@, is_opaque, dp) == super::record::option_view(result) by {}
                HostParserStart::Done(result)
            },
            None => {
                assert forall|dp: DomainParser| #[trigger] host_parser(input@, is_opaque, dp) == super::record::option_view(None) by {}
                HostParserStart::Done(None)
            },
        }
    } else if is_opaque {
        let result = match opaque_host_parser(input) {
            Some(s) => if s.is_empty() {
                Some(ParsedHost::Empty)
            } else {
                Some(ParsedHost::Opaque(s))
            },
            None => None,
        };
        assert forall|dp: DomainParser| #[trigger] host_parser(input@, is_opaque, dp) == super::record::option_view(result) by {}
        HostParserStart::Done(result)
    } else {
        let bytes = clazel_percent::decode::percent_decode_string(input);
        let domain = clazel_encoding::utf8::decode::decode_without_bom(bytes.as_slice());
        HostParserStart::Domain(domain)
    }
}

/// Host parser steps 7 to 9 on the domain parser's result.
fn finish_steps(ascii_domain: Option<Vec<u32>>) -> (output: Option<ParsedHost>)
    requires
        ascii_domain matches Some(a) ==> a.len() > 0,
    ensures
        super::record::option_view(output) == match super::record::opt_seq(ascii_domain) {
            None => None,
            Some(a) => if ends_in_a_number(a) {
                match super::spec::ipv4_parser(a) {
                    Some(address) => Some(Host::Ipv4(address)),
                    None => None,
                }
            } else {
                Some(Host::Domain(a))
            },
        },
{
    let ascii = ascii_domain?;
    if !super::ipv4::ends_in_a_number(ascii.as_slice()) {
        return Some(ParsedHost::Domain(ascii));
    }
    let address = super::ipv4::ipv4_parser(ascii.as_slice())?;
    Some(ParsedHost::Ipv4(address))
}

/// The host parser (URL §3.5), steps 7 to 9, given `ascii_domain`, the
/// domain parser's result on the "domain" [`host_parser_start`] returned
/// for `input`.
pub fn host_parser_finish(
    Ghost(input): Ghost<Seq<u32>>,
    Ghost(is_opaque): Ghost<bool>,
    Ghost(domain): Ghost<Seq<u32>>,
    ascii_domain: Option<Vec<u32>>,
) -> (output: Option<ParsedHost>)
    requires
        super::contract::host_parser_finish_requires(
            input,
            is_opaque,
            domain,
            super::record::opt_seq(ascii_domain),
        ),
    ensures
        super::contract::host_parser_finish_ensures(
            input,
            is_opaque,
            domain,
            super::record::opt_seq(ascii_domain),
            super::record::option_view(output),
        ),
{
    let ghost ascii_view = super::record::opt_seq(ascii_domain);
    let output = finish_steps(ascii_domain);
    assert forall|dp: DomainParser| dp(domain, false) == ascii_view implies #[trigger] host_parser(input, is_opaque, dp)
        == super::record::option_view(output) by {}
    output
}

} // verus!

#[cfg(test)]
mod tests {
    use super::{HostParserStart, host_parser_finish, host_parser_start};
    use crate::host::record::ParsedHost;
    use vstd::prelude::Ghost;

    fn scalars(s: &str) -> Vec<u32> {
        s.chars().map(u32::from).collect()
    }

    fn string(v: &[u32]) -> String {
        v.iter().filter_map(|&c| char::from_u32(c)).collect()
    }

    /// Host parse then serialize, with an ASCII-only stand-in for the
    /// domain parser (the real one is item 1.8): lowercase, as URL §3.3
    /// step 5 does for ASCII input with beStrict false.
    fn roundtrip(input: &str, is_opaque: bool) -> Option<String> {
        let host = match host_parser_start(&scalars(input), is_opaque) {
            HostParserStart::Done(h) => h,
            HostParserStart::Domain(d) => {
                if d.iter().any(|&c| c > 0x7F) {
                    return None;
                }
                let ascii: Vec<u32> = d
                    .iter()
                    .map(|&c| {
                        if (0x41..=0x5A).contains(&c) {
                            c | 0x20
                        } else {
                            c
                        }
                    })
                    .collect();
                host_parser_finish(
                    Ghost::assume_new(),
                    Ghost::assume_new(),
                    Ghost::assume_new(),
                    Some(ascii),
                )
            }
        };
        host.map(|h: ParsedHost| string(&h.serialize()))
    }

    #[test]
    fn standard_examples() {
        // URL §3, the parse-serialize table (the rows without IDNA).
        assert_eq!(
            roundtrip("EXAMPLE.COM", false).as_deref(),
            Some("example.com")
        );
        assert_eq!(
            roundtrip("EXAMPLE.COM", true).as_deref(),
            Some("EXAMPLE.COM")
        );
        assert_eq!(
            roundtrip("example%2Ecom", true).as_deref(),
            Some("example%2Ecom")
        );
        assert_eq!(
            roundtrip("faß.example", true).as_deref(),
            Some("fa%C3%9F.example")
        );
        assert_eq!(roundtrip("0", false).as_deref(), Some("0.0.0.0"));
        assert_eq!(roundtrip("0", true).as_deref(), Some("0"));
        assert_eq!(roundtrip("%30", false).as_deref(), Some("0.0.0.0"));
        assert_eq!(roundtrip("%30", true).as_deref(), Some("%30"));
        assert_eq!(roundtrip("0x", false).as_deref(), Some("0.0.0.0"));
        assert_eq!(
            roundtrip("0xffffffff", false).as_deref(),
            Some("255.255.255.255")
        );
        assert_eq!(roundtrip("[0:0::1]", false).as_deref(), Some("[::1]"));
        assert_eq!(roundtrip("[0:0::1]", true).as_deref(), Some("[::1]"));
        assert_eq!(roundtrip("[0:0::1%5D", false), None);
        assert_eq!(roundtrip("[0:0::%31]", true), None);
        assert_eq!(roundtrip("09", false), None);
        assert_eq!(roundtrip("09", true).as_deref(), Some("09"));
        assert_eq!(roundtrip("example.255", false), None);
        assert_eq!(
            roundtrip("example.255", true).as_deref(),
            Some("example.255")
        );
        assert_eq!(roundtrip("example^example", true), None);
    }
}
