//! Host parsing conformance (docs/phases/phase-1.md item 1.9).
//!
//! The proofs show the implementation equals `spec.rs`, and
//! `independent.rs` shows where the spec equals RFC 3986, RFC 4291 and RFC
//! 5952. This file checks both against the outside world:
//!
//! 1. The host rows of WPT `url/resources/urltestdata.json` and the rows of
//!    `url/resources/toascii.json`, converted by `cargo xtask testdata`
//!    (`tests/data/wpt-url-hosts/SOURCE.md` says which rows and why). Each
//!    case runs the host parser on the host string and compares the
//!    serialized host with the row's `hostname` (or failure).
//! 2. A differential test against Rust's `std::net::Ipv4Addr` and
//!    `std::net::Ipv6Addr` parsers and `Display`, on the strings where the
//!    standards agree.
//!
//! The host parser under test is `host_parser_full`: URL §3.5 steps 1 to 9,
//! with step 6 running `clazel-idna`'s URL §3.3 domain parser (UTS #46
//! ToASCII), so the rows whose domain is not ASCII pass through the real
//! thing. No row is an expected failure.

use clazel_url::host::ipv4::ipv4_parser;
use clazel_url::host::ipv6::ipv6_parser;
use clazel_url::host::parse::host_parser_full;
use clazel_url::host::record::ParsedHost;
use clazel_url::host::serialize::{ipv4_serializer, ipv6_serializer};
use std::net::{Ipv4Addr, Ipv6Addr};

/// One converted WPT case.
struct Case {
    name: &'static str,
    /// The string the URL parser passes to the host parser.
    input: &'static [u32],
    /// The host parser's isOpaque (the URL is not special).
    opaque: bool,
    /// The serialized host, or `None` for failure.
    expected: Option<&'static [u32]>,
}

// `const URLTESTDATA: &[Case]` and `const TOASCII: &[Case]`, generated
// from the vendored WPT files.
include!("generated/wpt_url_hosts.rs");

/// Host parse then serialize: the serialized host, or `None` for failure.
fn host_parse_serialize(input: &[u32], opaque: bool) -> Option<Vec<u32>> {
    host_parser_full(input, opaque).map(|h: ParsedHost| h.serialize())
}

fn string(v: &[u32]) -> String {
    v.iter()
        .map(|&c| char::from_u32(c).unwrap_or(char::REPLACEMENT_CHARACTER))
        .collect()
}

fn scalars(s: &str) -> Vec<u32> {
    s.chars().map(u32::from).collect()
}

/// Runs one suite and prints its summary line.
fn run_suite(suite: &str, cases: &[Case]) {
    let mut failures = Vec::new();
    let mut passed = 0usize;
    for case in cases {
        let got = host_parse_serialize(case.input, case.opaque);
        if got.as_deref() == case.expected {
            passed = passed.saturating_add(1);
        } else {
            failures.push(format!(
                "{}: got {:?}, expected {:?}",
                case.name,
                got.as_deref().map(string),
                case.expected.map(string)
            ));
        }
    }
    // Summary line for the README table (unit: a case); format in
    // xtask/src/conformance.rs.
    println!(
        "clazel-conformance: suite=\"{suite}\" pass={passed} xfail=0 fail={} total={}",
        cases.len().saturating_sub(passed),
        cases.len()
    );
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

#[test]
fn wpt_urltestdata_hosts() {
    run_suite("WPT url/ urltestdata.json hosts", URLTESTDATA);
}

#[test]
fn wpt_toascii() {
    run_suite("WPT url/ toascii.json", TOASCII);
}

// ---------------------------------------------------------------------
// Differential tests against std::net.
// ---------------------------------------------------------------------

/// A small deterministic generator (64-bit LCG, Knuth's constants).
struct Lcg(u64);

impl Lcg {
    fn next(&mut self) -> u64 {
        self.0 = self
            .0
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        self.0 >> 16
    }

    fn below(&mut self, n: u64) -> u64 {
        self.next().checked_rem(n).unwrap_or(0)
    }
}

fn samples(full: u64, miri: u64) -> u64 {
    if cfg!(miri) { miri } else { full }
}

/// A random address whose pieces are often 0, so that "::" is common.
fn random_ipv6(rng: &mut Lcg) -> [u16; 8] {
    let mut a = [0u16; 8];
    for p in &mut a {
        *p = match rng.below(6) {
            0..=2 => 0,
            3 => 1,
            4 => 0xFFFF,
            _ => u16::try_from(rng.below(0x1_0000)).unwrap_or(0),
        };
    }
    a
}

/// IPv4 serializer against `Ipv4Addr`'s `Display`: the same text for every
/// address tried (both write four decimal bytes without leading zeros).
#[test]
fn differential_ipv4_serializer() {
    let mut rng = Lcg(1);
    let mut addresses: Vec<u32> = vec![0, 1, 255, 256, 0x7F00_0001, 0xFFFF_FFFF, 0x0A0B_0C0D];
    for _ in 0..samples(200_000, 200) {
        addresses.push(u32::try_from(rng.below(0x1_0000_0000)).unwrap_or(0));
    }
    for a in addresses {
        assert_eq!(
            string(&ipv4_serializer(a)),
            Ipv4Addr::from(a).to_string(),
            "{a:#x}"
        );
    }
}

/// IPv4 parser against `Ipv4Addr::from_str`, which accepts exactly RFC
/// 3986's `IPv4address` (four decimal bytes, no leading zeros): wherever it
/// accepts a string, the URL Standard's IPv4 parser gives the same
/// address (`lemma_ipv4address_parses` proves this for the spec). Every
/// string up to 6 code points over "0123456789.x" is tried, plus random
/// longer ones.
#[test]
fn differential_ipv4_parser() {
    let alphabet: Vec<char> = "0123456789.x".chars().collect();
    let mut inputs: Vec<String> = vec![String::new()];
    let mut frontier: Vec<String> = vec![String::new()];
    for _ in 0..samples(6, 3) {
        let mut next = Vec::new();
        for s in &frontier {
            for &c in &alphabet {
                let mut t = s.clone();
                t.push(c);
                next.push(t);
            }
        }
        inputs.extend(next.iter().cloned());
        frontier = next;
    }
    let mut rng = Lcg(2);
    for _ in 0..samples(200_000, 200) {
        let mut parts = Vec::new();
        for _ in 0..4 {
            parts.push(rng.below(300).to_string());
        }
        inputs.push(parts.join("."));
    }
    let mut agreed = 0usize;
    for s in &inputs {
        let ours = ipv4_parser(&scalars(s));
        if let Ok(theirs) = s.parse::<Ipv4Addr>() {
            assert_eq!(ours, Some(u32::from(theirs)), "{s:?}");
            agreed = agreed.saturating_add(1);
        }
    }
    assert!(
        agreed > usize::try_from(samples(1000, 50)).unwrap_or(0),
        "too few strings in the common class: {agreed}"
    );
}

/// IPv6 serializer against `Ipv6Addr`'s `Display` (RFC 5952): the same
/// text, except where `Display` writes an embedded IPv4 address in dotted
/// form (RFC 5952 §5), which the URL Standard never does.
#[test]
fn differential_ipv6_serializer() {
    let mut rng = Lcg(3);
    let mut compared = 0usize;
    for _ in 0..samples(200_000, 200) {
        let a = random_ipv6(&mut rng);
        let theirs = Ipv6Addr::from(a).to_string();
        if theirs.contains('.') {
            continue;
        }
        assert_eq!(string(&ipv6_serializer(&a)), theirs, "{a:x?}");
        compared = compared.saturating_add(1);
    }
    assert!(compared > 100, "too few addresses compared: {compared}");
}

/// The text forms RFC 4291 §2.2 allows for `a`: each piece in hex with 0
/// to 3 leading zeros and random case, optionally one run of zero pieces
/// replaced by "::", and optionally the last two pieces as an IPv4 address.
fn random_text(rng: &mut Lcg, a: &[u16; 8]) -> String {
    let piece = |rng: &mut Lcg, p: u16| {
        let mut t = format!("{p:x}");
        for _ in 0..rng.below(4) {
            if t.len() < 4 {
                t.insert(0, '0');
            }
        }
        if rng.below(2) == 0 {
            t.to_uppercase()
        } else {
            t
        }
    };
    let ipv4_tail = rng.below(3) == 0;
    let units: Vec<String> = if ipv4_tail {
        let mut u: Vec<String> = a.iter().take(6).map(|&p| piece(rng, p)).collect();
        let [b0, b1] = a[6].to_be_bytes();
        let [b2, b3] = a[7].to_be_bytes();
        u.push(format!("{b0}.{b1}.{b2}.{b3}"));
        u
    } else {
        a.iter().map(|&p| piece(rng, p)).collect()
    };
    let groups: Vec<bool> = a.iter().map(|&p| p == 0).collect();
    // A run of zero pieces to compress, among those fully before the tail.
    let limit = if ipv4_tail { 6 } else { 8 };
    let start = usize::try_from(rng.below(8)).unwrap_or(0);
    let mut end = start;
    while end < limit && groups.get(end).copied().unwrap_or(false) {
        end = end.saturating_add(1);
    }
    if end > start && rng.below(4) != 0 {
        let len = usize::try_from(rng.below(u64::try_from(end.saturating_sub(start)).unwrap_or(1)))
            .unwrap_or(0)
            .saturating_add(1);
        let stop = start.saturating_add(len);
        let before = units.get(..start).unwrap_or(&[]).join(":");
        let after = units.get(stop..).unwrap_or(&[]).join(":");
        return format!("{before}::{after}");
    }
    units.join(":")
}

/// IPv6 parser against `Ipv6Addr::from_str`: wherever it accepts a string,
/// the URL Standard's IPv6 parser gives the same address
/// (`lemma_ipv6address_parses` proves this for RFC 3986's grammar). The
/// strings are random text forms of random addresses, and random strings
/// over the IPv6 alphabet.
#[test]
fn differential_ipv6_parser() {
    let mut rng = Lcg(4);
    let mut inputs = Vec::new();
    for _ in 0..samples(200_000, 200) {
        let a = random_ipv6(&mut rng);
        inputs.push(random_text(&mut rng, &a));
    }
    let alphabet: Vec<char> = "0123456789abcdefABCDEF:.".chars().collect();
    for _ in 0..samples(300_000, 300) {
        let len = rng.below(16);
        let s: String = (0..len)
            .map(|_| {
                let k = usize::try_from(rng.below(24)).unwrap_or(0);
                alphabet.get(k).copied().unwrap_or(':')
            })
            .collect();
        inputs.push(s);
    }
    let mut agreed = 0usize;
    let mut only_ours = Vec::new();
    for s in &inputs {
        let ours = ipv6_parser(&scalars(s));
        match s.parse::<Ipv6Addr>() {
            Ok(theirs) => {
                assert_eq!(ours, Some(theirs.segments()), "{s:?}");
                agreed = agreed.saturating_add(1);
            }
            Err(_) => {
                if ours.is_some() {
                    only_ours.push(s.clone());
                }
            }
        }
    }
    assert!(
        agreed > 100_000 || cfg!(miri),
        "too few strings in the common class: {agreed}"
    );
    assert!(
        only_ours.is_empty(),
        "the URL Standard accepts, std rejects: {:?}",
        only_ours.get(..10)
    );
}
