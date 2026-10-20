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
//! **The domain parser (URL §3.3) is item 1.8.** The host parser is shipped
//! as `host_parser_start` and `host_parser_finish` around it. For an ASCII
//! "domain" (host parser step 5's result), the domain parser with beStrict
//! false does not depend on UTS #46: step 2's ToASCII result is only a
//! validation error, step 5 sets result to the domain lowercased, and
//! steps 7 and 8 fail on the empty string and on forbidden domain code
//! points. [`ascii_domain_parser`] is exactly those steps, for this test
//! only. Rows whose domain is not ASCII need ToASCII itself: they are the
//! expected failures listed in [`EXPECTED_FAILURES`].

use clazel_url::host::ipv4::ipv4_parser;
use clazel_url::host::ipv6::ipv6_parser;
use clazel_url::host::parse::{HostParserStart, host_parser_finish, host_parser_start};
use clazel_url::host::record::ParsedHost;
use clazel_url::host::serialize::{ipv4_serializer, ipv6_serializer};
use std::net::{Ipv4Addr, Ipv6Addr};
use vstd::prelude::Ghost;

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

/// Cases whose domain (host parser step 5) is not ASCII, so the domain
/// parser needs UTS #46 ToASCII: they wait on item 1.8 (`clazel-idna`).
const EXPECTED_FAILURES: &[&str] = &[
    "a†-- (using URL)",
    "-† (using URL)",
    "-x.ß (using URL)",
    "x-.ß (using URL)",
    "x..ß (using URL)",
    "xn--a.ß (using URL)",
    "xn--tešla (using URL)",
    "xn--zca.ß (using URL)",
    "ab--c.ß (using URL)",
    "\u{200d}.example (using URL)",
    "يa (using URL)",
    "ශ\u{dca}\u{200d}ර\u{dd3} (using URL)",
    "نامه\u{200c}ای (using URL)",
    "�.com (using URL)",
    "x01234567890123456789012345678901234567890123456789012345678901† (using URL)",
    "x01234567890123456789012345678901234567890123456789012345678901x.ß (using URL)",
    "01234567890123456789012345678901234567890123456789.01234567890123456789012345678901234567890123456789.01234567890123456789012345678901234567890123456789.01234567890123456789012345678901234567890123456789.0123456789012345678901234567890123456789012345678.ß (using URL)",
    "a\u{ad}b (using URL)",
    "≠ (using URL)",
    "≮ (using URL)",
    "≯ (using URL)",
    "=\u{338} (using URL)",
    "<\u{338} (using URL)",
    ">\u{338} (using URL)",
    "=\u{ad}\u{338} (using URL)",
    "<\u{ad}\u{338} (using URL)",
    ">\u{ad}\u{338} (using URL)",
    "faß.de (using URL)",
    "βόλος.com (using URL)",
    "ශ\u{dca}\u{200d}ර\u{dd3}.com (using URL)",
    "نامه\u{200c}ای.com (using URL)",
    "www.looĸout.net (using URL)",
    "ᗯᗯᗯ.lookout.net (using URL)",
    "www.lookout.сом (using URL)",
    "www‥lookout.net (using URL)",
    "www.lookout‧net (using URL)",
    "www.lookout.net⩴80 (using URL)",
    "www\u{a0}.lookout.net (using URL)",
    "\u{1680}lookout.net (using URL)",
    "look\u{6dd}out.net (using URL)",
    "look\u{180e}out.net (using URL)",
    "look\u{2060}out.net (using URL)",
    "look\u{feff}out.net (using URL)",
    "look\u{1fffe}out.net (using URL)",
    "look\u{fffa}out.net (using URL)",
    "look⿰out.net (using URL)",
    "look\u{341}out.net (using URL)",
    "look\u{202e}out.net (using URL)",
    "look\u{206b}out.net (using URL)",
    "look\u{e0001}out.net (using URL)",
    "look\u{e0020}out.net (using URL)",
    "look־out.net (using URL)",
    "Bücher.de (using URL)",
    "♥.net (using URL)",
    "\u{378}.net (using URL)",
    "Ӏ.com (using URL)",
    "㛼.com (using URL)",
    "Ↄ.com (using URL)",
    "look\u{34f}out.net (using URL)",
    "ড়.com (using URL)",
    "ẞ.com (using URL)",
    "ẞ.foo.com (using URL)",
    "foo\u{300}.bar.com (using URL)",
    "Parsing: <http://GOO\u{a0}\u{3000}goo.com> against <http://other.com/>",
    "Parsing: <http://GOO\u{200b}\u{2060}\u{feff}goo.com> against <http://other.com/>",
    "Parsing: <http://www.foo。bar.com> against <http://other.com/>",
    "Parsing: <http://\u{fdd0}zyx.com> against <http://other.com/>",
    "Parsing: <http://%ef%b7%90zyx.com> against <http://other.com/>",
    "Parsing: <https://�> without base",
    "Parsing: <https://%EF%BF%BD> without base",
    "Parsing: <http://Ｇｏ.com> against <http://other.com/>",
    "Parsing: <http://％４１.com> against <http://other.com/>",
    "Parsing: <http://%ef%bc%85%ef%bc%94%ef%bc%91.com> against <http://other.com/>",
    "Parsing: <http://％００.com> against <http://other.com/>",
    "Parsing: <http://%ef%bc%85%ef%bc%90%ef%bc%90.com> against <http://other.com/>",
    "Parsing: <http://你好你好> against <http://other.com/>",
    "Parsing: <https://faß.ExAmPlE/> without base",
    "Parsing: <http://０Ｘｃ０．０２５０．０１> against <http://other.com/>",
    "Parsing: <ftp://example.com%80/> without base",
    "Parsing: <ftp://example.com%A0/> without base",
    "Parsing: <https://example.com%80/> without base",
    "Parsing: <https://example.com%A0/> without base",
    "Parsing: <ftp://%e2%98%83> without base",
    "Parsing: <https://%e2%98%83> without base",
    "Parsing: <http://💩.123/> without base",
    "Parsing: <https://\u{ffff}y> without base",
    "Parsing: <https://a%C2%ADb/> without base",
    "Parsing: <https://\u{ad}/> without base",
    "Parsing: <https://%C2%AD/> without base",
];

/// A forbidden domain code point (URL §3.2): a forbidden host code point,
/// a C0 control, U+0025 (%), or U+007F DELETE.
fn is_forbidden_domain_code_point(c: u32) -> bool {
    matches!(
        c,
        0x00 | 0x09
            | 0x0A
            | 0x0D
            | 0x20
            | 0x23
            | 0x2F
            | 0x3A
            | 0x3C
            | 0x3E
            | 0x3F
            | 0x40
            | 0x5B
            | 0x5C
            | 0x5D
            | 0x5E
            | 0x7C
    ) || c <= 0x1F
        || c == 0x25
        || c == 0x7F
}

/// URL §3.3 "domain parser" with beStrict false, for an ASCII `domain`
/// only (see the module comment): steps 5, 7, 8 and 9.
fn ascii_domain_parser(domain: &[u32]) -> Option<Vec<u32>> {
    // 5. "If domain is an ASCII string, then set result to domain,
    //    lowercased."
    let result: Vec<u32> = domain
        .iter()
        .map(|&c| {
            if (0x41..=0x5A).contains(&c) {
                c | 0x20
            } else {
                c
            }
        })
        .collect();
    // 7. "If result is the empty string, then return failure."
    // 8. "If result contains a forbidden domain code point, then return
    //    failure."
    if result.is_empty() || result.iter().any(|&c| is_forbidden_domain_code_point(c)) {
        return None;
    }
    // 9. "Return result."
    Some(result)
}

enum Outcome {
    /// The serialized host, or `None` for failure.
    Host(Option<Vec<u32>>),
    /// The domain is not ASCII: the domain parser needs ToASCII (item 1.8).
    NeedsIdna,
}

fn host_parse_serialize(input: &[u32], opaque: bool) -> Outcome {
    let host = match host_parser_start(input, opaque) {
        HostParserStart::Done(h) => h,
        HostParserStart::Domain(domain) => {
            if domain.iter().any(|&c| c > 0x7F) {
                return Outcome::NeedsIdna;
            }
            let ascii = ascii_domain_parser(&domain);
            host_parser_finish(
                Ghost::assume_new(),
                Ghost::assume_new(),
                Ghost::assume_new(),
                ascii,
            )
        }
    };
    Outcome::Host(host.map(|h: ParsedHost| h.serialize()))
}

fn string(v: &[u32]) -> String {
    v.iter()
        .map(|&c| char::from_u32(c).unwrap_or(char::REPLACEMENT_CHARACTER))
        .collect()
}

fn scalars(s: &str) -> Vec<u32> {
    s.chars().map(u32::from).collect()
}

/// What one suite gives: the number of passes, the names of the cases
/// that need IDNA, and the failures.
fn evaluate(cases: &[Case]) -> (usize, Vec<&'static str>, Vec<String>) {
    let mut failures = Vec::new();
    let mut needs_idna = Vec::new();
    let mut passed = 0usize;
    for case in cases {
        match host_parse_serialize(case.input, case.opaque) {
            Outcome::NeedsIdna => needs_idna.push(case.name),
            Outcome::Host(got) => {
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
        }
    }
    (passed, needs_idna, failures)
}

/// Runs one suite and prints its summary line.
fn run_suite(suite: &str, cases: &[Case]) {
    let (passed, needs_idna, mut failures) = evaluate(cases);
    let unlisted: Vec<&str> = needs_idna
        .iter()
        .filter(|n| !EXPECTED_FAILURES.contains(n))
        .copied()
        .collect();
    let xfail = needs_idna.len().saturating_sub(unlisted.len());
    for n in &unlisted {
        failures.push(format!(
            "{n:?}: needs IDNA, but is not listed in EXPECTED_FAILURES"
        ));
    }
    // Summary line for the README table (unit: a case); format in
    // xtask/src/conformance.rs.
    println!(
        "clazel-conformance: suite=\"{suite}\" pass={passed} xfail={xfail} fail={} total={}",
        cases.len().saturating_sub(passed).saturating_sub(xfail),
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

/// Every name in `EXPECTED_FAILURES` is a case that needs IDNA.
#[test]
fn expected_failures_are_current() {
    let mut all = evaluate(URLTESTDATA).1;
    all.extend(evaluate(TOASCII).1);
    for name in EXPECTED_FAILURES {
        assert!(
            all.contains(name),
            "{name}: listed in EXPECTED_FAILURES but does not need IDNA"
        );
    }
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
