//! Percent-encoding conformance (docs/phases/phase-1.md item 1.5).
//!
//! The proofs show the implementation equals `spec.rs`, and
//! `independent.rs` shows where the spec equals RFC 3986. This file checks
//! both against the outside world:
//!
//! 1. WPT `url/percent-encoding.window.js`, converted from the vendored
//!    files by `cargo xtask testdata` (`tests/data/wpt-url-percent-encoding/`):
//!    every case's fragment check (UTF-8, fragment set) and every UTF-8
//!    case's query check (special-query set). Query checks in other
//!    encodings are expected failures, listed by name below.
//! 2. A differential test against rust-url (`percent-encoding` 2.3.2 and
//!    `form_urlencoded` 1.2.2, the crates under Servo's and the `url`
//!    crate's URL parser): percent-decode over every input up to 2 bytes,
//!    every input up to 5 bytes over the bytes that matter to it, and
//!    random longer ones; UTF-8 percent-encode over every scalar value and
//!    random strings, for all eight sets. The sets come from outside this
//!    project: the five rust-url defines (copied from `url` 2.5.8), its
//!    `CONTROLS`, ECMA-262's `encodeURIComponent` for the component set
//!    (which URL §1.3 says it equals), and `form_urlencoded::byte_serialize`
//!    for application/x-www-form-urlencoded. Under Miri the samples are
//!    smaller.

use clazel_percent::decode::{percent_decode, percent_decode_string};
use clazel_percent::encode::{percent_encode, utf8_percent_encode, utf8_percent_encode_code_point};
use clazel_percent::spec::PercentEncodeSet;
use percent_encoding::{AsciiSet, CONTROLS, NON_ALPHANUMERIC};

/// One converted WPT case.
struct Case {
    name: &'static str,
    input: &'static [u32],
    encoding: &'static str,
    /// The expected `search`, without its "?".
    query: &'static str,
    /// The expected `hash`, without its "#" (always the UTF-8 output).
    fragment: &'static str,
}

// `const WPT: &[Case]`, generated from the vendored WPT files.
include!("generated/wpt_url_percent_encoding.rs");

/// WPT cases whose query check is expected to fail: "percent-encode after
/// encoding" is implemented for UTF-8 only (a modelling choice in
/// `spec.rs`). Their fragment checks still run.
const EXPECTED_FAILURES: &[&str] = &[
    "Input \u{2020} with encoding big5",
    "Input \u{2020} with encoding euc-kr",
    "Input \u{2020} with encoding windows-1252",
    "Input \u{e}A with encoding big5",
    "Input \u{e}A with encoding iso-2022-jp",
    "Input \u{203e}\\ with encoding iso-2022-jp",
    "Input \u{e5e5} with encoding gb18030",
    "Input \u{2212} with encoding shift_jis",
    "Input \u{a2} with encoding iso-8859-2",
];

fn string(v: &[u32]) -> String {
    v.iter()
        .map(|&c| char::from_u32(c).unwrap_or(char::REPLACEMENT_CHARACTER))
        .collect()
}

// ---------------------------------------------------------------------------
// 1. WPT
// ---------------------------------------------------------------------------

#[test]
fn wpt_url_percent_encoding() {
    let mut failures = Vec::new();
    let mut passed = 0usize;
    let mut expected_failures = 0usize;
    for case in WPT {
        assert!(
            case.input.iter().all(|&c| char::from_u32(c).is_some()),
            "{}: input is not a scalar value string",
            case.name
        );
        let fragment = string(&utf8_percent_encode(case.input, PercentEncodeSet::Fragment));
        if fragment == case.fragment {
            passed = passed.saturating_add(1);
        } else {
            failures.push(format!(
                "{} (fragment): got {fragment:?}, expected {:?}",
                case.name, case.fragment
            ));
        }
        if case.encoding == "utf-8" {
            let query = string(&utf8_percent_encode(
                case.input,
                PercentEncodeSet::SpecialQuery,
            ));
            if query == case.query {
                passed = passed.saturating_add(1);
            } else {
                failures.push(format!(
                    "{} (query): got {query:?}, expected {:?}",
                    case.name, case.query
                ));
            }
        } else if EXPECTED_FAILURES.contains(&case.name) {
            expected_failures = expected_failures.saturating_add(1);
        } else {
            failures.push(format!(
                "{}: not UTF-8, but not listed in EXPECTED_FAILURES",
                case.name
            ));
        }
    }
    for name in EXPECTED_FAILURES {
        if !WPT.iter().any(|c| c.name == *name && c.encoding != "utf-8") {
            failures.push(format!(
                "EXPECTED_FAILURES lists {name:?}, which is no such case"
            ));
        }
    }
    // Summary line for the README table (unit: a check, two
    // per case: fragment and query); format in xtask/src/conformance.rs.
    let total = WPT.len().saturating_mul(2);
    println!(
        "clazel-conformance: suite=\"WPT url/ percent-encoding\" pass={passed} xfail={expected_failures} fail={} total={total}",
        total
            .saturating_sub(passed)
            .saturating_sub(expected_failures)
    );
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

// ---------------------------------------------------------------------------
// 2. Differential
// ---------------------------------------------------------------------------

/// Deterministic SplitMix64, so a failure reproduces.
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ z.wrapping_shr(30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ z.wrapping_shr(27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ z.wrapping_shr(31)
    }

    fn below(&mut self, n: usize) -> usize {
        let n = u64::try_from(n).unwrap_or(u64::MAX);
        usize::try_from(self.next().checked_rem(n).unwrap_or(0)).unwrap_or(0)
    }

    /// Half the time a byte from `DECODE_EDGES`, otherwise any byte.
    fn edgy_byte(&mut self) -> u8 {
        if self.next() & 1 == 0 {
            DECODE_EDGES
                .get(self.below(DECODE_EDGES.len()))
                .copied()
                .unwrap_or(0)
        } else {
            self.next().to_le_bytes().first().copied().unwrap_or(0)
        }
    }

    /// A scalar value: often ASCII, sometimes from each UTF-8 length.
    fn scalar(&mut self) -> u32 {
        let limit = match self.below(4) {
            0 | 1 => 0x80,
            2 => 0x800,
            _ => 0x11_0000,
        };
        let c = u32::try_from(self.below(limit)).unwrap_or(0);
        if (0xD800..=0xDFFF).contains(&c) {
            0xFFFD
        } else {
            c
        }
    }
}

/// Bytes at the boundaries of percent-decode step 2.2's ranges, and "%".
const DECODE_EDGES: &[u8] = &[
    0x25, 0x2F, 0x30, 0x39, 0x3A, 0x40, 0x41, 0x46, 0x47, 0x60, 0x61, 0x66, 0x67, 0x00, 0x80, 0xFF,
];

/// Every byte string of exactly `len` bytes over `alphabet`.
fn all_of_len(alphabet: &[u8], len: usize) -> impl Iterator<Item = Vec<u8>> {
    let mut next = Some(vec![0usize; len]);
    std::iter::from_fn(move || {
        let digits = next.take()?;
        let out = digits
            .iter()
            .map(|&d| alphabet.get(d).copied().unwrap_or(0))
            .collect();
        let mut digits = digits;
        for d in digits.iter_mut().rev() {
            *d = d.saturating_add(1);
            if *d < alphabet.len() {
                next = Some(digits);
                return Some(out);
            }
            *d = 0;
        }
        Some(out)
    })
}

fn check_decode(inputs: impl Iterator<Item = Vec<u8>>) -> usize {
    let mut n = 0usize;
    for input in inputs {
        let ours = percent_decode(&input);
        let theirs: Vec<u8> = percent_encoding::percent_decode(&input).collect();
        assert_eq!(ours, theirs, "percent-decode {input:02X?}");
        n = n.saturating_add(1);
    }
    n
}

#[test]
fn differential_decode_short() {
    let all: Vec<u8> = (0..=255).collect();
    let max_full = if cfg!(miri) { 1 } else { 2 };
    let max_edges = if cfg!(miri) { 3 } else { 5 };
    let mut n = 0usize;
    for len in 0..=max_full {
        n = n.saturating_add(check_decode(all_of_len(&all, len)));
    }
    for len in max_full.saturating_add(1)..=max_edges {
        n = n.saturating_add(check_decode(all_of_len(DECODE_EDGES, len)));
    }
    println!("percent-decode agrees with percent-encoding 2.3.2 on {n} short inputs");
}

#[test]
fn differential_decode_longer() {
    let n = if cfg!(miri) { 20 } else { 100_000 };
    let mut rng = Rng(0x5EED_0105);
    let inputs = (0..n).map(|_| {
        let len = rng.below(40);
        (0..len).map(|_| rng.edgy_byte()).collect::<Vec<u8>>()
    });
    let checked = check_decode(inputs);
    // Percent-decode of a string is percent-decode of its UTF-8 encoding.
    for _ in 0..n {
        let len = rng.below(20);
        let s: Vec<u32> = (0..len)
            .map(|_| match rng.below(3) {
                0 => 0x25,
                1 => u32::from(rng.edgy_byte() & 0x7F),
                _ => rng.scalar(),
            })
            .collect();
        let text = string(&s);
        let theirs: Vec<u8> = percent_encoding::percent_decode_str(&text).collect();
        assert_eq!(percent_decode_string(&s), theirs, "percent-decode {text:?}");
    }
    println!("percent-decode agrees with percent-encoding 2.3.2 on {checked} random inputs");
}

// rust-url's sets, copied from `url` 2.5.8 `src/parser.rs`.

/// https://url.spec.whatwg.org/#fragment-percent-encode-set
const FRAGMENT: &AsciiSet = &CONTROLS.add(b' ').add(b'"').add(b'<').add(b'>').add(b'`');

/// https://url.spec.whatwg.org/#path-percent-encode-set
const PATH: &AsciiSet = &FRAGMENT.add(b'#').add(b'?').add(b'{').add(b'}');

/// https://url.spec.whatwg.org/#userinfo-percent-encode-set
const USERINFO: &AsciiSet = &PATH
    .add(b'/')
    .add(b':')
    .add(b';')
    .add(b'=')
    .add(b'@')
    .add(b'[')
    .add(b'\\')
    .add(b']')
    .add(b'^')
    .add(b'|');

// https://url.spec.whatwg.org/#query-state
const QUERY: &AsciiSet = &CONTROLS.add(b' ').add(b'"').add(b'#').add(b'<').add(b'>');
const SPECIAL_QUERY: &AsciiSet = &QUERY.add(b'\'');

/// rust-url 2.5.8's path set predates whatwg/url commit 9bc33c39 (5 March
/// 2025, "Add U+005E (^) to the path percent-encode set"). That is the only
/// difference (`path_set_differs_from_rust_url_only_at_caret` checks), so
/// strings are compared against the set with ^ added.
const PATH_WITH_CARET: &AsciiSet = &PATH.add(b'^');

/// ECMA-262 `encodeURIComponent` (§19.2.6.5 and Encode, §19.2.6.6): every
/// code point is escaped except the ASCII word characters and "-.!~*'()".
/// URL §1.3 says UTF-8 percent-encode with the component set "gives
/// identical results".
const ENCODE_URI_COMPONENT: &AsciiSet = &NON_ALPHANUMERIC
    .remove(b'_')
    .remove(b'-')
    .remove(b'.')
    .remove(b'!')
    .remove(b'~')
    .remove(b'*')
    .remove(b'\'')
    .remove(b'(')
    .remove(b')');

/// The other engine's UTF-8 percent-encoding of `s` with (its version of)
/// `set`.
fn reference(s: &str, set: PercentEncodeSet) -> String {
    let ascii_set = match set {
        PercentEncodeSet::C0Control => CONTROLS,
        PercentEncodeSet::Fragment => FRAGMENT,
        PercentEncodeSet::Query => QUERY,
        PercentEncodeSet::SpecialQuery => SPECIAL_QUERY,
        PercentEncodeSet::Path => PATH_WITH_CARET,
        PercentEncodeSet::Userinfo => USERINFO,
        PercentEncodeSet::Component => ENCODE_URI_COMPONENT,
        PercentEncodeSet::ApplicationXWwwFormUrlencoded => {
            return form_urlencoded::byte_serialize(s.as_bytes()).collect();
        }
    };
    percent_encoding::utf8_percent_encode(s, ascii_set).to_string()
}

const SETS: [PercentEncodeSet; 8] = [
    PercentEncodeSet::C0Control,
    PercentEncodeSet::Fragment,
    PercentEncodeSet::Query,
    PercentEncodeSet::SpecialQuery,
    PercentEncodeSet::Path,
    PercentEncodeSet::Userinfo,
    PercentEncodeSet::Component,
    PercentEncodeSet::ApplicationXWwwFormUrlencoded,
];

#[test]
fn path_set_differs_from_rust_url_only_at_caret() {
    let differ: Vec<u32> = (0..0x80u32)
        .filter(|&c| {
            let s = string(&[c]);
            string(&utf8_percent_encode_code_point(c, PercentEncodeSet::Path))
                != percent_encoding::utf8_percent_encode(&s, PATH).to_string()
        })
        .collect();
    assert_eq!(differ, [0x5E]);
}

#[test]
fn differential_encode_every_scalar_value() {
    let step = if cfg!(miri) { 4099 } else { 1 };
    let mut n = 0usize;
    for c in (0..=0x10_FFFFu32).step_by(step).filter_map(char::from_u32) {
        let s = String::from(c);
        for set in SETS {
            let ours = string(&utf8_percent_encode_code_point(u32::from(c), set));
            assert_eq!(ours, reference(&s, set), "{c:?} with {set:?}");
        }
        n = n.saturating_add(1);
    }
    println!("UTF-8 percent-encode agrees on {n} scalar values in all 8 sets");
}

#[test]
fn differential_encode_strings() {
    let n = if cfg!(miri) { 10 } else { 20_000 };
    let mut rng = Rng(0x5EED_0106);
    for _ in 0..n {
        let len = rng.below(16);
        let s: Vec<u32> = (0..len).map(|_| rng.scalar()).collect();
        let text = string(&s);
        for set in SETS {
            let ours = string(&utf8_percent_encode(&s, set));
            assert_eq!(ours, reference(&text, set), "{text:?} with {set:?}");
        }
    }
}

#[test]
fn differential_percent_encode_every_byte() {
    // NON_ALPHANUMERIC percent-encodes every byte but the 62 ASCII
    // alphanumerics; the unit tests in src/encode.rs cover those with
    // `format!`.
    for b in (0..=255u8).filter(|b| !b.is_ascii_alphanumeric()) {
        let theirs = percent_encoding::percent_encode(&[b], NON_ALPHANUMERIC).to_string();
        assert_eq!(string(&percent_encode(b)), theirs, "{b:#04X}");
        assert_eq!(percent_decode(theirs.as_bytes()), [b], "{theirs}");
    }
}
