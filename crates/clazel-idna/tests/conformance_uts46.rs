//! UTS #46 and URL domain parser conformance (docs/phases/phase-1.md item
//! 1.8, stage 3).
//!
//! The proofs show the executable code equals `uts46/spec.rs` relative to
//! the generated Unicode tables. This file checks both against WPT: every
//! row of `url/resources/IdnaTestV2.json` and `url/resources/toascii.json`
//! (converted by `cargo xtask testdata`, `tests/data/wpt-url-idna/`)
//! through the URL Standard's "domain parser" with beStrict false. Rows
//! expected to fail are listed by name in `EXPECTED_FAILURES`, with the
//! reason; the test fails if the list is not exactly the failing rows.
//!
//! It also runs a differential test against rust-url's `idna` crate
//! (`domain_to_ascii_cow` with `AsciiDenyList::URL`, its implementation of
//! the URL Standard's domain to ASCII, and `domain_to_ascii_strict` for
//! beStrict), on random strings over a pool of code points that exercise
//! every step: mapping, ignoring, deviations, NFC with reordering, Hangul
//! and exclusions, label separators, Punycode labels (valid and not),
//! hyphens, Bidi classes and joiners. `idna` (with `idna_adapter` 1.1.0)
//! uses Unicode 16.0 data, so the pool holds only code points whose
//! properties did not change between 16.0 and 18.0. `idna` 1.1.0 also
//! predates the URL Standard's rule that an ASCII domain is lowercased and
//! never fails when beStrict is false, so those inputs are compared only
//! with beStrict true.

use std::borrow::Cow;

use clazel_idna::uts46::process::domain_parser;
use idna::AsciiDenyList;

/// One converted WPT row.
struct Case {
    file: &'static str,
    line: usize,
    name: &'static str,
    input: &'static [u32],
    /// `None`: the domain parser must fail.
    output: Option<&'static [u32]>,
}

// `const IDNA_TEST_V2: &[Case]` and `const TOASCII: &[Case]`.
include!("generated/wpt_url_idna.rs");

/// Rows that fail, by test name, with the reason.
const EXPECTED_FAILURES: &[(&str, &str)] = &[];

fn string(v: &[u32]) -> String {
    v.iter()
        .map(|&c| char::from_u32(c).unwrap_or('\u{FFFD}'))
        .collect()
}

#[test]
fn wpt_url_idna() {
    let mut failing: Vec<String> = Vec::new();
    let mut total = 0usize;
    // Miri is slow; under it, every 97th row (the expected failures are
    // then checked only outside Miri).
    let step = if cfg!(miri) { 97 } else { 1 };
    for case in IDNA_TEST_V2.iter().chain(TOASCII).step_by(step) {
        total = total.saturating_add(1);
        let got = domain_parser(case.input, false);
        if got.as_deref() != case.output {
            eprintln!(
                "{}:{}: {}: got {:?}, expected {:?}",
                case.file,
                case.line,
                case.name,
                got.as_deref().map(string),
                case.output.map(string)
            );
            failing.push(case.name.to_owned());
        }
    }
    let expected: Vec<String> = EXPECTED_FAILURES
        .iter()
        .map(|(n, _)| (*n).to_owned())
        .collect();
    println!(
        "WPT url IDNA: {} of {total} pass ({} expected failures)",
        total.saturating_sub(failing.len()),
        expected.len()
    );
    if !cfg!(miri) {
        assert_eq!(
            failing, expected,
            "failing rows differ from EXPECTED_FAILURES"
        );
    } else {
        assert!(failing.iter().all(|f| expected.contains(f)), "{failing:?}");
    }
}

/// Code points for the differential test (all assigned before Unicode 16).
const POOL: &[char] = &[
    'a',
    'b',
    'x',
    'n',
    'z',
    '0',
    '9',
    '-',
    '.',
    'A',
    'Z',
    '_',
    ' ',
    '<',
    '%',
    '\u{DF}',
    '\u{3C2}',
    '\u{E0}',
    '\u{300}',
    '\u{301}',
    '\u{323}',
    '\u{307}',
    '\u{5D0}',
    '\u{5D1}',
    '\u{308}',
    '\u{627}',
    '\u{628}',
    '\u{644}',
    '\u{661}',
    '\u{6F1}',
    '\u{200C}',
    '\u{200D}',
    '\u{94D}',
    '\u{915}',
    '\u{3002}',
    '\u{FF0E}',
    '\u{FF21}',
    '\u{2615}',
    '\u{AC00}',
    '\u{1100}',
    '\u{1161}',
    '\u{11A8}',
    '\u{AD}',
    '\u{2260}',
    '\u{338}',
    '\u{FFFD}',
    '\u{E000}',
    '\u{1E9E}',
    '\u{130}',
    '\u{FB01}',
    '\u{2126}',
    '\u{958}',
    '\u{640}',
    '\u{64B}',
    '\u{FE0F}',
    '\u{2488}',
    '\u{1F600}',
];

struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 >> 12;
        self.0 ^= self.0 << 25;
        self.0 ^= self.0 >> 27;
        self.0.wrapping_mul(0x2545_F491_4F6C_DD1D)
    }

    fn below(&mut self, n: usize) -> usize {
        usize::try_from(self.next())
            .unwrap_or(0)
            .checked_rem(n)
            .unwrap_or(0)
    }

    fn string(&mut self, max: usize) -> String {
        let len = self.below(max).saturating_add(1);
        (0..len)
            .map(|_| POOL.get(self.below(POOL.len())).copied().unwrap_or('a'))
            .collect()
    }
}

fn ours(input: &str, strict: bool) -> Option<String> {
    let code_points: Vec<u32> = input.chars().map(u32::from).collect();
    domain_parser(&code_points, strict).map(|v| string(&v))
}

/// `idna`'s result, with an empty result as failure: the domain parser's
/// step 7 ("If result is the empty string, then return failure"), which
/// `idna` leaves to its caller (rust-url's host parser).
fn theirs(input: &str, strict: bool) -> Option<String> {
    let result = if strict {
        idna::domain_to_ascii_strict(input).ok()
    } else {
        idna::domain_to_ascii_cow(input.as_bytes(), AsciiDenyList::URL)
            .ok()
            .map(Cow::into_owned)
    };
    result.filter(|r| !r.is_empty())
}

#[test]
fn differential_idna() {
    let mut rng = Rng(0x5EED_1DA5_0000_0001);
    let count = if cfg!(miri) { 20 } else { 100_000 };
    for _ in 0..count {
        // A plain string, or labels some of which are Punycode of others.
        let mut input = rng.string(10);
        if rng.below(3) == 0 {
            let label = rng.string(6);
            let chars: Vec<char> = label.chars().collect();
            if let Some(p) = idna::punycode::encode(&chars) {
                input = format!("{input}.xn--{p}");
            }
        }
        for strict in [false, true] {
            // idna 1.1.0 predates the URL Standard's rule that the domain
            // parser lowercases an ASCII domain without failing (whatwg/url,
            // 2025; WPT toascii.json "IDNA cannot fail ASCII domains"), so
            // it can fail where the standard does not.
            if !strict && input.is_ascii() {
                continue;
            }
            assert_eq!(
                ours(&input, strict),
                theirs(&input, strict),
                "{input:?} strict={strict}"
            );
        }
    }
}
