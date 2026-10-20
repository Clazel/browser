//! Forgiving-base64 conformance (docs/phases/phase-1.md item 1.6).
//!
//! The proofs show the decoder and encoder equal `spec.rs`, and
//! `independent.rs` shows the spec equals RFC 4648 on canonical input.
//! This file checks both against the outside world:
//!
//! 1. Every row of WPT `fetch/data-urls/resources/base64.json`, converted
//!    by `cargo xtask testdata` (`tests/data/wpt-base64/`), through
//!    `decode`; and, for each row that decodes, the round trip through
//!    `encode`.
//! 2. A differential test against the `base64` crate (`STANDARD`, RFC 4648
//!    §4 with padding and canonical pad bits): `encode` must give the same
//!    string for every input up to 2 bytes, a stride through 3-byte inputs
//!    and random longer ones; `decode` must take each of those strings back
//!    to the bytes (canonical input, where Infra and RFC 4648 agree).
//! 3. A differential test of `decode` on non-canonical input against the
//!    same crate configured to be forgiving where Infra is (padding
//!    optional, non-zero pad bits allowed; see `forgiving`), after
//!    removing ASCII whitespace by hand: every string of up to 5
//!    characters over a 10-character alphabet that includes "=",
//!    whitespace, VT and a character outside the alphabet.

use base64::Engine as _;
use base64::engine::DecodePaddingMode;
use base64::engine::general_purpose::{GeneralPurpose, GeneralPurposeConfig, STANDARD};
use clazel_base64::decode::decode;
use clazel_base64::encode::encode;

/// One converted WPT row.
struct Case {
    line: usize,
    input: &'static [u32],
    /// `None`: decode must fail.
    expected: Option<&'static [u8]>,
}

// `const WPT: &[Case]`, generated from the vendored WPT file.
include!("generated/wpt_base64.rs");

fn ascii(s: &[u32]) -> String {
    s.iter()
        .map(|&c| char::from_u32(c).unwrap_or(char::REPLACEMENT_CHARACTER))
        .collect()
}

fn scalars(s: &str) -> Vec<u32> {
    s.chars().map(u32::from).collect()
}

#[test]
fn wpt_data_urls_base64() {
    assert_eq!(WPT.len(), 80, "base64.json has 80 rows");
    let mut failures = Vec::new();
    let mut failed = 0usize;
    for c in WPT {
        let before = failures.len();
        let got = decode(c.input);
        if got.as_deref() != c.expected {
            failures.push(format!(
                "base64.json:{}: {:?}: got {got:?}, want {:?}",
                c.line,
                ascii(c.input),
                c.expected
            ));
        }
        if let Some(bytes) = c.expected {
            let back = decode(&encode(bytes));
            if back.as_deref() != Some(bytes) {
                failures.push(format!("base64.json:{}: round trip gave {back:?}", c.line));
            }
        }
        if failures.len() != before {
            failed = failed.saturating_add(1);
        }
    }
    // Summary line for the README table; format in xtask/src/conformance.rs.
    println!(
        "clazel-conformance: suite=\"WPT fetch/data-urls base64\" pass={} xfail=0 fail={failed} total={}",
        WPT.len().saturating_sub(failed),
        WPT.len()
    );
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

/// xorshift64*: a fixed, dependency-free sequence of test inputs.
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 >> 12;
        self.0 ^= self.0 << 25;
        self.0 ^= self.0 >> 27;
        self.0.wrapping_mul(0x2545_F491_4F6C_DD1D)
    }

    fn bytes(&mut self, max_len: u64) -> Vec<u8> {
        let len = self
            .next()
            .checked_rem(max_len.saturating_add(1))
            .unwrap_or(0);
        (0..len).map(|_| self.next().to_le_bytes()[0]).collect()
    }
}

fn check_canonical(bytes: &[u8]) {
    let ours = encode(bytes);
    let theirs = STANDARD.encode(bytes);
    assert_eq!(ascii(&ours), theirs, "encode {bytes:02X?}");
    assert_eq!(
        decode(&scalars(&theirs)).as_deref(),
        Some(bytes),
        "decode {theirs:?}"
    );
}

#[test]
fn differential_canonical() {
    let miri = cfg!(miri);
    check_canonical(&[]);
    for a in 0..=255u8 {
        check_canonical(&[a]);
        let step = if miri { 51 } else { 1 };
        for b in (0..=255u8).step_by(step) {
            check_canonical(&[a, b]);
        }
    }
    // 3-byte inputs: a stride that is coprime to 2^24, so every bit
    // pattern of each byte occurs.
    let count = if miri { 500 } else { 1 << 20 };
    let mut x: u32 = 0;
    for _ in 0..count {
        let [_, a, b, c] = x.to_be_bytes();
        check_canonical(&[a, b, c]);
        x = x.wrapping_add(0x9E_3779) & 0xFF_FFFF;
    }
    let mut rng = Rng(0x0123_4567_89AB_CDEF);
    let count = if miri { 200 } else { 100_000 };
    for _ in 0..count {
        check_canonical(&rng.bytes(64));
    }
}

/// The `base64` crate made forgiving where Infra is: non-zero pad bits
/// allowed (Infra's note: "YQ" and "YR" both return `a`), and padding
/// either required to complete the last quantum (when the input has "=";
/// Infra step 2 removes it only from a length that is a multiple of 4) or
/// absent (when it has none). The crate's `Indifferent` mode would also
/// accept "AA=", which Infra and WPT (`ab=`) reject.
const fn forgiving(padding: DecodePaddingMode) -> GeneralPurpose {
    GeneralPurpose::new(
        &base64::alphabet::STANDARD,
        GeneralPurposeConfig::new()
            .with_decode_padding_mode(padding)
            .with_decode_allow_trailing_bits(true),
    )
}
const PADDED: GeneralPurpose = forgiving(DecodePaddingMode::RequireCanonical);
const UNPADDED: GeneralPurpose = forgiving(DecodePaddingMode::RequireNone);

#[test]
fn differential_forgiving() {
    let alphabet = ['A', 'Q', 'g', '/', '+', '=', ' ', '\n', '\u{0B}', '-'];
    let max_len = if cfg!(miri) { 2 } else { 5 };
    let mut strings = vec![String::new()];
    let mut all = vec![String::new()];
    for _ in 0..max_len {
        strings = strings
            .iter()
            .flat_map(|s| {
                alphabet.iter().map(move |&c| {
                    let mut t = s.clone();
                    t.push(c);
                    t
                })
            })
            .collect();
        all.extend(strings.iter().cloned());
    }
    let mut failures = Vec::new();
    for s in &all {
        let ours = decode(&scalars(s));
        // Infra step 1, by hand: the crate knows no whitespace.
        let stripped: String = s
            .chars()
            .filter(|c| !matches!(c, '\t' | '\n' | '\u{0C}' | '\r' | ' '))
            .collect();
        let engine = if stripped.contains('=') {
            &PADDED
        } else {
            &UNPADDED
        };
        let theirs = engine.decode(&stripped).ok();
        if ours != theirs {
            failures.push(format!("{s:?}: ours {ours:?}, base64 crate {theirs:?}"));
        }
    }
    assert!(
        failures.is_empty(),
        "{} of {} differ:\n{}",
        failures.len(),
        all.len(),
        failures.join("\n")
    );
}
