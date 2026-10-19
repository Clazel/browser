//! UTF-8 decode and encode conformance (docs/phases/phase-1.md items 1.3
//! and 1.4).
//!
//! The proofs show the decoder equals `utf8/spec.rs`, and `independent.rs`
//! shows the spec equals the Unicode Standard. This file checks both
//! against the outside world:
//!
//! 1. Every UTF-8 decode case in WPT `encoding/`, converted from the
//!    vendored files by `cargo xtask testdata` (`tests/data/wpt-encoding/`).
//! 2. A differential test of the three hooks against three other
//!    implementations: `String::from_utf8_lossy` and `str::from_utf8` from
//!    Rust's standard library, and `encoding_rs` (Firefox's), over every
//!    input up to 3 bytes, a structured and a random sample of 4-byte
//!    inputs, and random longer ones. Under Miri the samples are smaller.
//!
//! 3. "UTF-8 encode": every WPT case above whose input is well-formed UTF-8
//!    without a BOM, run in reverse (WPT `encoding/` has no UTF-8 encoder
//!    cases that do not go through a JavaScript string), and a differential
//!    test against `char::encode_utf8` and `encoding_rs` on every scalar
//!    value and on random scalar sequences.
//!
//! Encoding §4.1 and §8.1: "UTF-8 decode", "UTF-8 decode without BOM",
//! "UTF-8 decode without BOM or fail", and "UTF-8 encode".

use clazel_encoding::utf8::decode::{decode, decode_without_bom, decode_without_bom_or_fail};
use clazel_encoding::utf8::encode::encode;
use encoding_rs::UTF_8;

/// Which of the Encoding Standard's UTF-8 hooks a case runs.
#[derive(Debug, Clone, Copy)]
enum Hook {
    Decode,
    DecodeWithoutBom,
    DecodeWithoutBomOrFail,
}

/// One converted WPT case.
struct Case {
    file: &'static str,
    line: usize,
    name: &'static str,
    hook: Hook,
    input: &'static [u8],
    /// `None`: the hook must fail.
    expected: Option<&'static [u32]>,
}

// `const WPT: &[Case]`, generated from the vendored WPT files.
include!("generated/wpt_encoding.rs");

const BOM: [u8; 3] = [0xEF, 0xBB, 0xBF];

fn run(hook: Hook, input: &[u8]) -> Option<Vec<u32>> {
    match hook {
        Hook::Decode => Some(decode(input)),
        Hook::DecodeWithoutBom => Some(decode_without_bom(input)),
        Hook::DecodeWithoutBomOrFail => decode_without_bom_or_fail(input),
    }
}

fn scalars(s: &str) -> Vec<u32> {
    s.chars().map(u32::from).collect()
}

/// `encoding_rs`'s answer for a hook. Its `Encoding::decode` sniffs UTF-16
/// BOMs too, so "UTF-8 decode" is `decode_with_bom_removal`, which removes
/// only a UTF-8 BOM.
fn encoding_rs(hook: Hook, input: &[u8]) -> Option<Vec<u32>> {
    match hook {
        Hook::Decode => Some(scalars(&UTF_8.decode_with_bom_removal(input).0)),
        Hook::DecodeWithoutBom => Some(scalars(&UTF_8.decode_without_bom_handling(input).0)),
        Hook::DecodeWithoutBomOrFail => UTF_8
            .decode_without_bom_handling_and_without_replacement(input)
            .map(|s| scalars(&s)),
    }
}

/// The standard library's answer for a hook. `from_utf8_lossy` replaces
/// each maximal subpart of an ill-formed sequence with one U+FFFD, as
/// Encoding §8.1.1 does (Unicode §3.9.6).
fn std_lib(hook: Hook, input: &[u8]) -> Option<Vec<u32>> {
    match hook {
        Hook::Decode => {
            let rest = input.strip_prefix(&BOM).unwrap_or(input);
            Some(scalars(&String::from_utf8_lossy(rest)))
        }
        Hook::DecodeWithoutBom => Some(scalars(&String::from_utf8_lossy(input))),
        Hook::DecodeWithoutBomOrFail => std::str::from_utf8(input).ok().map(scalars),
    }
}

const HOOKS: [Hook; 3] = [
    Hook::Decode,
    Hook::DecodeWithoutBom,
    Hook::DecodeWithoutBomOrFail,
];

/// All three hooks agree with both references on `input`. Returns the
/// first disagreement, so the caller can report it with context.
fn differs(input: &[u8]) -> Option<String> {
    for hook in HOOKS {
        let ours = run(hook, input);
        for (engine, theirs) in [
            ("std", std_lib(hook, input)),
            ("encoding_rs", encoding_rs(hook, input)),
        ] {
            if ours != theirs {
                return Some(format!(
                    "{hook:?}({input:02X?}): ours {ours:X?}, {engine} {theirs:X?}"
                ));
            }
        }
    }
    None
}

/// Assert no input in `inputs` disagrees, reporting the first few that do.
fn check_all(what: &str, inputs: impl Iterator<Item = Vec<u8>>) {
    let mut count = 0usize;
    let mut failures = Vec::new();
    for input in inputs {
        count = count.saturating_add(1);
        if let Some(f) = differs(&input) {
            failures.push(f);
            if failures.len() >= 10 {
                break;
            }
        }
    }
    assert!(failures.is_empty(), "{what}: {}", failures.join("\n"));
    assert!(count > 0, "{what}: no inputs");
}

// ---------------------------------------------------------------------------
// 1. WPT
// ---------------------------------------------------------------------------

#[test]
fn wpt_encoding_utf8_decode() {
    assert!(WPT.len() >= 57, "WPT table shrank to {} cases", WPT.len());
    let mut failures = Vec::new();
    for c in WPT {
        let expected = c.expected.map(<[u32]>::to_vec);
        let ours = run(c.hook, c.input);
        if ours != expected {
            failures.push(format!(
                "{}:{} {} ({:?} {:02X?}): expected {expected:X?}, got {ours:X?}",
                c.file, c.line, c.name, c.hook, c.input
            ));
        }
        // The other engines must read the WPT case the same way, which
        // checks the converter's mapping of the API onto the hooks.
        for (engine, theirs) in [
            ("std", std_lib(c.hook, c.input)),
            ("encoding_rs", encoding_rs(c.hook, c.input)),
        ] {
            if theirs != expected {
                failures.push(format!(
                    "{}:{} {}: {engine} gives {theirs:X?}, WPT expects {expected:X?}",
                    c.file, c.line, c.name
                ));
            }
        }
        // A case that must fail fatally must replace something.
        if expected.is_none() {
            let replaced = decode(c.input);
            if !replaced.contains(&0xFFFD) {
                failures.push(format!(
                    "{}:{} {}: fatal case decodes without U+FFFD: {replaced:X?}",
                    c.file, c.line, c.name
                ));
            }
        }
    }
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

    fn byte(&mut self) -> u8 {
        self.next().to_le_bytes().first().copied().unwrap_or(0)
    }

    /// Half the time a byte from `EDGES`, otherwise any byte.
    fn edgy_byte(&mut self) -> u8 {
        if self.next() & 1 == 0 {
            EDGES.get(self.below(EDGES.len())).copied().unwrap_or(0)
        } else {
            self.byte()
        }
    }
}

/// Bytes at the boundaries of Encoding §8.1.1's decoder (and Unicode
/// Table 3-7): ASCII, the continuation range and its sub-ranges after E0,
/// ED, F0 and F4, the lead ranges, and bytes that never appear.
const EDGES: &[u8] = &[
    0x00, 0x41, 0x7F, 0x80, 0x8F, 0x90, 0x9F, 0xA0, 0xBB, 0xBF, 0xC0, 0xC1, 0xC2, 0xDF, 0xE0, 0xE1,
    0xEC, 0xED, 0xEE, 0xEF, 0xF0, 0xF1, 0xF3, 0xF4, 0xF5, 0xF7, 0xF8, 0xFE, 0xFF,
];

/// Every byte string of exactly `len` bytes over `alphabet`.
fn all_of_len(alphabet: &[u8], len: usize) -> impl Iterator<Item = Vec<u8>> {
    let mut next = Some(vec![0usize; len]);
    std::iter::from_fn(move || {
        let digits = next.take()?;
        let out: Vec<u8> = digits
            .iter()
            .filter_map(|d| alphabet.get(*d).copied())
            .collect();
        // Advance the odometer; `None` after the last one.
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

/// Inputs of up to 3 bytes, all of them (16.8 million). Under Miri, up to
/// 1 byte, plus 2- and 3-byte inputs over `EDGES`.
#[test]
fn differential_exhaustive_up_to_3_bytes() {
    let all: Vec<u8> = (0..=u8::MAX).collect();
    if cfg!(miri) {
        check_all("len 0-1", (0..=1).flat_map(|n| all_of_len(&all, n)));
        check_all("len 2 over EDGES", all_of_len(EDGES, 2));
        let mut rng = Rng(3);
        check_all(
            "len 3 sample",
            (0..200).map(|_| (0..3).map(|_| rng.edgy_byte()).collect()),
        );
        return;
    }
    for len in 0..=2 {
        check_all(&format!("len {len}"), all_of_len(&all, len));
    }
    // Length 3, split by first byte across threads.
    let threads = std::thread::available_parallelism()
        .map_or(4, usize::from)
        .min(64);
    let all = &all;
    std::thread::scope(|scope| {
        for t in 0..threads {
            scope.spawn(move || {
                let firsts = all.iter().skip(t).step_by(threads);
                check_all(
                    &format!("len 3, thread {t}"),
                    firsts.flat_map(|a| {
                        all_of_len(all, 2).map(move |rest| {
                            let mut input = vec![*a];
                            input.extend(rest);
                            input
                        })
                    }),
                );
            });
        }
    });
}

/// 4-byte inputs: every one over `EDGES` (29^4, about 707,000), and
/// uniformly random ones.
#[test]
fn differential_4_bytes() {
    let (random, structured) = if cfg!(miri) {
        (100, false)
    } else {
        (1 << 20, true)
    };
    if structured {
        check_all("len 4 over EDGES", all_of_len(EDGES, 4));
    }
    let mut rng = Rng(4);
    check_all(
        "len 4 random",
        (0..random).map(|_| (0..4).map(|_| rng.byte()).collect()),
    );
}

/// Longer inputs: random bytes biased to `EDGES`, and well-formed text
/// with random corruptions, from 5 to 300 bytes.
#[test]
fn differential_longer() {
    let n = if cfg!(miri) { 20 } else { 100_000 };
    let mut rng = Rng(5);
    check_all(
        "random bytes",
        (0..n).map(|_| {
            let len = rng.below(296).saturating_add(5);
            (0..len).map(|_| rng.edgy_byte()).collect()
        }),
    );
    let mut rng = Rng(6);
    check_all(
        "corrupted text",
        (0..n).map(|_| {
            let mut text = String::new();
            let chars = rng.below(60).saturating_add(2);
            for _ in 0..chars {
                // Weighted to the four UTF-8 lengths; never a surrogate.
                let limit = match rng.below(4) {
                    0 => 0x80,
                    1 => 0x800,
                    2 => 0x1_0000,
                    _ => 0x11_0000,
                };
                let c = u32::try_from(rng.below(limit))
                    .ok()
                    .and_then(char::from_u32);
                text.push(c.unwrap_or('\u{FFFD}'));
            }
            let mut bytes = text.into_bytes();
            if rng.below(4) == 0 {
                let mut with_bom = BOM.to_vec();
                with_bom.append(&mut bytes);
                bytes = with_bom;
            }
            for _ in 0..rng.below(4) {
                let at = rng.below(bytes.len());
                match rng.below(3) {
                    0 => {
                        if let Some(b) = bytes.get_mut(at) {
                            *b = rng.edgy_byte();
                        }
                    }
                    1 => bytes.truncate(at),
                    _ => bytes.insert(at.min(bytes.len()), rng.edgy_byte()),
                }
            }
            bytes
        }),
    );
}

// ---------------------------------------------------------------------------
// 3. Encode
// ---------------------------------------------------------------------------

/// WPT decode cases read backwards: when the bytes are well-formed UTF-8
/// with no BOM, "UTF-8 encode" of the decoded scalar values must give the
/// bytes back.
#[test]
fn wpt_encoding_utf8_encode() {
    let mut count = 0usize;
    let mut failures = Vec::new();
    for c in WPT {
        let Some(expected) = c.expected else { continue };
        if std::str::from_utf8(c.input).is_err() || c.input.starts_with(&BOM) {
            continue;
        }
        count = count.saturating_add(1);
        let ours = encode(expected);
        if ours != c.input {
            failures.push(format!(
                "{}:{} {}: ours {ours:02X?}, expected {:02X?}",
                c.file, c.line, c.name, c.input
            ));
        }
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
    assert!(count >= 8, "WPT encode cases shrank to {count}");
}

/// `encoding_rs`'s and the standard library's encodings of `s`.
fn reference_encodings(s: &str) -> [(&'static str, Vec<u8>); 2] {
    [
        ("std", s.as_bytes().to_vec()),
        ("encoding_rs", UTF_8.encode(s).0.into_owned()),
    ]
}

/// Every scalar value on its own. Under Miri, a stride through them.
#[test]
fn differential_encode_every_scalar_value() {
    let step = if cfg!(miri) { 4099 } else { 1 };
    let mut failures = Vec::new();
    for c in ('\u{0}'..=char::MAX).step_by(step) {
        let mut buf = [0u8; 4];
        let ours = encode(&[u32::from(c)]);
        if ours != c.encode_utf8(&mut buf).as_bytes() {
            failures.push(format!("U+{:04X}: ours {ours:02X?}", u32::from(c)));
        }
        for (engine, theirs) in reference_encodings(c.encode_utf8(&mut buf)) {
            if ours != theirs {
                failures.push(format!(
                    "U+{:04X}: ours {ours:02X?}, {engine} {theirs:02X?}",
                    u32::from(c)
                ));
            }
        }
        if failures.len() >= 10 {
            break;
        }
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

/// Random scalar sequences, weighted to the four UTF-8 lengths.
#[test]
fn differential_encode_sequences() {
    let n = if cfg!(miri) { 20 } else { 100_000 };
    let mut rng = Rng(7);
    for _ in 0..n {
        let len = rng.below(64);
        let text: String = (0..len)
            .map(|_| {
                let limit = match rng.below(4) {
                    0 => 0x80,
                    1 => 0x800,
                    2 => 0x1_0000,
                    _ => 0x11_0000,
                };
                u32::try_from(rng.below(limit))
                    .ok()
                    .and_then(char::from_u32)
                    .unwrap_or('\u{FFFD}')
            })
            .collect();
        let ours = encode(&scalars(&text));
        for (engine, theirs) in reference_encodings(&text) {
            assert_eq!(ours, theirs, "{engine} on {text:?}");
        }
    }
}
