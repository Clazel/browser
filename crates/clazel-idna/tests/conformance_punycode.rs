//! Punycode conformance (docs/phases/phase-1.md item 1.8, stage 1).
//!
//! The proofs show the decoder and encoder equal `punycode/spec.rs`, and
//! `punycode/independent.rs` shows the spec equals the RFC's own sample
//! implementation (Appendix C). This file checks both against the outside
//! world:
//!
//! 1. Every sample string of RFC 3492 §7.1, transcribed below from the RFC
//!    text: `decode` must give the listed code points, and `encode` the
//!    listed Punycode. The samples use mixed-case annotation (Appendix A),
//!    which only changes the case of the digits after the last delimiter;
//!    our encoder outputs lowercase digits, so those are compared
//!    lowercased. The decoder ignores case, so it is fed the samples as
//!    printed.
//! 2. A differential test against rust-url's `idna` crate (used by the
//!    `url` crate and Servo), `idna::punycode`: `encode` on random strings
//!    of scalar values, `decode` on every string of up to 3 characters
//!    over a 39-character alphabet and on random longer ones, and the round
//!    trip through both. `idna` decodes only to `char`s, so where our
//!    decoder returns a value that is not a scalar value, `idna` must fail.

use clazel_idna::punycode::decode::decode;
use clazel_idna::punycode::encode::encode;

fn scalars(s: &str) -> Vec<u32> {
    s.chars().map(u32::from).collect()
}

fn chars(v: &[u32]) -> Option<Vec<char>> {
    v.iter().map(|&c| char::from_u32(c)).collect()
}

fn string(v: &[u32]) -> String {
    v.iter().filter_map(|&c| char::from_u32(c)).collect()
}

/// The sample with the digits after its last delimiter lowercased: what
/// an encoder without mixed-case annotation outputs.
fn without_annotation(punycode: &str) -> String {
    match punycode.rfind('-') {
        Some(d) => {
            let (basic, digits) = punycode.split_at(d);
            format!("{basic}{}", digits.to_ascii_lowercase())
        }
        None => punycode.to_ascii_lowercase(),
    }
}

/// RFC 3492 §7.1 sample strings: (label, code points, Punycode as printed).
const RFC_3492_SAMPLES: &[(&str, &[u32], &str)] = &[
    (
        "(A)",
        &[
            0x0644, 0x064A, 0x0647, 0x0645, 0x0627, 0x0628, 0x062A, 0x0643, 0x0644, 0x0645, 0x0648,
            0x0634, 0x0639, 0x0631, 0x0628, 0x064A, 0x061F,
        ],
        "egbpdaj6bu4bxfgehfvwxn",
    ),
    (
        "(B)",
        &[
            0x4ED6, 0x4EEC, 0x4E3A, 0x4EC0, 0x4E48, 0x4E0D, 0x8BF4, 0x4E2D, 0x6587,
        ],
        "ihqwcrb4cv8a8dqg056pqjye",
    ),
    (
        "(C)",
        &[
            0x4ED6, 0x5011, 0x7232, 0x4EC0, 0x9EBD, 0x4E0D, 0x8AAA, 0x4E2D, 0x6587,
        ],
        "ihqwctvzc91f659drss3x8bo0yb",
    ),
    (
        "(D)",
        &[
            0x0050, 0x0072, 0x006F, 0x010D, 0x0070, 0x0072, 0x006F, 0x0073, 0x0074, 0x011B, 0x006E,
            0x0065, 0x006D, 0x006C, 0x0075, 0x0076, 0x00ED, 0x010D, 0x0065, 0x0073, 0x006B, 0x0079,
        ],
        "Proprostnemluvesky-uyb24dma41a",
    ),
    (
        "(E)",
        &[
            0x05DC, 0x05DE, 0x05D4, 0x05D4, 0x05DD, 0x05E4, 0x05E9, 0x05D5, 0x05D8, 0x05DC, 0x05D0,
            0x05DE, 0x05D3, 0x05D1, 0x05E8, 0x05D9, 0x05DD, 0x05E2, 0x05D1, 0x05E8, 0x05D9, 0x05EA,
        ],
        "4dbcagdahymbxekheh6e0a7fei0b",
    ),
    (
        "(F)",
        &[
            0x092F, 0x0939, 0x0932, 0x094B, 0x0917, 0x0939, 0x093F, 0x0928, 0x094D, 0x0926, 0x0940,
            0x0915, 0x094D, 0x092F, 0x094B, 0x0902, 0x0928, 0x0939, 0x0940, 0x0902, 0x092C, 0x094B,
            0x0932, 0x0938, 0x0915, 0x0924, 0x0947, 0x0939, 0x0948, 0x0902,
        ],
        "i1baa7eci9glrd9b2ae1bj0hfcgg6iyaf8o0a1dig0cd",
    ),
    (
        "(G)",
        &[
            0x306A, 0x305C, 0x307F, 0x3093, 0x306A, 0x65E5, 0x672C, 0x8A9E, 0x3092, 0x8A71, 0x3057,
            0x3066, 0x304F, 0x308C, 0x306A, 0x3044, 0x306E, 0x304B,
        ],
        "n8jok5ay5dzabd5bym9f0cm5685rrjetr6pdxa",
    ),
    (
        "(H)",
        &[
            0xC138, 0xACC4, 0xC758, 0xBAA8, 0xB4E0, 0xC0AC, 0xB78C, 0xB4E4, 0xC774, 0xD55C, 0xAD6D,
            0xC5B4, 0xB97C, 0xC774, 0xD574, 0xD55C, 0xB2E4, 0xBA74, 0xC5BC, 0xB9C8, 0xB098, 0xC88B,
            0xC744, 0xAE4C,
        ],
        "989aomsvi5e83db1d2a355cv1e0vak1dwrv93d5xbh15a0dt30a5jpsd879ccm6fea98c",
    ),
    (
        "(I)",
        &[
            0x043F, 0x043E, 0x0447, 0x0435, 0x043C, 0x0443, 0x0436, 0x0435, 0x043E, 0x043D, 0x0438,
            0x043D, 0x0435, 0x0433, 0x043E, 0x0432, 0x043E, 0x0440, 0x044F, 0x0442, 0x043F, 0x043E,
            0x0440, 0x0443, 0x0441, 0x0441, 0x043A, 0x0438,
        ],
        "b1abfaaepdrnnbgefbaDotcwatmq2g4l",
    ),
    (
        "(J)",
        &[
            0x0050, 0x006F, 0x0072, 0x0071, 0x0075, 0x00E9, 0x006E, 0x006F, 0x0070, 0x0075, 0x0065,
            0x0064, 0x0065, 0x006E, 0x0073, 0x0069, 0x006D, 0x0070, 0x006C, 0x0065, 0x006D, 0x0065,
            0x006E, 0x0074, 0x0065, 0x0068, 0x0061, 0x0062, 0x006C, 0x0061, 0x0072, 0x0065, 0x006E,
            0x0045, 0x0073, 0x0070, 0x0061, 0x00F1, 0x006F, 0x006C,
        ],
        "PorqunopuedensimplementehablarenEspaol-fmd56a",
    ),
    (
        "(K)",
        &[
            0x0054, 0x1EA1, 0x0069, 0x0073, 0x0061, 0x006F, 0x0068, 0x1ECD, 0x006B, 0x0068, 0x00F4,
            0x006E, 0x0067, 0x0074, 0x0068, 0x1EC3, 0x0063, 0x0068, 0x1EC9, 0x006E, 0x00F3, 0x0069,
            0x0074, 0x0069, 0x1EBF, 0x006E, 0x0067, 0x0056, 0x0069, 0x1EC7, 0x0074,
        ],
        "TisaohkhngthchnitingVit-kjcr8268qyxafd2f1b9g",
    ),
    (
        "(L)",
        &[
            0x0033, 0x5E74, 0x0042, 0x7D44, 0x91D1, 0x516B, 0x5148, 0x751F,
        ],
        "3B-ww4c5e180e575a65lsy2b",
    ),
    (
        "(M)",
        &[
            0x5B89, 0x5BA4, 0x5948, 0x7F8E, 0x6075, 0x002D, 0x0077, 0x0069, 0x0074, 0x0068, 0x002D,
            0x0053, 0x0055, 0x0050, 0x0045, 0x0052, 0x002D, 0x004D, 0x004F, 0x004E, 0x004B, 0x0045,
            0x0059, 0x0053,
        ],
        "-with-SUPER-MONKEYS-pc58ag80a8qai00g7n9n",
    ),
    (
        "(N)",
        &[
            0x0048, 0x0065, 0x006C, 0x006C, 0x006F, 0x002D, 0x0041, 0x006E, 0x006F, 0x0074, 0x0068,
            0x0065, 0x0072, 0x002D, 0x0057, 0x0061, 0x0079, 0x002D, 0x305D, 0x308C, 0x305E, 0x308C,
            0x306E, 0x5834, 0x6240,
        ],
        "Hello-Another-Way--fc4qua05auwb3674vfr0b",
    ),
    (
        "(O)",
        &[
            0x3072, 0x3068, 0x3064, 0x5C4B, 0x6839, 0x306E, 0x4E0B, 0x0032,
        ],
        "2-u9tlzr9756bt3uc0v",
    ),
    (
        "(P)",
        &[
            0x004D, 0x0061, 0x006A, 0x0069, 0x3067, 0x004B, 0x006F, 0x0069, 0x3059, 0x308B, 0x0035,
            0x79D2, 0x524D,
        ],
        "MajiKoi5-783gue6qz075azm5e",
    ),
    (
        "(Q)",
        &[
            0x30D1, 0x30D5, 0x30A3, 0x30FC, 0x0064, 0x0065, 0x30EB, 0x30F3, 0x30D0,
        ],
        "de-jg4avhby1noc0d",
    ),
    (
        "(R)",
        &[0x305D, 0x306E, 0x30B9, 0x30D4, 0x30FC, 0x30C9, 0x3067],
        "d9juau41awczczp",
    ),
    (
        "(S)",
        &[
            0x002D, 0x003E, 0x0020, 0x0024, 0x0031, 0x002E, 0x0030, 0x0030, 0x0020, 0x003C, 0x002D,
        ],
        "-> $1.00 <--",
    ),
];

#[test]
fn rfc_3492_samples() {
    assert_eq!(RFC_3492_SAMPLES.len(), 19, "(A) to (S)");
    for &(label, code_points, punycode) in RFC_3492_SAMPLES {
        assert_eq!(
            decode(&scalars(punycode)).as_deref(),
            Some(code_points),
            "decode {label}"
        );
        assert_eq!(
            encode(code_points).map(|v| string(&v)),
            Some(without_annotation(punycode)),
            "encode {label}"
        );
    }
}

struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 >> 12;
        self.0 ^= self.0 << 25;
        self.0 ^= self.0 >> 27;
        self.0.wrapping_mul(0x2545_F491_4F6C_DD1D)
    }

    fn below(&mut self, n: u64) -> u64 {
        self.next().checked_rem(n).unwrap_or(0)
    }

    /// A random scalar value, mostly from small blocks so that strings
    /// repeat code points and mix basic and non-basic ones.
    fn scalar(&mut self) -> char {
        let c = match self.below(8) {
            0 | 1 => 0x61_u64.wrapping_add(self.below(26)),
            2 => [0x2D, 0x30, 0x39, 0x41, 0x5A, 0x7F, 0x00]
                .get(usize::try_from(self.below(7)).unwrap_or(0))
                .copied()
                .unwrap_or(0x2D),
            3 => 0xE0_u64.wrapping_add(self.below(32)),
            4 => 0x430_u64.wrapping_add(self.below(32)),
            5 => 0x4E00_u64.wrapping_add(self.below(0x5200)),
            6 => 0x1_0000_u64.wrapping_add(self.below(0x10_0000)),
            _ => self.below(0x11_0000),
        };
        char::from_u32(u32::try_from(c).unwrap_or(0)).unwrap_or('\u{FFFD}')
    }
}

fn check_decode(input: &str) {
    let ours = decode(&scalars(input));
    let theirs = idna::punycode::decode(input);
    match ours.as_deref().map(chars) {
        Some(Some(cs)) => assert_eq!(theirs, Some(cs), "decode {input:?}"),
        // Ours failed, or produced values that are not scalar values,
        // which idna cannot represent.
        _ => assert_eq!(theirs, None, "decode {input:?}: ours gave {ours:X?}"),
    }
}

#[test]
fn differential_encode() {
    let mut rng = Rng(0x0123_4567_89AB_CDEF);
    let count = if cfg!(miri) { 30 } else { 200_000 };
    for _ in 0..count {
        let len = rng.below(40);
        let input: Vec<char> = (0..len).map(|_| rng.scalar()).collect();
        let code_points: Vec<u32> = input.iter().map(|&c| u32::from(c)).collect();
        let ours = encode(&code_points).map(|v| string(&v));
        let theirs = idna::punycode::encode(&input);
        assert_eq!(ours, theirs, "encode {input:?}");
        if let Some(encoded) = ours {
            // The round trip, through both decoders.
            assert_eq!(decode(&scalars(&encoded)), Some(code_points), "{encoded:?}");
            check_decode(&encoded);
        }
    }
}

#[test]
fn differential_decode() {
    let alphabet: Vec<char> = "abcdefghijklmnopqrstuvwxyz0123456789-AZ".chars().collect();
    let max_len = if cfg!(miri) { 1 } else { 3 };
    let mut strings = vec![String::new()];
    for _ in 0..max_len {
        let mut longer = Vec::new();
        for s in &strings {
            for &c in &alphabet {
                longer.push(format!("{s}{c}"));
            }
        }
        for s in &longer {
            check_decode(s);
        }
        strings = longer;
    }
    let mut rng = Rng(0xFEDC_BA98_7654_3210);
    let count = if cfg!(miri) { 30 } else { 200_000 };
    for _ in 0..count {
        let len = rng.below(16);
        let s: String = (0..len)
            .map(|_| {
                let i = usize::try_from(rng.below(39)).unwrap_or(0);
                alphabet.get(i).copied().unwrap_or('a')
            })
            .collect();
        check_decode(&s);
    }
}
