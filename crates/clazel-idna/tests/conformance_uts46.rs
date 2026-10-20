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

use clazel_idna::uts46::process::domain_parser;

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
