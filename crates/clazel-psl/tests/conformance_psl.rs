//! The Public Suffix List's own `checkPublicSuffix` suite
//! (`data/publicsuffix-5dd321ff/tests.txt`, vendored from the same commit as
//! the list), run through the proven executable code. Each line is `input
//! expected`, `null` meaning no registrable domain; `//` lines are comments.
//! The harness canonicalizes input and expected output with the URL host
//! parser (the standard says to canonicalize first) and has the `null`
//! input return null.
//!
//! Prints one `clazel-conformance:` line (format in `xtask/src/conformance.rs`).

use clazel_psl::exec::registrable_domain_of_domain_exec;
use clazel_url::host::parse::host_parser_full;
use clazel_url::host::record::ParsedHost;

const TESTS: &str = include_str!("../data/publicsuffix-5dd321ff/tests.txt");

fn to_u32(s: &str) -> Vec<u32> {
    s.chars().map(u32::from).collect()
}

/// The canonical form the standard asks for before comparing ("lower-case,
/// Punycode"): the URL host parser's domain, through the proven parser.
fn canonical(s: &str) -> Vec<u32> {
    match host_parser_full(&to_u32(s), false) {
        Some(ParsedHost::Domain(d)) => d,
        _ => to_u32(&s.to_ascii_lowercase()),
    }
}

fn text(v: &[u32]) -> String {
    v.iter().filter_map(|c| char::from_u32(*c)).collect()
}

#[test]
fn check_public_suffix() {
    // The size of the suite: its non-comment, non-blank lines.
    let total = TESTS
        .lines()
        .filter(|l| !l.trim().is_empty() && !l.trim().starts_with("//"))
        .count();
    let mut pass = 0usize;
    let mut failures = Vec::new();
    for line in TESTS.lines() {
        let line = line.trim();
        if line.is_empty() || line.starts_with("//") {
            continue;
        }
        let mut it = line.split_whitespace();
        let (Some(input), Some(expected)) = (it.next(), it.next()) else {
            failures.push(format!("malformed line {line:?}"));
            continue;
        };
        let got = if input == "null" {
            None
        } else {
            registrable_domain_of_domain_exec(&canonical(input)).map(|v| text(&v))
        };
        let want = if expected == "null" {
            None
        } else {
            Some(text(&canonical(expected)))
        };
        if got == want {
            pass += 1;
        } else {
            failures.push(format!("{input}: got {got:?}, want {want:?}"));
        }
    }
    println!(
        "clazel-conformance: suite=\"publicsuffix tests.txt checkPublicSuffix\" pass={pass} xfail=0 fail={} total={total}",
        failures.len()
    );
    assert!(failures.is_empty(), "{failures:#?}");
}
