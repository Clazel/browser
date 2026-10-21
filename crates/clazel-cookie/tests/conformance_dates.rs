//! Cookie-date conformance (docs/phases/phase-2.md item 2.7).
//!
//! The proofs show the parser equals `date/spec.rs`, and the lemmas and
//! `date/independent.rs` check the spec against the calendar and RFC 9110.
//! This file checks it against the outside world: every row of
//! `http-state`'s `tests/data/dates/` (`examples.json`, which IETF
//! contributors wrote for RFC 6265, and `bsd-examples.json` from
//! Chromium), converted by `cargo xtask testdata`
//! (`tests/data/http-state-dates/`), through `parse_a_cookie_date`. A
//! row passes when the parsed date is the expected one, its weekday (taken
//! from `seconds_since_1601`: 1601-01-01 was a Monday) is the expected
//! weekday, or both fail.

use clazel_cookie::date::exec::parse_a_cookie_date;

/// One converted row.
struct Case {
    file: &'static str,
    index: usize,
    input: &'static [u8],
    /// (year, month, day, hour, minute, second, weekday with Monday 0);
    /// `None`: parsing must fail.
    expected: Option<(u32, u32, u32, u32, u32, u32, u32)>,
}

// `const DATES: &[Case]`, generated from the vendored files.
include!("generated/http_state_dates.rs");

#[test]
fn http_state_dates() {
    let mut pass: u64 = 0;
    let mut failed: u64 = 0;
    for c in DATES {
        let got = parse_a_cookie_date(c.input).map(|d| {
            let weekday = d
                .seconds_since_1601()
                .checked_div(86400)
                .and_then(|days| days.checked_rem(7))
                .and_then(|w| u32::try_from(w).ok());
            (
                d.year,
                d.month,
                d.day_of_month,
                d.hour,
                d.minute,
                d.second,
                weekday.unwrap_or(u32::MAX),
            )
        });
        if got == c.expected {
            pass = pass.saturating_add(1);
        } else {
            failed = failed.saturating_add(1);
            println!(
                "FAIL {}[{}] {:?}: got {got:?}, expected {:?}",
                c.file,
                c.index,
                String::from_utf8_lossy(c.input),
                c.expected
            );
        }
    }
    println!(
        "clazel-conformance: suite=\"http-state dates/\" pass={pass} xfail=0 fail={failed} total={}",
        DATES.len()
    );
    assert_eq!(failed, 0);
}
