//! `http-state` cookie parser corpus conformance (docs/phases/phase-2.md
//! item 2.9).
//!
//! Each of the 222 rows of `tests/data/http-state-parser/parser.json` (the
//! RFC 6265 interoperability tests) is a response to
//! `http://home.example.org:8888/cookie-parser?<test>` with some
//! `Set-Cookie` header values, followed by a request to
//! `/cookie-parser-result?<test>` on the same server (or to the row's
//! `sent-to`, the test's `Location`), whose `Cookie` header must be the
//! `sent` cookies. Here: the header values go one by one through
//! `store_a_set_cookie_string_exec`, then `retrieve_a_cookie_string_exec`
//! runs for the second URL, as an HTTP request; the cookie-string must be
//! the `sent` cookies, written `name=value` and joined with "; ", or just
//! `value` for an empty name (RFC 6265bis §5.8.3 step 6.1). The URLs are
//! parsed by the proven URL parser, and the clock is 1 January 2010, when
//! the corpus was written (the rows' dates are relative to it).
//!
//! The corpus is for RFC 6265. Rows where RFC 6265bis draft 22 differs on
//! purpose are in `XFAIL` with the reason; none is counted as a pass.
//! Under Miri, every fifth row is run.

mod support;

/// One converted row.
struct Case {
    name: &'static str,
    received: &'static [&'static [u8]],
    sent_to: Option<&'static str>,
    sent: &'static [(&'static [u8], &'static [u8])],
}

// `const PARSER: &[Case]`, generated from the vendored `parser.json`.
include!("generated/http_state_parser.rs");

/// 1 January 2010, 00:00:00 UTC.
const NOW_UNIX: u64 = 1_262_304_000;

/// RFC 6265bis §5.6 step 3 makes a name-value pair without "=" a cookie with
/// an empty name and that value, and "=value" a cookie with an empty name;
/// RFC 6265 §5.2 ignored both, which these rows expect.
const NAMELESS: &str = "nameless cookies (RFC 6265bis \u{a7}5.6 step 3; RFC 6265 ignored them)";

/// The row sends a NUL or a carriage return inside a header value, which the
/// HTTP layer (Phase 3) would end or reject; \u{a7}5.6 step 1 ignores a
/// string with a CTL character. Chromium disables these rows too.
const HTTP_LAYER: &str = "a NUL or CR inside the header value, handled by the HTTP layer (Phase 3); Chromium disables the row";

/// The row's cookie has Path=/cookie-parser-result/foo/bar and the request is
/// for /cookie-parser-result/f%6Fo/bar: the row expects the percent-encoded
/// path to be decoded before path-matching, which \u{a7}5.1.4 does not do.
/// Chromium disables the row.
const PERCENT_PATH: &str =
    "path-match compares octets, without percent-decoding (\u{a7}5.1.4); Chromium disables the row";

/// RFC 6265 \u{a7}5.2.3 ignored a Domain attribute with an empty value;
/// draft 22 \u{a7}5.6.3 does not, so the last Domain attribute here is empty,
/// which \u{a7}5.7 step 7 reads as no domain-attribute: a host-only cookie.
const EMPTY_DOMAIN: &str = "an empty Domain attribute is not ignored (RFC 6265bis \u{a7}5.6.3)";

/// Rows that are expected to fail: (name, reason).
const XFAIL: &[(&str, &str)] = &[
    ("0004", NAMELESS),
    ("0021", NAMELESS),
    ("0023", NAMELESS),
    ("0024", NAMELESS),
    ("0025", NAMELESS),
    ("0026", NAMELESS),
    ("0027", NAMELESS),
    ("0028", NAMELESS),
    ("CHROMIUM0009", NAMELESS),
    ("CHROMIUM0010", NAMELESS),
    ("CHROMIUM0012", NAMELESS),
    ("MOZILLA0012", NAMELESS),
    ("MOZILLA0014", NAMELESS),
    ("MOZILLA0015", NAMELESS),
    ("MOZILLA0016", NAMELESS),
    ("MOZILLA0017", NAMELESS),
    ("NAME0017", NAMELESS),
    ("NAME0023", NAMELESS),
    ("NAME0025", NAMELESS),
    ("NAME0028", NAMELESS),
    ("NAME0031", NAMELESS),
    ("NAME0032", NAMELESS),
    ("NAME0033", NAMELESS),
    ("DISABLED_CHROMIUM0022", HTTP_LAYER),
    ("DISABLED_CHROMIUM0023", HTTP_LAYER),
    ("DISABLED_PATH0029", PERCENT_PATH),
    ("OPTIONAL_DOMAIN0042", EMPTY_DOMAIN),
];

/// The cookie-string the row expects.
fn expected(c: &Case) -> Vec<u8> {
    let mut out = Vec::new();
    for (i, (name, value)) in c.sent.iter().enumerate() {
        if i > 0 {
            out.extend_from_slice(b"; ");
        }
        if !name.is_empty() {
            out.extend_from_slice(name);
            out.push(b'=');
        }
        out.extend_from_slice(value);
    }
    out
}

/// The cookie-string sent to the row's second URL; `None` if a URL does not
/// parse.
fn run(c: &Case) -> Option<Vec<u8>> {
    let now = support::since_1601(NOW_UNIX);
    let set = support::parse(&format!(
        "http://home.example.org:8888/cookie-parser?{}",
        c.name
    ))?;
    let context = support::http_context(&set);
    let mut jar = Vec::new();
    for header in c.received {
        jar = support::set_cookie(&jar, header, &set, &context, now)?;
    }
    let target = match c.sent_to {
        None => format!(
            "http://home.example.org:8888/cookie-parser-result?{}",
            c.name
        ),
        Some(url) if url.starts_with('/') => format!("http://home.example.org:8888{url}"),
        Some(url) => url.to_owned(),
    };
    let target = support::parse(&target)?;
    let context = support::http_context(&target);
    support::cookie_string(&mut jar, &target, &context, now)
}

#[test]
fn http_state_parser() {
    let step = if cfg!(miri) { 5 } else { 1 };
    let mut pass: u64 = 0;
    let mut xfail: u64 = 0;
    let mut failed: u64 = 0;
    let mut total: u64 = 0;
    for c in PARSER.iter().step_by(step) {
        total = total.saturating_add(1);
        let got = run(c);
        let ok = got.as_deref() == Some(expected(c).as_slice());
        let expected_failure = XFAIL.iter().find(|(n, _)| *n == c.name);
        match (ok, expected_failure) {
            (true, None) => pass = pass.saturating_add(1),
            (false, Some(_)) => xfail = xfail.saturating_add(1),
            (true, Some((_, reason))) => {
                failed = failed.saturating_add(1);
                println!("FAIL (expected to fail, but passes: {reason}) {}", c.name);
            }
            (false, None) => {
                failed = failed.saturating_add(1);
                println!(
                    "FAIL {} {:?}: got {:?}, expected {:?}",
                    c.name,
                    c.received
                        .iter()
                        .map(|r| String::from_utf8_lossy(r))
                        .collect::<Vec<_>>(),
                    got.as_deref().map(String::from_utf8_lossy),
                    String::from_utf8_lossy(&expected(c))
                );
            }
        }
    }
    if !cfg!(miri) {
        assert_eq!(total, u64::try_from(PARSER.len()).unwrap_or(u64::MAX));
    }
    println!(
        "clazel-conformance: suite=\"http-state parser corpus\" pass={pass} xfail={xfail} fail={failed} total={total}"
    );
    assert_eq!(failed, 0);
}
