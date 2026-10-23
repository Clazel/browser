//! WPT `cookies/` conformance (docs/phases/phase-2.md item 2.9).
//!
//! The proofs show the exec code equals `storage/spec.rs`; this file checks
//! the spec against the web platform's own cookie tests, through the proven
//! code. Every case of the tables converted from the vendored pages
//! (`tests/data/wpt-cookies/`, `SOURCE.md` says which and which not) is run
//! as the page runs it: the cookies are set as `Set-Cookie` header values of
//! a response from `/cookies/resources/cookie.py` (`httpCookieTest`) or
//! assigned to `document.cookie` in the page (`domCookieTest`), and
//! `document.cookie` is read at the test page, or, for `httpCookieTest` with
//! `defaultPath`, in `/cookies/resources/echo-cookie.html`. The URLs are
//! parsed by the proven URL parser, and each case starts with an empty jar.
//!
//! The expected failures are listed in `XFAIL`, each with its reason; none
//! is counted as a pass. Under Miri, every 89th case is run (two cases; a store
//! runs the Public Suffix List scan several times, which Miri runs at about ten seconds a case).

mod support;

use clazel_cookie::storage::exec::{CookieRecord, DocumentCallRecord, RequestContextRecord};
use clazel_origin::exec::url_origin_exec;
use clazel_url::url::record::ParsedUrl;

/// One converted case.
struct Case {
    file: &'static str,
    index: usize,
    name: &'static str,
    page: &'static str,
    https: bool,
    http: bool,
    default_path: bool,
    cookies: &'static [&'static [u8]],
    expected: &'static [u8],
}

// `const WPT_COOKIES: &[Case]`, generated from the vendored pages.
include!("generated/wpt_cookies.rs");

/// 23 October 2026, 00:00:00 UTC.
const NOW_UNIX: u64 = 1_792_713_600;

/// Cases that are expected to fail: (file, name, reason).
const XFAIL: &[(&str, &str, &str)] = &[(
    "value.html",
    "Set cookie but ignore value after LF",
    "the string is `test=13\\nZYX`, a Set-Cookie value with a line feed: the HTTP layer (Phase 3) ends the header value at the LF, so the cookie parser sees `test=13`; \u{a7}5.6 step 1 ignores a string with a CTL character, so given the raw string it ignores it",
)];

fn document_context(url: &ParsedUrl) -> RequestContextRecord {
    RequestContextRecord::NonHttp(DocumentCallRecord {
        site_for_cookies: url_origin_exec(url, 0),
        top_level_origin: url_origin_exec(url, 0),
    })
}

/// What `document.cookie` reads at the end of the case; `None` if a URL
/// does not parse.
fn run(c: &Case) -> Option<Vec<u8>> {
    let now = support::since_1601(NOW_UNIX);
    let base = if c.https {
        "https://web-platform.test:8443"
    } else {
        "http://web-platform.test:8000"
    };
    let page = support::parse(&format!("{base}{}", c.page))?;
    let mut jar: Vec<CookieRecord> = Vec::new();
    if c.http {
        let source = support::parse(&format!("{base}/cookies/resources/cookie.py"))?;
        let context = support::http_context(&source);
        for cookie in c.cookies {
            jar = support::set_cookie(&jar, cookie, &source, &context, now)?;
        }
    } else {
        let context = document_context(&page);
        for cookie in c.cookies {
            jar = support::set_cookie(&jar, cookie, &page, &context, now)?;
        }
    }
    let reader = if c.default_path {
        support::parse(&format!("{base}/cookies/resources/echo-cookie.html"))?
    } else {
        page
    };
    let context = document_context(&reader);
    support::cookie_string(&mut jar, &reader, &context, now)
}

#[test]
fn wpt_cookies() {
    let step = if cfg!(miri) { 89 } else { 1 };
    let mut pass: u64 = 0;
    let mut xfail: u64 = 0;
    let mut failed: u64 = 0;
    let mut total: u64 = 0;
    for c in WPT_COOKIES.iter().step_by(step) {
        total = total.saturating_add(1);
        let got = run(c);
        let ok = got.as_deref() == Some(c.expected);
        let expected_failure = XFAIL.iter().find(|(f, n, _)| *f == c.file && *n == c.name);
        match (ok, expected_failure) {
            (true, None) => pass = pass.saturating_add(1),
            (false, Some(_)) => xfail = xfail.saturating_add(1),
            (true, Some((_, _, reason))) => {
                failed = failed.saturating_add(1);
                println!(
                    "FAIL (expected to fail, but passes: {reason}) {}[{}] {:?}",
                    c.file, c.index, c.name
                );
            }
            (false, None) => {
                failed = failed.saturating_add(1);
                println!(
                    "FAIL {}[{}] {:?}: got {:?}, expected {:?}",
                    c.file,
                    c.index,
                    c.name,
                    got.as_deref().map(String::from_utf8_lossy),
                    String::from_utf8_lossy(c.expected)
                );
            }
        }
    }
    if !cfg!(miri) {
        assert_eq!(total, u64::try_from(WPT_COOKIES.len()).unwrap_or(u64::MAX));
    }
    println!(
        "clazel-conformance: suite=\"WPT cookies/ httpCookieTest and domCookieTest tables\" pass={pass} xfail={xfail} fail={failed} total={total}"
    );
    assert_eq!(failed, 0);
}
