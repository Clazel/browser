//! WPT `cookies/` conformance through the kernel (docs/phases/phase-2.md
//! item 2.12): the converted tables that `clazel-cookie` vendors
//! (`../../clazel-cookie/tests/data/wpt-cookies/`, converted into
//! `../../clazel-cookie/tests/generated/wpt_cookies.rs`, which this file
//! includes: the data is reused, not copied), run as frames from fake
//! renderers, so through the IPC codec as well.
//!
//! The kernel has `document.cookie` only (the HTTP layer is Phase 3), so the
//! two kinds of case are run differently:
//!
//! - **`domCookieTest` cases** (the cookies are assigned to
//!   `document.cookie` in the page): the kernel opens a tab on the page, the
//!   renderer sends one `CookieSet` frame per assignment, then `CookieGet`,
//!   and the `CookieValue` reply must be the expected `document.cookie`.
//! - **`httpCookieTest` cases** (the cookies are `Set-Cookie` header values
//!   of a response): the kernel cannot receive a header, so the jar the HTTP
//!   path of `clazel-cookie` builds (the proven `store_a_set_cookie_string_exec`
//!   with an HTTP context, as `clazel-cookie`'s own conformance test does) is
//!   given to the kernel as its state, a tab is opened on the page that reads
//!   (the page, or `echo-cookie.html` when `defaultPath` is set), and the
//!   renderer's `CookieGet` must return the expected `document.cookie`.
//!   That runs the kernel's getter (request URL from the lock and committed
//!   URL, document context, cookie-averse check) on all of the cases, and the
//!   setter on the first kind.
//!
//! Each case starts with a fresh kernel and the clock at 23 October 2026. The
//! URL functions are the real ones (`step_real`, item 2.13). The
//! expected failures are listed in `XFAIL`, each with its reason. Under Miri,
//! every 4th `domCookieTest` case and every 89th `httpCookieTest` case is
//! run (a cookie call runs the Public Suffix List scan, which Miri runs at
//! about ten seconds a call).

mod support;

use clazel_cookie::matching::exec::canonicalize_a_host_name;
use clazel_cookie::storage::exec::{
    CookieRecord, HttpRequestRecord, RequestContextRecord, RequestUrlRecord,
    store_a_set_cookie_string_exec,
};
use clazel_ipc::message::codec::Msg;
use clazel_kernel::exec::records::EventRecord;
use clazel_origin::exec::url_origin_exec;
use clazel_url::url::parse::basic_url_parser;
use clazel_url::url::record::ParsedUrl;
use clazel_url::url::serialize::url_path_serializer;
use support::{Kernel, Out, code_points};

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

// `const WPT_COOKIES: &[Case]`, generated from the pages vendored by
// `clazel-cookie`.
include!("../../clazel-cookie/tests/generated/wpt_cookies.rs");

/// Seconds from 1601-01-01T00:00:00Z to 1970-01-01T00:00:00Z.
const UNIX_EPOCH_1601: u64 = 11_644_473_600;

/// 23 October 2026, 00:00:00 UTC, as a time of the cookie model.
const NOW: u64 = 1_792_713_600 + UNIX_EPOCH_1601;

/// Cases that are expected to fail: (file, name, reason).
const XFAIL: &[(&str, &str, &str)] = &[(
    "value.html",
    "Set cookie but ignore value after LF",
    "the string is `test=13\\nZYX`, a Set-Cookie value with a line feed: the HTTP layer (Phase 3) ends the header value at the LF, so the cookie parser sees `test=13`; \u{a7}5.6 step 1 ignores a string with a CTL character, so given the raw string it ignores it",
)];

fn parse(s: &str) -> Option<ParsedUrl> {
    basic_url_parser(&code_points(s), None)
}

/// The request URL of a parsed URL, as far as cookies read it.
fn request_url(url: &ParsedUrl) -> Option<RequestUrlRecord> {
    let narrow = |units: &[u32]| -> Option<Vec<u8>> {
        units.iter().map(|c| u8::try_from(*c).ok()).collect()
    };
    Some(RequestUrlRecord {
        scheme: narrow(&url.scheme)?,
        host: canonicalize_a_host_name(&url.host),
        path: narrow(&url_path_serializer(&url.path))?,
    })
}

/// A response to an HTTP request from a client with no "site for cookies".
fn http_context(url: &ParsedUrl) -> RequestContextRecord {
    RequestContextRecord::Http(HttpRequestRecord {
        url_origin: url_origin_exec(url, 0),
        site_for_cookies: None,
        is_reload_navigation: false,
        reloaded_document_was_same_site: false,
        navigates_top_level_traversable: false,
        method_is_safe: true,
        target_is_active_or_top_level: true,
    })
}

/// The origin of the server a case runs on.
fn base(c: &Case) -> &'static str {
    if c.https {
        "https://web-platform.test:8443"
    } else {
        "http://web-platform.test:8000"
    }
}

/// What `document.cookie` reads at the end of the case, got by the kernel
/// from a renderer in the reading page's tab.
fn read_in_kernel(mut kernel: Kernel, url: &str) -> Option<Vec<u8>> {
    let (Some(id), _) = kernel.open_tab(url, "") else {
        return None;
    };
    match kernel.send(id, &Msg::CookieGet).as_slice() {
        [Out::To(to, Msg::CookieValue { cookie_string })] if *to == id => {
            Some(cookie_string.clone())
        }
        _ => None,
    }
}

/// A `domCookieTest` case: set and get through the kernel.
fn run_dom(c: &Case) -> Option<Vec<u8>> {
    let mut kernel = Kernel::new();
    kernel.event(&EventRecord::Tick { time: NOW });
    let page = format!("{}{}", base(c), c.page);
    let (Some(id), _) = kernel.open_tab(&page, "") else {
        return None;
    };
    for cookie in c.cookies {
        // A `CookieSet` carries text; every converted cookie is UTF-8.
        let text = std::str::from_utf8(cookie).ok()?;
        let out = kernel.send(
            id,
            &Msg::CookieSet {
                cookie_string: text.as_bytes().to_vec(),
            },
        );
        if !out.is_empty() {
            return None;
        }
    }
    match kernel.send(id, &Msg::CookieGet).as_slice() {
        [Out::To(to, Msg::CookieValue { cookie_string })] if *to == id => {
            Some(cookie_string.clone())
        }
        _ => None,
    }
}

/// An `httpCookieTest` case: the jar the HTTP path builds, read through the
/// kernel.
fn run_http(c: &Case) -> Option<Vec<u8>> {
    let source = parse(&format!("{}/cookies/resources/cookie.py", base(c)))?;
    let mut jar: Vec<CookieRecord> = Vec::new();
    for cookie in c.cookies {
        jar = store_a_set_cookie_string_exec(
            &jar,
            cookie,
            &request_url(&source)?,
            &http_context(&source),
            NOW,
        );
    }
    let mut kernel = Kernel::new();
    kernel.event(&EventRecord::Tick { time: NOW });
    kernel.state.as_mut()?.jar = jar;
    let reader = if c.default_path {
        format!("{}/cookies/resources/echo-cookie.html", base(c))
    } else {
        format!("{}{}", base(c), c.page)
    };
    read_in_kernel(kernel, &reader)
}

/// Run the cases with `http == http`, every `step`th under Miri, and print
/// the suite line.
fn suite(name: &str, http: bool, miri_step: usize, run: fn(&Case) -> Option<Vec<u8>>) {
    let step = if cfg!(miri) { miri_step } else { 1 };
    let cases: Vec<&Case> = WPT_COOKIES.iter().filter(|c| c.http == http).collect();
    let mut pass: u64 = 0;
    let mut xfail: u64 = 0;
    let mut failed: u64 = 0;
    let mut total: u64 = 0;
    for c in cases.iter().step_by(step) {
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
        assert_eq!(total, u64::try_from(cases.len()).unwrap_or(u64::MAX));
    }
    println!(
        "clazel-conformance: suite=\"{name}\" pass={pass} xfail={xfail} fail={failed} total={total}"
    );
    assert_eq!(failed, 0);
}

#[test]
fn wpt_cookies_dom_through_kernel() {
    suite(
        "WPT cookies/ domCookieTest tables, document.cookie set and get through the kernel",
        false,
        4,
        run_dom,
    );
}

#[test]
fn wpt_cookies_http_read_through_kernel() {
    suite(
        "WPT cookies/ httpCookieTest tables, document.cookie read through the kernel",
        true,
        89,
        run_http,
    );
}
