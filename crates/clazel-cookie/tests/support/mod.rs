//! Helpers shared by the cookie conformance tests: URLs parsed with the
//! proven URL parser become the request records the storage code takes.

use clazel_cookie::matching::exec::{CanonicalHostName, canonicalize_a_host_name};
use clazel_cookie::storage::exec::{
    CookieRecord, HttpRequestRecord, RequestContextRecord, RequestUrlRecord,
    retrieve_a_cookie_string_exec, store_a_set_cookie_string_exec,
};
use clazel_origin::exec::url_origin_exec;
use clazel_url::url::parse::basic_url_parser;
use clazel_url::url::record::ParsedUrl;
use clazel_url::url::serialize::url_path_serializer;

/// Seconds from 1601-01-01T00:00:00Z to 1970-01-01T00:00:00Z.
const UNIX_EPOCH_1601: u64 = 11_644_473_600;

/// A Unix time (seconds since 1970) as a time of the cookie model.
pub fn since_1601(unix: u64) -> u64 {
    unix.saturating_add(UNIX_EPOCH_1601)
}

/// Parse an absolute URL with the proven basic URL parser.
pub fn parse(s: &str) -> Option<ParsedUrl> {
    let input: Vec<u32> = s.chars().map(u32::from).collect();
    basic_url_parser(&input, None)
}

fn narrow(units: &[u32]) -> Option<Vec<u8>> {
    units.iter().map(|c| u8::try_from(*c).ok()).collect()
}

/// The request URL of a parsed URL, as far as cookies read it.
pub fn request_url(url: &ParsedUrl) -> Option<RequestUrlRecord> {
    let host: Option<CanonicalHostName> = canonicalize_a_host_name(&url.host);
    Some(RequestUrlRecord {
        scheme: narrow(&url.scheme)?,
        host,
        path: narrow(&url_path_serializer(&url.path))?,
    })
}

/// A response to (or a request of) an HTTP request from a client with no
/// "site for cookies": same-site.
pub fn http_context(url: &ParsedUrl) -> RequestContextRecord {
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

/// Receive a Set-Cookie string.
pub fn set_cookie(
    jar: &[CookieRecord],
    value: &[u8],
    url: &ParsedUrl,
    context: &RequestContextRecord,
    now: u64,
) -> Option<Vec<CookieRecord>> {
    let req = request_url(url)?;
    Some(store_a_set_cookie_string_exec(
        jar, value, &req, context, now,
    ))
}

/// The cookie-string for a retrieval, updating the jar.
pub fn cookie_string(
    jar: &mut Vec<CookieRecord>,
    url: &ParsedUrl,
    context: &RequestContextRecord,
    now: u64,
) -> Option<Vec<u8>> {
    let req = request_url(url)?;
    Some(retrieve_a_cookie_string_exec(jar, &req, context, now))
}
