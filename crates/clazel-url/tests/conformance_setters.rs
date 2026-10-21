//! URL API setter conformance (docs/phases/phase-1.md item 1.11).
//!
//! The proofs show the exec setters equal `api/spec.rs`. This file checks
//! the spec against the outside world:
//!
//! 1. Every case of WPT `url/resources/setters_tests.json`, converted by
//!    `cargo xtask testdata` (`tests/data/wpt-url-setters/SOURCE.md`). A
//!    case is `new URL(href)`, then the setter with the new value, then
//!    each getter the case names compared with its value. The unit is a
//!    case: it passes only if every getter it names matches.
//! 2. A differential test against rust-url 2.5.8's setters (`url::quirks`,
//!    which implements the URL API for Servo): 200,000 random (start URL,
//!    setter, value) triples, comparing the href after the setter. One rule
//!    newer than rust-url (U+005E in the path percent-encode set) is
//!    adjusted for in `ours`. Every other mismatch must fall in one of the
//!    [`Divergence`] classes, each a place where rust-url contradicts a
//!    named step of the standard and a WPT case we pass; the test prints
//!    how many fell in each, and fails on any other. (The `href` setter is
//!    the basic URL parser, whose differential test is in
//!    `conformance_url.rs`.)
//!
//! The URL is parsed by `basic_url_parser` and set by the setters in
//! `api/setters.rs`, whose parser runs `host_parser_full`, so
//! `clazel-idna`'s domain parser handles every non-ASCII domain.

use clazel_url::api::setters;
use clazel_url::host::record::ParsedHost;
use clazel_url::url::parse::basic_url_parser;
use clazel_url::url::record::{ParsedPath, ParsedUrl};
use clazel_url::url::serialize::url_path_serializer;

/// One converted WPT case.
struct Case {
    name: &'static str,
    setter: &'static str,
    href: &'static str,
    new_value: &'static str,
    /// (getter, value) pairs.
    expected: &'static [(&'static str, &'static str)],
}

// `const SETTERS_TESTS: &[Case]`, generated from the vendored WPT file.
include!("generated/wpt_url_setters.rs");

/// Cases that fail for a reason outside the setters, by name, with the
/// reason. None today.
const EXPECTED_FAILURES: &[(&str, &str)] = &[];

fn scalars(s: &str) -> Vec<u32> {
    s.chars().map(u32::from).collect()
}

fn string(v: &[u32]) -> String {
    v.iter()
        .map(|&c| char::from_u32(c).unwrap_or(char::REPLACEMENT_CHARACTER))
        .collect()
}

/// A URL API getter (URL §6.1), from the URL record.
fn getter(url: &ParsedUrl, name: &str) -> Option<String> {
    let hostname = url
        .host
        .as_ref()
        .map(|h: &ParsedHost| string(&h.serialize()))
        .unwrap_or_default();
    let prefixed = |prefix: char, v: &Option<Vec<u32>>| match v {
        Some(v) if !v.is_empty() => format!("{prefix}{}", string(v)),
        _ => String::new(),
    };
    Some(match name {
        "href" => string(&url.serialize(false)),
        "protocol" => format!("{}:", string(&url.scheme)),
        "username" => string(&url.username),
        "password" => string(&url.password),
        "host" => match (&url.host, url.port) {
            (None, _) => String::new(),
            (Some(_), None) => hostname,
            (Some(_), Some(p)) => format!("{hostname}:{p}"),
        },
        "hostname" => hostname,
        "port" => url.port.map(|p| p.to_string()).unwrap_or_default(),
        "pathname" => string(&url_path_serializer(&url.path)),
        "search" => prefixed('?', &url.query),
        "hash" => prefixed('#', &url.fragment),
        _ => return None,
    })
}

/// `url[setter] = value`. `Err` if the setter throws (only `href` does).
fn set(url: &mut ParsedUrl, setter: &str, value: &str) -> Result<(), String> {
    let v = scalars(value);
    match setter {
        "href" => {
            if !setters::set_href(url, &v) {
                return Err("href setter threw a TypeError".into());
            }
        }
        "protocol" => setters::set_protocol(url, &v),
        "username" => setters::set_username(url, &v),
        "password" => setters::set_password(url, &v),
        "host" => setters::set_host(url, &v),
        "hostname" => setters::set_hostname(url, &v),
        "port" => setters::set_port(url, &v),
        "pathname" => setters::set_pathname(url, &v),
        "search" => setters::set_search(url, &v),
        "hash" => setters::set_hash(url, &v),
        other => return Err(format!("no setter {other:?}")),
    }
    Ok(())
}

/// What is wrong with `case`, if anything.
fn run_case(case: &Case) -> Option<String> {
    let Some(mut url) = basic_url_parser(&scalars(case.href), None) else {
        return Some(format!("new URL({:?}) failed", case.href));
    };
    if let Err(e) = set(&mut url, case.setter, case.new_value) {
        return Some(e);
    }
    let problems: Vec<String> = case
        .expected
        .iter()
        .filter_map(|(name, want)| match getter(&url, name) {
            Some(got) if got == *want => None,
            Some(got) => Some(format!("{name}: got {got:?}, expected {want:?}")),
            None => Some(format!("no getter {name:?}")),
        })
        .collect();
    if problems.is_empty() {
        None
    } else {
        Some(problems.join("; "))
    }
}

#[test]
fn wpt_setters_tests() {
    let mut failures = Vec::new();
    let mut passed = 0usize;
    let mut expected_failures = 0usize;
    for case in SETTERS_TESTS {
        match run_case(case) {
            None => passed = passed.saturating_add(1),
            Some(_) if EXPECTED_FAILURES.iter().any(|(n, _)| *n == case.name) => {
                expected_failures = expected_failures.saturating_add(1);
            }
            Some(p) => failures.push(format!("{}: {p}", case.name)),
        }
    }
    for (name, _) in EXPECTED_FAILURES {
        match SETTERS_TESTS.iter().find(|c| c.name == *name) {
            None => failures.push(format!(
                "EXPECTED_FAILURES lists {name:?}, which is no such case"
            )),
            Some(c) if run_case(c).is_none() => {
                failures.push(format!("EXPECTED_FAILURES lists {name:?}, which passes"));
            }
            Some(_) => {}
        }
    }
    // Summary line for the README table (unit: a case); format in
    // xtask/src/conformance.rs.
    println!(
        "clazel-conformance: suite=\"WPT url/ setters_tests.json\" pass={passed} xfail={expected_failures} fail={} total={}",
        SETTERS_TESTS
            .len()
            .saturating_sub(passed)
            .saturating_sub(expected_failures),
        SETTERS_TESTS.len()
    );
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

// ---------------------------------------------------------------------
// Differential test against rust-url's setters.
// ---------------------------------------------------------------------

/// A small deterministic generator (64-bit LCG, Knuth's constants).
struct Lcg(u64);

impl Lcg {
    fn next(&mut self) -> u64 {
        self.0 = self
            .0
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        self.0 >> 16
    }

    fn below(&mut self, n: usize) -> usize {
        let n = u64::try_from(n).unwrap_or(1);
        usize::try_from(self.next().checked_rem(n).unwrap_or(0)).unwrap_or(0)
    }

    fn pick<'a>(&mut self, from: &[&'a str]) -> &'a str {
        from.get(self.below(from.len())).copied().unwrap_or("")
    }
}

fn samples(full: usize, miri: usize) -> usize {
    if cfg!(miri) { miri } else { full }
}

/// URLs the setters start from: one of each kind (special, file,
/// non-special with a host, with an empty host, without a host, with an
/// opaque path), with and without credentials, port, query and fragment.
/// Each parses to the same href in both engines.
const START: &[&str] = &[
    "http://example.com/a/b?q#f",
    "https://u:p@h.example:8080/a/b/c",
    "ws://h/",
    "ftp://h:21/x",
    "file:///C:/dir/file",
    "file://host/share/x",
    "file:///",
    "sc://h/a/b",
    "sc://u@h:1/a?q#f",
    "sc:///p",
    "sc:/a/b",
    "sc:opaque?q#f",
    "mailto:x@example.com",
    "javascript:alert(1)",
    "web+demo:/.//p",
    "http://1.2.3.4/",
    "http://[::1]:99/",
];

/// The setters, by attribute name.
const SETTERS: &[&str] = &[
    "protocol", "username", "password", "host", "hostname", "port", "pathname", "search", "hash",
];

/// Pieces that random values are made of: every delimiter a setter's
/// state switches on, schemes, ports at the 16-bit edge, hosts, dot
/// segments, C0 controls, spaces, tabs, and non-ASCII code points.
const PIECES: &[&str] = &[
    "/",
    "\\",
    "?",
    "#",
    "@",
    ":",
    "[",
    "]",
    "%",
    "%2e",
    ".",
    "..",
    " ",
    "\t",
    "\n",
    "\u{0}",
    "\u{1f}",
    "a",
    "B",
    "z9",
    "http",
    "https",
    "file",
    "sc",
    "ws",
    "example.com",
    "EXAMPLE.org",
    "localhost",
    "C|",
    "c:",
    "1.2.3.4",
    "0x7f.1",
    "[::1]",
    "80",
    "443",
    "21",
    "65535",
    "65536",
    "8080",
    "0",
    "user",
    "%40",
    "^",
    "|",
    "~",
    "'",
    "\"",
    "<",
    ">",
    "`",
    "{",
    "}",
    "ß",
    "ñ",
    "\u{fffd}",
    "\u{1f600}",
    "-",
    "_",
    "+",
    "=",
];

/// A random value: zero to five pieces.
fn random_value(rng: &mut Lcg) -> String {
    let mut s = String::new();
    for _ in 0..rng.below(6) {
        s.push_str(rng.pick(PIECES));
    }
    s
}

/// rust-url's href after `setter` = `value` on `start`.
fn theirs(start: &str, setter: &str, value: &str) -> Option<String> {
    let mut u = url::Url::parse(start).ok()?;
    // Each quirks setter reports whether it changed the URL; the URL API
    // ignores that, and so does this test.
    let _ = match setter {
        "protocol" => url::quirks::set_protocol(&mut u, value),
        "username" => url::quirks::set_username(&mut u, value),
        "password" => url::quirks::set_password(&mut u, value),
        "host" => url::quirks::set_host(&mut u, value),
        "hostname" => url::quirks::set_hostname(&mut u, value),
        "port" => url::quirks::set_port(&mut u, value),
        "pathname" => {
            url::quirks::set_pathname(&mut u, value);
            Ok(())
        }
        "search" => {
            url::quirks::set_search(&mut u, value);
            Ok(())
        }
        "hash" => {
            url::quirks::set_hash(&mut u, value);
            Ok(())
        }
        _ => return None,
    };
    Some(u.as_str().to_owned())
}

/// `s` with every `from` replaced by `to`.
fn replace(s: &[u32], from: &[u32], to: &[u32]) -> Vec<u32> {
    let mut out = Vec::new();
    let mut i = 0usize;
    while i < s.len() {
        if s.get(i..).is_some_and(|t| t.starts_with(from)) {
            out.extend_from_slice(to);
            i = i.saturating_add(from.len());
        } else {
            out.extend(s.get(i).copied());
            i = i.saturating_add(1);
        }
    }
    out
}

/// Our href after `setter` = `value` on `start`, adjusted for the place
/// where rust-url 2.5.8 is older than the standard, as in
/// `conformance_url.rs`: the path percent-encode set gained U+005E (^) in
/// whatwg/url `9bc33c39` (March 2025), so a path segment's "%5E" (which
/// only an encoded "^" produces from the pieces here) is written "^".
fn ours(start: &str, setter: &str, value: &str) -> Option<String> {
    let mut u = basic_url_parser(&scalars(start), None)?;
    set(&mut u, setter, value).ok()?;
    if let ParsedPath::List(l) = &mut u.path {
        for seg in l.iter_mut() {
            *seg = replace(seg, &[0x25, 0x35, 0x45], &[0x5E]);
        }
    }
    Some(string(&u.serialize(false)))
}

/// Our URL after `setter` = `value` on `start`, unadjusted.
fn ours_url(start: &str, setter: &str, value: &str) -> Option<ParsedUrl> {
    let mut u = basic_url_parser(&scalars(start), None)?;
    set(&mut u, setter, value).ok()?;
    Some(u)
}

/// The places where rust-url 2.5.8's setters contradict a named step of
/// the standard. Each is backed by a WPT `setters_tests.json` case that we
/// pass (named in the comment), so a mismatch in one of these classes is
/// rust-url's.
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Copy)]
enum Divergence {
    /// URL serializer step 3 writes "/." only while the host is null and
    /// path[0] is the empty string of a path of size above 1; rust-url
    /// keeps the "/." of `web+demo:/.//p` after the pathname, host or
    /// hostname setter changes either (WPT: <non-spec:/.//>.pathname = 'p'
    /// is <non-spec:/p>, "Drop /. from path"; <non-spec:/.//p>.hostname =
    /// 'h' is <non-spec://h//p>).
    StaleDotPrefix,
    /// The pathname setter empties the path and runs the path start state
    /// on the value as it is, after basic URL parser step 3 removes ASCII
    /// tab or newline; with a non-null host and nothing left, path start
    /// state steps 4 and 5 add no segment. rust-url puts a "/" in front of
    /// a value that does not start with one before removing tab or
    /// newline, so it adds an empty segment, and for a null host then
    /// omits the "/." that URL serializer step 3 writes (WPT:
    /// <foo://somehost/some/path>.pathname = '' is <foo://somehost>,
    /// "Non-special URLs can have their paths erased"; <foo:///some/path>
    /// is <foo://>).
    PathnameLeadingSlash,
    /// The path state keeps every empty segment of a file URL (the rule
    /// that removed leading empty segments of a file URL's path is gone
    /// from the standard); rust-url still removes them in the pathname
    /// setter (WPT: <file:///unicorn>.pathname = '//\\/' is
    /// <file://////>, "File URLs and (back)slashes").
    FileLeadingEmptySegments,
    /// With a file URL, host state step 1 hands c to the file host state,
    /// whose step 1.2.1 sets the host to the empty string when the value
    /// starts with "/", "\\", "?" or "#", or is only tab or newline
    /// (nothing before the delimiter or the EOF code point); rust-url
    /// leaves the host (WPT: <file://hi/x>.host = '' is <file:///x>, the
    /// same step at the EOF code point).
    FileHostEmptiedByDelimiter,
    /// Host state step 2.1: a ":" with an empty buffer returns failure and
    /// the URL is unchanged; rust-url sets an empty host on a non-special
    /// URL (WPT: <foo://path/to>.host = ':80' is unchanged).
    HostColonFirst,
    /// Port setter step 2 tests for the empty string before basic URL
    /// parser step 3 removes ASCII tab or newline, so a value of only tab
    /// or newline reaches port state step 2.2 and returns failure, leaving
    /// the port; rust-url removes the port (WPT:
    /// <https://domain.com:3000>.port = '\n\n\t\t' is unchanged).
    PortOnlyTabOrNewline,
    /// Scheme state step 2.1.3 forbids switching to "file" only for a URL
    /// that includes credentials or has a non-null port; rust-url also
    /// refuses for a URL with a non-empty host (WPT covers only the
    /// credentials and port cases, which we pass: <http://test@example.net>
    /// and <https://example.net:1234>.protocol = 'file' are unchanged).
    ProtocolFileWithHost,
}

/// `value` after basic URL parser step 3 (remove all ASCII tab or
/// newline).
fn without_tab_or_newline(value: &str) -> String {
    value
        .chars()
        .filter(|c| !matches!(c, '\t' | '\n' | '\r'))
        .collect()
}

/// Which divergence explains `ours_href` != `theirs_href`, if any.
fn divergence(
    start: &str,
    setter: &str,
    value: &str,
    ours_href: Option<&str>,
    theirs_href: Option<&str>,
) -> Option<Divergence> {
    let (Some(o), Some(t)) = (ours_href, theirs_href) else {
        return None;
    };
    let v = without_tab_or_newline(value);
    if start == "web+demo:/.//p"
        && matches!(setter, "pathname" | "host" | "hostname")
        && t.rfind("/./").is_some_and(|k| {
            format!(
                "{}{}",
                t.get(..k).unwrap_or(""),
                t.get(k.saturating_add(2)..).unwrap_or("")
            ) == o
        })
    {
        return Some(Divergence::StaleDotPrefix);
    }
    if setter == "pathname"
        && ours(start, setter, &format!("/{value}"))
            .is_some_and(|alt| alt == t || alt.replacen(":/./", ":/", 1) == t)
    {
        return Some(Divergence::PathnameLeadingSlash);
    }
    if setter == "pathname" && start.starts_with("file:") {
        let mut u = ours_url(start, setter, value)?;
        if let ParsedPath::List(l) = &mut u.path {
            while l.len() > 1 && l.first().is_some_and(Vec::is_empty) {
                l.remove(0);
            }
        }
        if string(&u.serialize(false)) == t {
            return Some(Divergence::FileLeadingEmptySegments);
        }
    }
    if start.starts_with("file:")
        && matches!(setter, "host" | "hostname")
        && !value.is_empty()
        && (v.is_empty() || v.starts_with(['/', '\\', '?', '#']))
        && t == start
        && ours_url(start, setter, value).is_some_and(|u| matches!(u.host, Some(ParsedHost::Empty)))
    {
        return Some(Divergence::FileHostEmptiedByDelimiter);
    }
    if setter == "host" && v.starts_with(':') && start_href(start).is_some_and(|h| h == o) {
        return Some(Divergence::HostColonFirst);
    }
    if setter == "port"
        && !value.is_empty()
        && v.is_empty()
        && start_href(start).is_some_and(|h| h == o)
    {
        return Some(Divergence::PortOnlyTabOrNewline);
    }
    if setter == "protocol"
        && v == "file"
        && o.starts_with("file://")
        && start_href(start).is_some_and(|h| h == t)
    {
        return Some(Divergence::ProtocolFileWithHost);
    }
    None
}

/// `start`'s href.
fn start_href(start: &str) -> Option<String> {
    basic_url_parser(&scalars(start), None).map(|u| string(&u.serialize(false)))
}

#[test]
fn differential_rust_url() {
    for start in START {
        let theirs_href = url::Url::parse(start).ok().map(|u| u.as_str().to_owned());
        assert!(start_href(start).is_some(), "{start:?} must parse");
        assert_eq!(start_href(start), theirs_href, "{start:?}");
    }
    let mut rng = Lcg(29);
    let mut agree = 0usize;
    let mut unexplained: Vec<String> = Vec::new();
    let mut explained: std::collections::BTreeMap<Divergence, usize> =
        std::collections::BTreeMap::new();
    let n = samples(200_000, 300);
    for _ in 0..n {
        let start = rng.pick(START);
        let setter = rng.pick(SETTERS);
        let value = random_value(&mut rng);
        let a = ours(start, setter, &value);
        let b = theirs(start, setter, &value);
        if a == b {
            agree = agree.saturating_add(1);
        } else if let Some(d) = divergence(start, setter, &value, a.as_deref(), b.as_deref()) {
            let count = explained.entry(d).or_insert(0);
            *count = count.saturating_add(1);
        } else {
            unexplained.push(format!(
                "<{start}>.{setter} = {value:?}: ours {a:?}, rust-url {b:?}"
            ));
        }
    }
    println!("rust-url agrees on {agree} of {n} cases; known divergences: {explained:?}");
    let shown: Vec<&String> = unexplained.iter().take(40).collect();
    assert!(
        unexplained.is_empty(),
        "{} unexplained mismatches:\n{:#?}",
        unexplained.len(),
        shown
    );
}
