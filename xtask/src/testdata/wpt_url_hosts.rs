//! WPT `url/`: the host rows of `url/resources/urltestdata.json` (read by
//! `url/url-constructor.any.js`) and the rows of `url/resources/toascii.json`
//! (read by `url/toascii.window.js`), as tables of (name, host string,
//! isOpaque, expected serialized host or failure).
//!
//! The URL parser (item 1.10) does not exist yet, so the converter keeps
//! only rows where the host parser alone decides the outcome, and hands
//! the test the exact string the URL parser would give the host parser.
//! A `urltestdata.json` row is kept when its input is
//! `scheme://authority[rest]` with:
//! - no ASCII tab or newline anywhere, and no leading or trailing C0
//!   control or space (the URL parser removes or strips those first);
//! - a lowercase ASCII scheme (`[a-z][a-z0-9+.-]*`) other than `file`
//!   (file URLs have their own host state), followed by exactly `//`;
//! - an authority (up to the first `/`, `?` or `#`, or `\` for special
//!   schemes) with no `@` (no credentials) and no `:` outside `[...]` (no
//!   port);
//! - for a special scheme, a non-empty authority (an empty one is
//!   failure before the host parser runs, "host-missing").
//!
//! Then the URL parser's host state passes the authority to the host
//! parser, with isOpaque true for a non-special scheme (URL §4.4, host
//! state); nothing after the host can fail; a `failure` row fails in the
//! host parser and any other row's `hostname` is the serialized host. The
//! base URL is irrelevant: the input is absolute. A `toascii.json` row is
//! kept when its input, put between `https://` and `/x` as the test does,
//! gives an authority by the same rules (so no `/`, `?`, `#`, `\`, `@` or
//! port); then `hostname` is `output`, or the URL fails if `output` is
//! null. The converter checks that the vendored tests still say all this.

use std::fmt::Write as _;
use std::path::Path;

use serde_json::Value;

/// The files vendored for this suite (besides LICENSE.md and SOURCE.md).
pub const FILES: &[&str] = &[
    "toascii.json",
    "toascii.window.js",
    "url-constructor.any.js",
    "urltestdata.json",
];

/// Text the tests must contain, verbatim.
const REQUIRED: &[(&str, &str)] = &[
    (
        "url-constructor.any.js",
        "assert_equals(url.hostname, expected.hostname, \"hostname\")",
    ),
    (
        "url-constructor.any.js",
        "}, `Parsing: <${expected.input}> ${base ? \"against <\" + base + \">\" : \"without base\"}`)",
    ),
    ("toascii.window.js", "input = \"https://\" + input + \"/x\""),
    (
        "toascii.window.js",
        "assert_equals(url.hostname, hostTest.output)",
    ),
    (
        "toascii.window.js",
        "assert_throws_js(TypeError, () => makeURL(\"url\", hostTest.input))",
    ),
    (
        "toascii.window.js",
        "}, hostTest.input + \" (using \" + typeName[type] + \")\")",
    ),
];

/// URL §4.1: the special schemes, other than "file".
const SPECIAL: &[&str] = &["ftp", "http", "https", "ws", "wss"];

struct Case {
    name: String,
    input: Vec<u32>,
    opaque: bool,
    expected: Option<Vec<u32>>,
}

/// The host string and isOpaque the URL parser passes to the host parser
/// for `input`, if the rules in the module comment hold.
fn host_of(input: &str) -> Option<(String, bool)> {
    let chars: Vec<char> = input.chars().collect();
    if chars.iter().any(|&c| matches!(c, '\t' | '\n' | '\r')) {
        return None;
    }
    let edge = |c: Option<&char>| c.is_some_and(|&c| c <= ' ');
    if edge(chars.first()) || edge(chars.last()) {
        return None;
    }
    let colon = input.find(':')?;
    let (scheme, rest) = input.split_at(colon);
    let mut scheme_chars = scheme.chars();
    let first_ok = scheme_chars.next().is_some_and(|c| c.is_ascii_lowercase());
    let rest_ok = scheme_chars
        .all(|c| c.is_ascii_lowercase() || c.is_ascii_digit() || matches!(c, '+' | '-' | '.'));
    if !first_ok || !rest_ok || scheme == "file" {
        return None;
    }
    let after = rest.strip_prefix("://")?;
    let special = SPECIAL.contains(&scheme);
    let end = after
        .find(|c: char| matches!(c, '/' | '?' | '#') || (special && c == '\\'))
        .unwrap_or(after.len());
    let authority = &after[..end];
    if authority.contains('@') {
        return None;
    }
    let mut inside = false;
    for c in authority.chars() {
        match c {
            '[' => inside = true,
            ']' => inside = false,
            ':' if !inside => return None,
            _ => {}
        }
    }
    if special && authority.is_empty() {
        return None;
    }
    Some((authority.to_owned(), !special))
}

fn code_points(s: &str) -> Vec<u32> {
    s.chars().map(u32::from).collect()
}

/// Convert the suite in `dir` to the body of a Rust source file.
pub fn convert(dir: &Path) -> Result<String, String> {
    for (file, needle) in REQUIRED {
        let path = dir.join(file);
        let text =
            std::fs::read_to_string(&path).map_err(|e| format!("{}: {e}", path.display()))?;
        if text.matches(needle).count() != 1 {
            return Err(format!(
                "{file}: expected {needle:?} exactly once; the test changed upstream"
            ));
        }
    }
    let read = |name: &str| -> Result<Vec<Value>, String> {
        let path = dir.join(name);
        let text =
            std::fs::read_to_string(&path).map_err(|e| format!("{}: {e}", path.display()))?;
        let json: Value =
            serde_json::from_str(&text).map_err(|e| format!("{name}: not JSON: {e}"))?;
        json.as_array()
            .cloned()
            .ok_or_else(|| format!("{name}: expected a top-level array"))
    };

    let mut url_cases = Vec::new();
    let mut url_rows = 0usize;
    for (k, row) in read("urltestdata.json")?.iter().enumerate() {
        if row.is_string() {
            continue;
        }
        url_rows = url_rows.saturating_add(1);
        let at = |what: &str| format!("urltestdata.json: item {k}: {what}");
        let input = row
            .get("input")
            .and_then(Value::as_str)
            .ok_or_else(|| at("no string \"input\""))?;
        let base = match row.get("base") {
            Some(Value::String(b)) => Some(b.as_str()),
            Some(Value::Null) => None,
            _ => return Err(at("\"base\" is not a string or null")),
        };
        let Some((host, opaque)) = host_of(input) else {
            continue;
        };
        let failure = row.get("failure").and_then(Value::as_bool).unwrap_or(false);
        let expected = if failure {
            None
        } else {
            let hostname = row
                .get("hostname")
                .and_then(Value::as_str)
                .ok_or_else(|| at("no string \"hostname\""))?;
            let host_field = row
                .get("host")
                .and_then(Value::as_str)
                .ok_or_else(|| at("no string \"host\""))?;
            if host_field != hostname {
                return Err(at(
                    "\"host\" differs from \"hostname\", but the input has no port",
                ));
            }
            Some(code_points(hostname))
        };
        let name = match base {
            Some(b) => format!("Parsing: <{input}> against <{b}>"),
            None => format!("Parsing: <{input}> without base"),
        };
        url_cases.push(Case {
            name,
            input: code_points(&host),
            opaque,
            expected,
        });
    }

    let mut toascii_cases = Vec::new();
    let mut toascii_rows = 0usize;
    for (k, row) in read("toascii.json")?.iter().enumerate() {
        if row.is_string() {
            continue;
        }
        toascii_rows = toascii_rows.saturating_add(1);
        let at = |what: &str| format!("toascii.json: item {k}: {what}");
        let input = row
            .get("input")
            .and_then(Value::as_str)
            .ok_or_else(|| at("no string \"input\""))?;
        let expected = match row.get("output") {
            Some(Value::String(o)) => Some(code_points(o)),
            Some(Value::Null) => None,
            _ => return Err(at("\"output\" is not a string or null")),
        };
        let url = format!("https://{input}/x");
        let Some((host, opaque)) = host_of(&url) else {
            continue;
        };
        if host != input || opaque {
            continue;
        }
        toascii_cases.push(Case {
            name: format!("{input} (using URL)"),
            input: code_points(input),
            opaque,
            expected,
        });
    }
    if url_cases.is_empty() || toascii_cases.is_empty() {
        return Err("no host cases converted".into());
    }
    render(&url_cases, url_rows, &toascii_cases, toascii_rows)
}

fn render(
    url: &[Case],
    url_rows: usize,
    toascii: &[Case],
    toascii_rows: usize,
) -> Result<String, String> {
    let mut out = String::new();
    out.push_str(
        "// @generated by `cargo xtask testdata` from tests/data/wpt-url-hosts/.\n\
         // Do not edit: `cargo xtask verify` fails if this differs from what the\n\
         // converter (xtask/src/testdata/wpt_url_hosts.rs) produces.\n\
         // Source, commit and license: tests/data/wpt-url-hosts/SOURCE.md.\n",
    );
    writeln!(
        out,
        "// urltestdata.json: {} of {url_rows} rows are host rows; toascii.json: {} of {toascii_rows} rows.",
        url.len(),
        toascii.len()
    )
    .map_err(|e| e.to_string())?;
    for (table, cases) in [("URLTESTDATA", url), ("TOASCII", toascii)] {
        writeln!(out, "const {table}: &[Case] = &[").map_err(|e| e.to_string())?;
        for c in cases {
            let list = |v: &[u32]| {
                v.iter()
                    .map(|u| format!("0x{u:04X}"))
                    .collect::<Vec<_>>()
                    .join(", ")
            };
            let expected = match &c.expected {
                Some(e) => format!("Some(&[{}])", list(e)),
                None => "None".to_owned(),
            };
            writeln!(
                out,
                "    Case {{ name: {:?}, input: &[{}], opaque: {}, expected: {} }},",
                c.name,
                list(&c.input),
                c.opaque,
                expected
            )
            .map_err(|e| e.to_string())?;
        }
        out.push_str("];\n");
    }
    Ok(out)
}

#[cfg(test)]
mod tests {
    use super::host_of;

    #[test]
    fn host_strings() {
        assert_eq!(
            host_of("http://example.com/x"),
            Some(("example.com".into(), false))
        );
        assert_eq!(host_of("sc://ñ?x"), Some(("ñ".into(), true)));
        assert_eq!(host_of("http://[::1]/"), Some(("[::1]".into(), false)));
        assert_eq!(host_of("http://a\\b"), Some(("a".into(), false)));
        assert_eq!(host_of("sc://a\\b/"), Some(("a\\b".into(), true)));
        assert_eq!(host_of("sc:///x"), Some((String::new(), true)));
        // Ports, credentials, file URLs, missing hosts, stripped code points.
        assert_eq!(host_of("http://a:80/"), None);
        assert_eq!(host_of("http://[::1]:80/"), None);
        assert_eq!(host_of("http://u@a/"), None);
        assert_eq!(host_of("file://a/"), None);
        assert_eq!(host_of("http:///a"), None);
        assert_eq!(host_of(" http://a/"), None);
        assert_eq!(host_of("http://a\tb/"), None);
        assert_eq!(host_of("HTTP://a/"), None);
        assert_eq!(host_of("http:/a/"), None);
    }
}
