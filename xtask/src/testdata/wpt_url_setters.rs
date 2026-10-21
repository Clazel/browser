//! WPT `url/`: every case of `url/resources/setters_tests.json` (read by
//! `url/url-setters.any.js`), as a table of (name, setter, href, new
//! value, expected getters).
//!
//! A case is `const url = new URL(href); url[setter] = new_value;` and then
//! each getter named in `expected` is compared with its value. The
//! converter checks that the vendored test still says all this.

use std::fmt::Write as _;
use std::path::Path;

use serde_json::Value;

/// The files vendored for this suite (besides LICENSE.md and SOURCE.md).
pub const FILES: &[&str] = &["setters_tests.json", "url-setters.any.js"];

/// Text the test must contain, verbatim.
const REQUIRED: &[&str] = &[
    "for (const [propertyToBeSet, testCases] of Object.entries(allTestCases)) {",
    "if (propertyToBeSet === \"comment\") {",
    "const name = `Setting <${test_case.href}>.${propertyToBeSet} = '${test_case.new_value}'${",
    "test_case.comment ? ` ${test_case.comment}` : ''",
    "const url = new URL(test_case.href);",
    "url[propertyToBeSet] = test_case.new_value;",
    "for (const [property, expectedValue] of Object.entries(test_case.expected)) {",
    "assert_equals(url[property], expectedValue);",
    "}, `URL: ${name}`);",
];

/// The setters (and getters) a case may name.
const ATTRIBUTES: &[&str] = &[
    "href", "protocol", "username", "password", "host", "hostname", "port", "pathname", "search",
    "hash",
];

struct Case {
    name: String,
    setter: String,
    href: String,
    new_value: String,
    expected: Vec<(String, String)>,
}

fn attribute(what: &str, name: &str) -> Result<String, String> {
    if ATTRIBUTES.contains(&name) {
        Ok(name.to_owned())
    } else {
        Err(format!(
            "setters_tests.json: {what} {name:?} is not a URL attribute"
        ))
    }
}

/// Convert the suite in `dir` to the body of a Rust source file.
pub fn convert(dir: &Path) -> Result<String, String> {
    let js = dir.join("url-setters.any.js");
    let text = std::fs::read_to_string(&js).map_err(|e| format!("{}: {e}", js.display()))?;
    for needle in REQUIRED {
        if !text.contains(needle) {
            return Err(format!(
                "url-setters.any.js: expected {needle:?}; the test changed upstream"
            ));
        }
    }
    let path = dir.join("setters_tests.json");
    let text = std::fs::read_to_string(&path).map_err(|e| format!("{}: {e}", path.display()))?;
    let json: Value =
        serde_json::from_str(&text).map_err(|e| format!("setters_tests.json: not JSON: {e}"))?;
    let groups = json
        .as_object()
        .ok_or("setters_tests.json: expected a top-level object")?;

    let mut cases = Vec::new();
    for (key, group) in groups {
        if key == "comment" {
            continue;
        }
        let setter = attribute("key", key)?;
        let rows = group
            .as_array()
            .ok_or_else(|| format!("setters_tests.json: {key:?} is not an array"))?;
        for (k, row) in rows.iter().enumerate() {
            let at = |what: &str| format!("setters_tests.json: {key}[{k}]: {what}");
            let field = |f: &str| {
                row.get(f)
                    .and_then(Value::as_str)
                    .ok_or_else(|| at(&format!("no string {f:?}")))
            };
            let href = field("href")?;
            let new_value = field("new_value")?;
            let comment = match row.get("comment") {
                None => None,
                Some(Value::String(c)) => Some(c.as_str()),
                Some(_) => return Err(at("\"comment\" is not a string")),
            };
            let expected_obj = row
                .get("expected")
                .and_then(Value::as_object)
                .ok_or_else(|| at("no object \"expected\""))?;
            let mut expected = Vec::new();
            for (getter, value) in expected_obj {
                let value = value
                    .as_str()
                    .ok_or_else(|| at(&format!("expected {getter:?} is not a string")))?;
                expected.push((attribute("getter", getter)?, value.to_owned()));
            }
            if expected.is_empty() {
                return Err(at("\"expected\" is empty"));
            }
            // The test's name, as url-setters.any.js builds it.
            let name = match comment {
                Some(c) if !c.is_empty() => {
                    format!("URL: Setting <{href}>.{setter} = '{new_value}' {c}")
                }
                _ => format!("URL: Setting <{href}>.{setter} = '{new_value}'"),
            };
            cases.push(Case {
                name,
                setter: setter.clone(),
                href: href.to_owned(),
                new_value: new_value.to_owned(),
                expected,
            });
        }
    }
    if cases.is_empty() {
        return Err("setters_tests.json: no cases".into());
    }
    render(&cases)
}

fn render(cases: &[Case]) -> Result<String, String> {
    let mut out = String::new();
    out.push_str(
        "// @generated by `cargo xtask testdata` from tests/data/wpt-url-setters/.\n\
         // Do not edit: `cargo xtask verify` fails if this differs from what the\n\
         // converter (xtask/src/testdata/wpt_url_setters.rs) produces.\n\
         // Source, commit and license: tests/data/wpt-url-setters/SOURCE.md.\n",
    );
    writeln!(out, "// setters_tests.json: {} cases.", cases.len()).map_err(|e| e.to_string())?;
    out.push_str("const SETTERS_TESTS: &[Case] = &[\n");
    for c in cases {
        let mut expected = String::from("&[");
        for (getter, value) in &c.expected {
            write!(expected, "({getter:?}, {value:?}), ").map_err(|e| e.to_string())?;
        }
        expected.push(']');
        writeln!(
            out,
            "    Case {{ name: {:?}, setter: {:?}, href: {:?}, new_value: {:?}, expected: {expected} }},",
            c.name, c.setter, c.href, c.new_value
        )
        .map_err(|e| e.to_string())?;
    }
    out.push_str("];\n");
    Ok(out)
}
