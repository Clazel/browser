//! WPT `url/IdnaTestV2.any.js` and `url/toascii.window.js`: their data
//! files `url/resources/IdnaTestV2.json` and `url/resources/toascii.json`,
//! as tables of (input code points, expected host or failure).
//!
//! Both tests parse `https://<input>/x` with `new URL()` and compare the
//! host with the output, or expect a `TypeError` for `null`. For a special
//! URL, the host parser percent-decodes the host, runs the URL Standard's
//! "domain parser" with beStrict false, and then, if the result ends in a
//! number, parses it as IPv4. The converter turns each row into a case for
//! the domain parser directly, and refuses rows where that could differ
//! (see `check_direct`), so an upstream row that needs the URL layer fails
//! the conversion instead of being silently misread. The converter also
//! checks that the two test files still run the data that way.
//!
//! JavaScript strings may hold lone surrogates; `new URL()` takes a
//! USVString, whose conversion replaces each with U+FFFD (WebIDL), and so
//! does the converter, before parsing the JSON (whose parser rejects them).

use std::fmt::Write as _;
use std::path::Path;

use serde_json::Value;

/// The files vendored for this suite (besides LICENSE.md and SOURCE.md).
pub const FILES: &[&str] = &[
    "IdnaTestV2.any.js",
    "IdnaTestV2.json",
    "toascii.json",
    "toascii.window.js",
];

/// Text the tests must contain, verbatim.
const REQUIRED: &[(&str, &str)] = &[
    (
        "IdnaTestV2.any.js",
        "assert_throws_js(TypeError, () => new URL(`https://${idnaTest.input}/x`));",
    ),
    (
        "IdnaTestV2.any.js",
        "const url = new URL(`https://${idnaTest.input}/x`);",
    ),
    (
        "IdnaTestV2.any.js",
        "assert_equals(url.host, idnaTest.output);",
    ),
    ("IdnaTestV2.any.js", "if (idnaTest.input === \"\") {"),
    ("toascii.window.js", "input = \"https://\" + input + \"/x\""),
    (
        "toascii.window.js",
        "assert_equals(url.host, hostTest.output)",
    ),
    (
        "toascii.window.js",
        "assert_throws_js(TypeError, () => makeURL(\"url\", hostTest.input))",
    ),
];

struct Case {
    line: usize,
    name: String,
    input: Vec<u32>,
    output: Option<Vec<u32>>,
}

/// Replace JSON `\uXXXX` escapes of lone surrogates by `�`.
fn replace_lone_surrogates(text: &str) -> String {
    let surrogate = |s: &str| -> Option<u32> {
        let hex = s.get(2..6)?;
        let v = u32::from_str_radix(hex, 16).ok()?;
        (s.starts_with("\\u") && (0xD800..=0xDFFF).contains(&v)).then_some(v)
    };
    let mut out = String::with_capacity(text.len());
    let mut rest = text;
    while let Some(i) = rest.find("\\u") {
        let (before, at) = rest.split_at(i);
        out.push_str(before);
        match surrogate(at) {
            Some(high @ 0xD800..=0xDBFF) => {
                let next = at.get(6..).unwrap_or("");
                if surrogate(next).is_some_and(|low| (0xDC00..=0xDFFF).contains(&low)) {
                    out.push_str(at.get(..12).unwrap_or(at));
                    rest = at.get(12..).unwrap_or("");
                } else {
                    let _ = high;
                    out.push_str("\\uFFFD");
                    rest = next;
                }
            }
            Some(_) => {
                out.push_str("\\uFFFD");
                rest = at.get(6..).unwrap_or("");
            }
            None => {
                out.push_str(at.get(..2).unwrap_or(at));
                rest = at.get(2..).unwrap_or("");
            }
        }
    }
    out.push_str(rest);
    out
}

/// Rows where the URL layer could change the result.
///
/// For `https://<input>/x`, the URL parser removes ASCII tab or newline
/// anywhere, ends the host at `/`, `?`, `#` or `\`, takes everything up
/// to `@` as credentials, ends the host at `:` (port), and treats `[` as
/// an IPv6 address; the host parser then percent-decodes `%XX`. A host
/// that ends in a number goes to the IPv4 parser. Those rows are refused.
fn check_direct(input: &str, output: Option<&str>) -> Result<(), String> {
    if let Some(c) = input.chars().find(|c| {
        matches!(
            c,
            '\t' | '\n' | '\r' | '/' | '?' | '#' | '\\' | '@' | ':' | '['
        )
    }) {
        return Err(format!("contains {c:?}, which the URL parser handles"));
    }
    let bytes = input.as_bytes();
    for (i, &b) in bytes.iter().enumerate() {
        let hex = |k: usize| {
            bytes
                .get(i.saturating_add(k))
                .is_some_and(u8::is_ascii_hexdigit)
        };
        if b == b'%' && hex(1) && hex(2) {
            return Err("contains a percent-encoded byte, which the host parser decodes".into());
        }
    }
    let host = output.unwrap_or(input);
    let mut labels: Vec<&str> = host.split('.').collect();
    if labels.len() > 1 && labels.last() == Some(&"") {
        labels.pop();
    }
    let last = labels.last().copied().unwrap_or("");
    let numeric = !last.is_empty() && last.bytes().all(|b| b.is_ascii_digit());
    let hex = (last.starts_with("0x") || last.starts_with("0X"))
        && last.bytes().skip(2).all(|b| b.is_ascii_hexdigit());
    if numeric || hex {
        return Err("ends in a number, which the IPv4 parser handles".into());
    }
    Ok(())
}

fn cases(
    dir: &Path,
    file: &str,
    name: &dyn Fn(&str, Option<&str>) -> String,
) -> Result<Vec<Case>, String> {
    let path = dir.join(file);
    let text = std::fs::read_to_string(&path).map_err(|e| format!("{}: {e}", path.display()))?;
    let json: Value = serde_json::from_str(&replace_lone_surrogates(&text))
        .map_err(|e| format!("{file}: not JSON: {e}"))?;
    let rows = json
        .as_array()
        .ok_or(format!("{file}: expected an array"))?;
    // The line of each `"input":` key, in order.
    let lines: Vec<usize> = text
        .lines()
        .enumerate()
        .filter(|(_, l)| l.trim_start().starts_with("\"input\":"))
        .map(|(i, _)| i.saturating_add(1))
        .collect();
    let objects: Vec<&Value> = rows.iter().filter(|r| !r.is_string()).collect();
    if objects.len() != lines.len() {
        return Err(format!(
            "{file}: {} rows but {} \"input\" lines; expected one per row",
            objects.len(),
            lines.len()
        ));
    }
    let mut out = Vec::new();
    for (row, line) in objects.into_iter().zip(lines) {
        let at = |what: &str| format!("{file}:{line}: {what}");
        let input = row
            .get("input")
            .and_then(Value::as_str)
            .ok_or_else(|| at("no string \"input\""))?;
        let output = match row.get("output") {
            Some(Value::Null) => None,
            Some(Value::String(s)) => Some(s.as_str()),
            _ => return Err(at("\"output\" is neither a string nor null")),
        };
        // "cannot test empty string input through new URL()"
        if input.is_empty() {
            continue;
        }
        check_direct(input, output).map_err(|e| at(&e))?;
        let comment = row.get("comment").and_then(Value::as_str);
        out.push(Case {
            line,
            name: name(input, comment),
            input: input.chars().map(u32::from).collect(),
            output: output.map(|o| o.chars().map(u32::from).collect()),
        });
    }
    Ok(out)
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
    let idna = cases(dir, "IdnaTestV2.json", &|input, comment| match comment {
        Some(c) => format!("ToASCII(\"{input}\") {c}"),
        None => format!("ToASCII(\"{input}\")"),
    })?;
    let toascii = cases(dir, "toascii.json", &|input, _| {
        format!("{input} (using URL)")
    })?;
    let mut out = String::new();
    out.push_str(
        "// @generated by `cargo xtask testdata` from tests/data/wpt-url-idna/.\n\
         // Do not edit: `cargo xtask verify` fails if this differs from what the\n\
         // converter (xtask/src/testdata/wpt_idna.rs) produces.\n\
         // Source, commit and license: tests/data/wpt-url-idna/SOURCE.md.\n",
    );
    for (name, file, list) in [
        ("IDNA_TEST_V2", "IdnaTestV2.json", &idna),
        ("TOASCII", "toascii.json", &toascii),
    ] {
        writeln!(out, "const {name}: &[Case] = &[").map_err(|e| e.to_string())?;
        for c in list {
            let input: Vec<String> = c.input.iter().map(|u| format!("0x{u:04X}")).collect();
            let output = match &c.output {
                Some(o) => {
                    let o: Vec<String> = o.iter().map(|u| format!("0x{u:04X}")).collect();
                    format!("Some(&[{}])", o.join(", "))
                }
                None => "None".into(),
            };
            writeln!(
                out,
                "    Case {{ file: {file:?}, line: {}, name: {:?}, input: &[{}], output: {output} }},",
                c.line,
                c.name,
                input.join(", ")
            )
            .map_err(|e| e.to_string())?;
        }
        out.push_str("];\n");
    }
    Ok(out)
}

#[cfg(test)]
mod tests {
    use super::{check_direct, replace_lone_surrogates};

    #[test]
    fn surrogates() {
        assert_eq!(replace_lone_surrogates("\"a\\ud900z\""), "\"a\\uFFFDz\"");
        assert_eq!(
            replace_lone_surrogates("\"\\ud83d\\ude00\""),
            "\"\\ud83d\\ude00\""
        );
        assert_eq!(
            replace_lone_surrogates("\"\\udc00\\u0041\""),
            "\"\\uFFFD\\u0041\""
        );
    }

    #[test]
    fn direct() {
        assert!(check_direct("a.b", Some("a.b")).is_ok());
        assert!(check_direct("a%.b", None).is_ok());
        assert!(check_direct("a%41.b", None).is_err());
        assert!(check_direct("a/b", None).is_err());
        assert!(check_direct("a.1", Some("a.1")).is_err());
        assert!(check_direct("a.0x1f.", None).is_err());
    }
}
