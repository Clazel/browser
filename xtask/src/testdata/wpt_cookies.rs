//! WPT `cookies/`: the tests whose data is a literal table (or a few
//! string expressions) and whose body is `httpCookieTest(cookie, expected)`
//! or `domCookieTest(cookie, expected)`, as a table of cases.
//!
//! Each vendored page declares `const <table> = [ {cookie, expected, name,
//! defaultPath}, ... ]` and runs it in a `for (const test of <table>)` loop
//! (`name.html` also loops over a list of names). The converter reads the
//! table with the small expression reader below (string, template and
//! number literals, `+`, `.repeat(n)`, `.slice(n)`, and the helper
//! `cookieStringWithNameAndValueLengths` of `cookie-test.js`), and checks
//! that the page still has the loop text it expects, so an upstream change
//! fails the conversion instead of being misread. Strings are JavaScript
//! (UTF-16); a cookie goes over the wire, or into `document.cookie`, as the
//! UTF-8 of its string (`cookie.py` isomorphic-encodes the UTF-8 that
//! `JSON.stringify` and `encodeURIComponent` produced; a lone surrogate
//! becomes U+FFFD).
//!
//! A case is: the cookies to set (several `Set-Cookie` header values, or
//! several `document.cookie` assignments), the expected `document.cookie`
//! string, whether the cookie is set over HTTP (`Http`) or by script
//! (`Dom`), whether it is read at the default path of
//! `/cookies/resources/cookie.py` (`default_path`, the `echo-cookie.html`
//! frame) or at the test page, and the page.

use std::fmt::Write as _;
use std::path::Path;

use super::js::{Parser, find_all};

/// One page and how its tests run.
struct Page {
    file: &'static str,
    /// The page's path on the server.
    path: &'static str,
    https: bool,
    /// The table's name, as in `const <table> = [`.
    table: &'static str,
    /// Lines the page must contain, verbatim, saying how the table runs.
    required: &'static [&'static str],
    /// How the table's entries become cases: (Http or Dom, suffix of the name).
    runs: &'static [(&'static str, &'static str)],
}

const HTTP_LOOP: &str = "httpCookieTest(test.cookie, test.expected, test.name, test.defaultPath);";
const HTTP_LOOP_NO_PATH: &str = "httpCookieTest(test.cookie, test.expected, test.name);";

const PAGES: &[Page] = &[
    Page {
        file: "name.html",
        path: "/cookies/name/name.html",
        https: false,
        table: "nameTests",
        required: &["for (const test of nameTests) {", HTTP_LOOP_NO_PATH],
        runs: &[("Http", "")],
    },
    Page {
        file: "value.html",
        path: "/cookies/value/value.html",
        https: false,
        table: "valueTests",
        required: &["for (const test of valueTests) {", HTTP_LOOP],
        runs: &[("Http", "")],
    },
    Page {
        file: "expires.html",
        path: "/cookies/attributes/expires.html",
        https: false,
        table: "expiresTests",
        required: &[
            "httpCookieTest(test.cookie, test.expected, test.name + \" via HTTP headers\");",
            "domCookieTest(test.cookie, test.expected, test.name + \" via document.cookie\");",
        ],
        runs: &[
            ("Http", " via HTTP headers"),
            ("Dom", " via document.cookie"),
        ],
    },
    Page {
        file: "max-age.html",
        path: "/cookies/attributes/max-age.html",
        https: false,
        table: "maxAgeTests",
        required: &["for (const test of maxAgeTests) {", HTTP_LOOP_NO_PATH],
        runs: &[("Http", "")],
    },
    Page {
        file: "invalid.html",
        path: "/cookies/attributes/invalid.html",
        https: false,
        table: "invalidAttributeTests",
        required: &["for (const test of invalidAttributeTests) {", HTTP_LOOP],
        runs: &[("Http", "")],
    },
    Page {
        file: "path.html",
        path: "/cookies/attributes/path.html",
        https: false,
        table: "pathTests",
        required: &["for (const test of pathTests) {", HTTP_LOOP],
        runs: &[("Http", "")],
    },
    Page {
        file: "secure.https.html",
        path: "/cookies/attributes/secure.https.html",
        https: true,
        table: "secureTests",
        required: &["for (const test of secureTests) {", HTTP_LOOP],
        runs: &[("Http", "")],
    },
    Page {
        file: "charset.html",
        path: "/cookies/encoding/charset.html",
        https: false,
        table: "charsetTests",
        required: &["for (const test of charsetTests) {", HTTP_LOOP_NO_PATH],
        runs: &[("Http", "")],
    },
    Page {
        file: "name-and-value.html",
        path: "/cookies/size/name-and-value.html",
        https: false,
        table: "nameAndValueSizeTests",
        required: &[
            "for (const test of nameAndValueSizeTests) {",
            HTTP_LOOP_NO_PATH,
        ],
        runs: &[("Http", "")],
    },
];

/// The files vendored for this suite (besides LICENSE.md and SOURCE.md).
pub const FILES: &[&str] = &[
    "cookie-test.js",
    "name.html",
    "value.html",
    "expires.html",
    "max-age.html",
    "invalid.html",
    "path.html",
    "secure.https.html",
    "charset.html",
    "name-and-value.html",
];

/// Text `cookie-test.js` must contain, verbatim: what a test does.
const HELPER_REQUIRED: &[&str] = &[
    "function httpCookieTest(cookie, expectedValue, name, defaultPath = true,",
    "await fetch(`/cookies/resources/cookie.py?set=${encodedCookie}`);",
    "cookies = await getAndExpireCookiesForDefaultPathTest();",
    "iframe.src = '/cookies/resources/echo-cookie.html';",
    "function domCookieTest(cookie, expectedValue, name) {",
    "document.cookie = singlecookie;",
    "return `${\"t\".repeat(nameLength)}=${\"1\".repeat(valueLength)}`;",
];

/// A JavaScript value the tables use.
#[derive(Debug, Clone)]
enum V {
    Str(Vec<u16>),
    Num(u64),
    Bool(bool),
    Arr(Vec<V>),
}

fn add(l: V, r: V) -> Result<V, String> {
    match (l, r) {
        (V::Str(mut a), V::Str(b)) => {
            a.extend(b);
            Ok(V::Str(a))
        }
        (l, r) => Err(format!("cannot add {l:?} and {r:?}")),
    }
}

fn arg_num(args: &[V], i: usize) -> Result<u64, String> {
    match args.get(i) {
        Some(V::Num(n)) => Ok(*n),
        other => Err(format!("argument {i}: expected a number, found {other:?}")),
    }
}

fn units(s: &str) -> Vec<u16> {
    s.encode_utf16().collect()
}

fn repeat(s: &[u16], n: u64) -> Result<Vec<u16>, String> {
    let n = usize::try_from(n).map_err(|e| e.to_string())?;
    if n > 100_000 {
        return Err(format!("repeat({n}) is unreasonably long"));
    }
    Ok(s.repeat(n))
}

fn call(target: Option<V>, name: &str, args: &[V]) -> Result<V, String> {
    match (target, name) {
        (None, "cookieStringWithNameAndValueLengths") => {
            let mut s = repeat(&units("t"), arg_num(args, 0)?)?;
            s.extend(units("="));
            s.extend(repeat(&units("1"), arg_num(args, 1)?)?);
            Ok(V::Str(s))
        }
        (Some(V::Str(s)), "repeat") => Ok(V::Str(repeat(&s, arg_num(args, 0)?)?)),
        (Some(V::Str(s)), "slice") => {
            let from = usize::try_from(arg_num(args, 0)?).map_err(|e| e.to_string())?;
            Ok(V::Str(s.get(from..).unwrap_or_default().to_vec()))
        }
        (t, n) => Err(format!("unsupported call {n} on {t:?}")),
    }
}

fn args(p: &mut Parser) -> Result<Vec<V>, String> {
    p.expect("(")?;
    p.list(')', expr)
}

fn primary(p: &mut Parser) -> Result<V, String> {
    p.skip_trivia();
    match p.peek() {
        Some('`') => template(p),
        Some('"' | '\'') => {
            let node = p.literal()?;
            Ok(V::Str(node.str_units()?.to_vec()))
        }
        Some(c) if c.is_ascii_digit() => Ok(V::Num(p.literal()?.num()?)),
        Some('t' | 'f') if p.rest_starts_with("true") || p.rest_starts_with("false") => {
            Ok(V::Bool(p.literal()?.boolean()?))
        }
        Some('[') => {
            p.bump();
            Ok(V::Arr(p.list(']', value)?))
        }
        Some(c) if c.is_ascii_alphabetic() => {
            let name = p.ident()?;
            let a = args(p)?;
            call(None, &name, &a)
        }
        _ => p.err("expected an expression"),
    }
}

/// `` `text ${expr} text` ``.
fn template(p: &mut Parser) -> Result<V, String> {
    p.bump();
    let mut out: Vec<u16> = Vec::new();
    let mut buf = [0u16; 2];
    loop {
        let Some(c) = p.bump() else {
            return p.err("unterminated template");
        };
        match c {
            '`' => return Ok(V::Str(out)),
            '$' if p.peek() == Some('{') => {
                p.bump();
                let v = expr(p)?;
                p.expect("}")?;
                out = match add(V::Str(out), v)? {
                    V::Str(s) => s,
                    _ => return p.err("template part is not a string"),
                };
            }
            '\\' => {
                let e = p.bump();
                let unit = match e {
                    Some('n') => 0x0A,
                    Some('r') => 0x0D,
                    Some('t') => 0x09,
                    Some('`') => 0x60,
                    Some('$') => 0x24,
                    Some('\\') => 0x5C,
                    _ => return p.err("unsupported escape in template"),
                };
                out.push(unit);
            }
            c => out.extend_from_slice(c.encode_utf16(&mut buf)),
        }
    }
}

fn term(p: &mut Parser) -> Result<V, String> {
    let mut v = primary(p)?;
    loop {
        p.skip_trivia();
        if p.peek() != Some('.') {
            return Ok(v);
        }
        p.bump();
        let name = p.ident()?;
        let a = args(p)?;
        v = call(Some(v), &name, &a)?;
    }
}

fn expr(p: &mut Parser) -> Result<V, String> {
    let mut v = term(p)?;
    while p.eat("+") {
        let r = term(p)?;
        v = add(v, r)?;
    }
    Ok(v)
}

fn value(p: &mut Parser) -> Result<V, String> {
    expr(p)
}

/// One entry: an object with identifier keys and expression values.
fn entry(p: &mut Parser) -> Result<Vec<(String, V)>, String> {
    p.expect("{")?;
    p.list('}', |p| {
        let key = p.ident()?;
        p.expect(":")?;
        Ok((key, value(p)?))
    })
}

struct Case {
    file: &'static str,
    index: usize,
    name: String,
    page: &'static str,
    https: bool,
    http: bool,
    default_path: bool,
    cookies: Vec<Vec<u8>>,
    expected: Vec<u8>,
}

fn utf8(units: &[u16]) -> Vec<u8> {
    String::from_utf16_lossy(units).into_bytes()
}

fn string_of(v: &V, what: &str) -> Result<Vec<u16>, String> {
    match v {
        V::Str(s) => Ok(s.clone()),
        other => Err(format!("{what}: expected a string, found {other:?}")),
    }
}

fn read_text(dir: &Path, file: &str) -> Result<String, String> {
    std::fs::read_to_string(dir.join(file)).map_err(|e| format!("{file}: {e}"))
}

fn check_required(file: &str, text: &str, required: &[&str]) -> Result<(), String> {
    for r in required {
        if !text.contains(r) {
            return Err(format!("{file}: no longer contains {r:?}"));
        }
    }
    Ok(())
}

pub fn convert(dir: &Path) -> Result<String, String> {
    check_required(
        "cookie-test.js",
        &read_text(dir, "cookie-test.js")?,
        HELPER_REQUIRED,
    )?;
    let mut cases: Vec<Case> = Vec::new();
    for page in PAGES {
        let text = read_text(dir, page.file)?;
        check_required(page.file, &text, page.required)?;
        let marker = format!("const {} = [", page.table);
        let found = find_all(&text, &marker);
        let [pos] = found.as_slice() else {
            return Err(format!("{}: expected {marker:?} exactly once", page.file));
        };
        // `find_all` gives the position after the marker, which ends in "[".
        let mut p = Parser::at(&text, *pos);
        let entries = p
            .list(']', entry)
            .map_err(|e| format!("{}: {e}", page.file))?;
        for (index, fields) in entries.iter().enumerate() {
            let get = |k: &str| fields.iter().find(|(f, _)| f == k).map(|(_, v)| v);
            let bad = |what: &str| format!("{}[{index}]: {what}", page.file);
            let cookie = get("cookie").ok_or_else(|| bad("no cookie"))?;
            let cookies: Vec<Vec<u8>> = match cookie {
                V::Str(s) => vec![utf8(s)],
                V::Arr(items) => items
                    .iter()
                    .map(|v| string_of(v, "cookie").map(|s| utf8(&s)))
                    .collect::<Result<_, _>>()
                    .map_err(|e| bad(&e))?,
                other => return Err(bad(&format!("cookie is {other:?}"))),
            };
            let expected = string_of(
                get("expected").ok_or_else(|| bad("no expected"))?,
                "expected",
            )
            .map_err(|e| bad(&e))?;
            let name = string_of(get("name").ok_or_else(|| bad("no name"))?, "name")
                .map_err(|e| bad(&e))?;
            let default_path = match get("defaultPath") {
                None => true,
                Some(V::Bool(b)) => *b,
                Some(other) => return Err(bad(&format!("defaultPath is {other:?}"))),
            };
            for (via, suffix) in page.runs {
                let mut full = String::from_utf16_lossy(&name);
                full.push_str(suffix);
                cases.push(Case {
                    file: page.file,
                    index,
                    name: full,
                    page: page.path,
                    https: page.https,
                    http: *via == "Http",
                    default_path: default_path && *via == "Http",
                    cookies: cookies.clone(),
                    expected: utf8(&expected),
                });
            }
        }
    }
    // name.html's second loop: every name in a list is set to `<name>=test`.
    {
        let text = read_text(dir, "name.html")?;
        check_required(
            "name.html",
            &text,
            &[
                "const cookie = `${name}=test`;",
                "httpCookieTest(cookie, cookie, `Name is set as expected for ${name}=test`);",
            ],
        )?;
        let marker = "for (const name of ";
        let found = find_all(&text, marker);
        let [pos] = found.as_slice() else {
            return Err(format!("name.html: expected {marker:?} exactly once"));
        };
        let mut p = Parser::at(&text, *pos);
        let list = p.literal().map_err(|e| format!("name.html: {e}"))?;
        for (i, n) in list.array()?.iter().enumerate() {
            let name = String::from_utf16_lossy(n.str_units()?);
            let cookie = format!("{name}=test");
            cases.push(Case {
                file: "name.html",
                index: i,
                name: format!("Name is set as expected for {name}=test"),
                page: "/cookies/name/name.html",
                https: false,
                http: true,
                default_path: true,
                cookies: vec![cookie.clone().into_bytes()],
                expected: cookie.into_bytes(),
            });
        }
    }
    let mut out = String::new();
    out.push_str("// @generated by `cargo xtask testdata` from tests/data/wpt-cookies/.\n");
    out.push_str("// Do not edit: `cargo xtask verify` fails if this differs from what the\n");
    out.push_str("// converter (xtask/src/testdata/wpt_cookies.rs) produces.\n");
    out.push_str("// Source, commit and license: tests/data/wpt-cookies/SOURCE.md.\n");
    out.push_str("const WPT_COOKIES: &[Case] = &[\n");
    let bytes = |b: &[u8]| {
        let v: Vec<String> = b.iter().map(|x| format!("0x{x:02X}")).collect();
        format!("&[{}]", v.join(", "))
    };
    for c in &cases {
        let cookies: Vec<String> = c.cookies.iter().map(|b| bytes(b)).collect();
        writeln!(
            out,
            "    Case {{ file: {:?}, index: {}, name: {:?}, page: {:?}, https: {}, http: {}, default_path: {}, cookies: &[{}], expected: {} }},",
            c.file,
            c.index,
            c.name,
            c.page,
            c.https,
            c.http,
            c.default_path,
            cookies.join(", "),
            bytes(&c.expected),
        )
        .map_err(|e| e.to_string())?;
    }
    out.push_str("];\n");
    Ok(out)
}
