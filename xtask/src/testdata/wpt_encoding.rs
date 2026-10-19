//! WPT `encoding/`: the UTF-8 decode cases, as a table of
//! (input bytes, hook, expected scalar values or failure).
//!
//! WPT keeps these as JavaScript, not JSON. Each rule below names the file
//! and the literal it reads; the literal must appear exactly where the rule
//! says, so an upstream change that moves or reshapes it fails the
//! conversion rather than dropping cases.
//!
//! How the Encoding API maps onto the Encoding Standard's hooks (Encoding
//! §7.2 `TextDecoder.decode()`):
//! - `new TextDecoder()` / `new TextDecoder('utf-8')`: BOM sniffing, then
//!   replacement errors: "UTF-8 decode".
//! - `ignoreBOM: true`: no BOM handling: "UTF-8 decode without BOM".
//! - `fatal: true`: BOM handling, then fatal errors. On input that does not
//!   start with a UTF-8 BOM this is "UTF-8 decode without BOM or fail"; the
//!   converter checks that no fatal case starts with one.

use std::fmt::Write as _;
use std::path::Path;

use super::js::{Node, Parser, find_all, scalars};

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum Hook {
    Decode,
    DecodeWithoutBom,
    DecodeWithoutBomOrFail,
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord)]
struct Case {
    file: &'static str,
    line: usize,
    hook: Hook,
    name: String,
    input: Vec<u8>,
    /// `None`: the decoder must fail (a `TypeError` in the API).
    expected: Option<Vec<u32>>,
}

const BOM: [u8; 3] = [0xEF, 0xBB, 0xBF];

/// The files vendored for this suite (besides LICENSE.md and SOURCE.md).
pub const FILES: &[&str] = &[
    "api-basics.any.js",
    "api-surrogates-utf8.any.js",
    "textdecoder-byte-order-marks.any.js",
    "textdecoder-eof.any.js",
    "textdecoder-fatal-streaming.any.js",
    "textdecoder-fatal.any.js",
    "textdecoder-ignorebom.any.js",
    "textdecoder-mistakes.any.js",
];

struct Source {
    file: &'static str,
    text: String,
}

impl Source {
    /// The literal right after the only occurrence of `marker`.
    fn after_only(&self, marker: &str) -> Result<Node, String> {
        match find_all(&self.text, marker).as_slice() {
            [pos] => Parser::at(&self.text, *pos).literal(),
            found => Err(format!(
                "{}: expected {marker:?} exactly once, found {} times",
                self.file,
                found.len()
            )),
        }
        .map_err(|e| format!("{}: {e}", self.file))
    }

    /// The literal right after the first occurrence of `marker`.
    fn after_first(&self, marker: &str) -> Result<Node, String> {
        let pos = find_all(&self.text, marker)
            .first()
            .copied()
            .ok_or_else(|| format!("{}: no {marker:?}", self.file))?;
        Parser::at(&self.text, pos)
            .literal()
            .map_err(|e| format!("{}: {e}", self.file))
    }

    fn case(
        &self,
        line: usize,
        hook: Hook,
        name: String,
        input: Vec<u8>,
        expected: Option<Vec<u32>>,
    ) -> Case {
        Case {
            file: self.file,
            line,
            hook,
            name,
            input,
            expected,
        }
    }
}

fn is_utf8(n: &Node) -> Result<bool, String> {
    Ok(n.string()?.eq_ignore_ascii_case("utf-8"))
}

fn string_scalars(n: &Node) -> Result<Vec<u32>, String> {
    scalars(n.str_units()?).map_err(|e| format!("line {}: {e}", n.line))
}

/// Convert the suite in `dir` to the body of a Rust source file.
pub fn convert(dir: &Path) -> Result<String, String> {
    let mut sources = Vec::new();
    for file in FILES {
        let path = dir.join(file);
        let text =
            std::fs::read_to_string(&path).map_err(|e| format!("{}: {e}", path.display()))?;
        sources.push(Source { file, text });
    }
    let get = |file: &str| {
        sources
            .iter()
            .find(|s| s.file == file)
            .ok_or_else(|| format!("{file}: not loaded"))
    };
    let mut cases = Vec::new();

    // textdecoder-fatal.any.js: `var bad = [{encoding, input, name}, ...]`,
    // each decoded with `{fatal: true}` and expected to throw.
    let s = get("textdecoder-fatal.any.js")?;
    for row in s.after_only("var bad = ")?.array()? {
        if !is_utf8(row.field("encoding")?)? {
            continue;
        }
        let input = row.field("input")?.bytes()?;
        if input.starts_with(&BOM) {
            return Err(format!(
                "{}:{}: fatal case starts with a BOM",
                s.file, row.line
            ));
        }
        let name = format!("Fatal flag: utf-8 - {}", row.field("name")?.string()?);
        cases.push(s.case(row.line, Hook::DecodeWithoutBomOrFail, name, input, None));
    }

    // textdecoder-fatal-streaming.any.js, "Fatal flag, non-streaming cases":
    // an inline `[{encoding, sequence}, ...]`; fatal must throw, and the
    // replacement decoder must return the literal after the decode call.
    let s = get("textdecoder-fatal-streaming.any.js")?;
    let rows = s.after_only("test(function() {\n    ")?;
    let replaced = s.after_only(
        "new TextDecoder(testCase.encoding).decode(new Uint8Array([testCase.sequence])),",
    )?;
    for row in rows.array()? {
        if !is_utf8(row.field("encoding")?)? {
            continue;
        }
        let input = row.field("sequence")?.bytes()?;
        if input.starts_with(&BOM) {
            return Err(format!(
                "{}:{}: fatal case starts with a BOM",
                s.file, row.line
            ));
        }
        let name = "Fatal flag, non-streaming cases: utf-8".to_owned();
        cases.push(s.case(
            row.line,
            Hook::DecodeWithoutBomOrFail,
            name.clone(),
            input.clone(),
            None,
        ));
        cases.push(s.case(
            row.line,
            Hook::Decode,
            name,
            input,
            Some(string_scalars(&replaced)?),
        ));
    }

    // textdecoder-mistakes.any.js: `const invalid8 = [{bytes, charcodes}]`,
    // "Invalid Unicode input is replaced: utf-8".
    let s = get("textdecoder-mistakes.any.js")?;
    for row in s.after_only("const invalid8 = ")?.array()? {
        let units: Vec<u16> = row
            .field("charcodes")?
            .array()?
            .iter()
            .map(|n| {
                let v = n.num()?;
                u16::try_from(v).map_err(|_| format!("line {}: {v} is not a char code", n.line))
            })
            .collect::<Result<_, _>>()?;
        let expected = scalars(&units).map_err(|e| format!("{}:{}: {e}", s.file, row.line))?;
        let name = "Invalid Unicode input is replaced: utf-8".to_owned();
        cases.push(s.case(
            row.line,
            Hook::Decode,
            name,
            row.field("bytes")?.bytes()?,
            Some(expected),
        ));
    }

    // textdecoder-byte-order-marks.any.js: `var testCases = [{encoding, bom,
    // bytes}]` and `var string`; the bytes decode to `string` with and
    // without their own BOM in front.
    let s = get("textdecoder-byte-order-marks.any.js")?;
    let expected = string_scalars(&s.after_only("var string = ")?)?;
    for row in s.after_only("var testCases = ")?.array()? {
        if !is_utf8(row.field("encoding")?)? {
            continue;
        }
        let bytes = row.field("bytes")?.bytes()?;
        let mut with_bom = row.field("bom")?.bytes()?;
        with_bom.extend_from_slice(&bytes);
        let name = "Byte-order marks: utf-8".to_owned();
        cases.push(s.case(
            row.line,
            Hook::Decode,
            format!("{name} (no BOM)"),
            bytes,
            Some(expected.clone()),
        ));
        cases.push(s.case(
            row.line,
            Hook::Decode,
            format!("{name} (BOM)"),
            with_bom,
            Some(expected.clone()),
        ));
    }

    // api-basics.any.js, "Encode/decode round trip: utf-8": `var bytes`
    // decodes to `var sample`.
    let s = get("api-basics.any.js")?;
    let bytes = s.after_only("var bytes = ")?;
    let sample = string_scalars(&s.after_only("var sample = ")?)?;
    let name = "Encode/decode round trip: utf-8".to_owned();
    cases.push(s.case(bytes.line, Hook::Decode, name, bytes.bytes()?, Some(sample)));

    // api-surrogates-utf8.any.js: `var badStrings = [{input, expected,
    // decoded, name}]`; `expected` (bytes) decodes to `decoded`.
    let s = get("api-surrogates-utf8.any.js")?;
    for row in s.after_only("var badStrings = ")?.array()? {
        let name = format!(
            "Invalid surrogates encoded into UTF-8: {}",
            row.field("name")?.string()?
        );
        let decoded = string_scalars(row.field("decoded")?)?;
        cases.push(s.case(
            row.line,
            Hook::Decode,
            name,
            row.field("expected")?.bytes()?,
            Some(decoded),
        ));
    }

    // textdecoder-ignorebom.any.js: `var cases = [{encoding, bytes}]`. With
    // `ignoreBOM: true` the result is `BOM + 'abc'`; by default, `'abc'`.
    let s = get("textdecoder-ignorebom.any.js")?;
    let mut kept = string_scalars(&s.after_only("var BOM = ")?)?;
    let abc = string_scalars(&s.after_first("BOM + ")?)?;
    kept.extend_from_slice(&abc);
    for row in s.after_only("var cases = ")?.array()? {
        if !is_utf8(row.field("encoding")?)? {
            continue;
        }
        let bytes = row.field("bytes")?.bytes()?;
        let name = "BOM is ignored if ignoreBOM option is specified: utf-8".to_owned();
        cases.push(s.case(
            row.line,
            Hook::DecodeWithoutBom,
            format!("{name} (ignoreBOM)"),
            bytes.clone(),
            Some(kept.clone()),
        ));
        cases.push(s.case(
            row.line,
            Hook::Decode,
            format!("{name} (default)"),
            bytes,
            Some(abc.clone()),
        ));
    }

    // Every file: self-contained one-line assertions
    // `assert_equals(new TextDecoder(<utf-8 or nothing>).decode(<literal
    // bytes>), <string literal>)`. Anything else (variables, options,
    // streaming, other encodings) is left to the rules above.
    for s in &sources {
        for pos in find_all(&s.text, "assert_equals(new TextDecoder(") {
            let mut p = Parser::at(&s.text, pos);
            if let Some(case) = harvest(s, &mut p).map_err(|e| format!("{}: {e}", s.file))? {
                cases.push(case);
            }
        }
    }

    cases.sort();
    render(&cases)
}

/// One `assert_equals(new TextDecoder(...` call, if it is self-contained.
fn harvest(s: &Source, p: &mut Parser) -> Result<Option<Case>, String> {
    let line = p.line();
    if !p.eat(")") {
        // A variable as the label: skip.
        if !(p.next_is('\'') || p.next_is('"')) {
            return Ok(None);
        }
        let label = p.literal()?;
        if !is_utf8(&label)? || !p.eat(")") {
            return Ok(None);
        }
    }
    if !p.eat(".decode(") {
        return Ok(None);
    }
    let input = if p.eat("new Uint8Array(") || p.eat("Uint8Array.from(") {
        if !p.next_is('[') {
            return Ok(None);
        }
        let bytes = p.literal()?.bytes()?;
        p.expect(")")?;
        bytes
    } else if p.eat("Uint8Array.of(") || p.eat("u(") {
        p.list(')', |p| p.literal()?.byte())?
    } else {
        return Ok(None);
    };
    // Options (`{stream: true}`) or a variable as the expectation: skip.
    if !p.eat("),") || !(p.next_is('"') || p.next_is('\'')) {
        return Ok(None);
    }
    let expected = p.literal()?;
    if !p.eat(")") {
        return Ok(None);
    }
    let name = format!("assert_equals at line {line}");
    Ok(Some(s.case(
        line,
        Hook::Decode,
        name,
        input,
        Some(string_scalars(&expected)?),
    )))
}

fn render(cases: &[Case]) -> Result<String, String> {
    let mut out = String::new();
    let w = |out: &mut String, s: String| out.push_str(&s);
    w(
        &mut out,
        "// @generated by `cargo xtask testdata` from tests/data/wpt-encoding/.\n".into(),
    );
    w(
        &mut out,
        "// Do not edit: `cargo xtask verify` fails if this differs from what the\n".into(),
    );
    w(
        &mut out,
        "// converter (xtask/src/testdata/wpt_encoding.rs) produces.\n".into(),
    );
    w(
        &mut out,
        "// Source, commit and license: tests/data/wpt-encoding/SOURCE.md.\n".into(),
    );
    w(&mut out, "const WPT: &[Case] = &[\n".into());
    for c in cases {
        let input: Vec<String> = c.input.iter().map(|b| format!("0x{b:02X}")).collect();
        let expected = match &c.expected {
            None => "None".to_owned(),
            Some(v) => {
                let v: Vec<String> = v.iter().map(|u| format!("0x{u:04X}")).collect();
                format!("Some(&[{}])", v.join(", "))
            }
        };
        writeln!(
            out,
            "    Case {{ file: {:?}, line: {}, name: {:?}, hook: Hook::{:?}, input: &[{}], expected: {expected} }},",
            c.file,
            c.line,
            c.name,
            c.hook,
            input.join(", ")
        )
        .map_err(|e| e.to_string())?;
    }
    out.push_str("];\n");
    Ok(out)
}
