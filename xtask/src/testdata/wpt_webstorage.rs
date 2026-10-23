//! WPT `webstorage/`: the `*.window.js` tests whose body is a sequence of
//! `localStorage` calls and assertions, as a table of cases of operations.
//!
//! Each vendored file runs `["localStorage", "sessionStorage"].forEach(
//! function(name) { test(function() { ... }, "..."); ... });`. The kernel
//! has `localStorage` only (item 2.10: there is no `sessionStorage` message),
//! so only the `localStorage` instance of each test is converted. The
//! converter reads a test body with the grammar below and **skips** a test
//! whose body uses anything else (a loop, a closure, an object argument, a
//! thrown exception, a lone surrogate, a computed key), saying why; the
//! skipped tests are listed in the generated file and in `SOURCE.md`.
//!
//! Supported statements, where `A` is a string literal, `null`,
//! `undefined` or a number (converted as WebIDL's DOMString conversion
//! does: `null` is `"null"`, `undefined` is `"undefined"`):
//!
//! - `var s = window[name];`
//! - `s.clear();`, `s.setItem(A, A);`, `s.removeItem(A);`
//! - `s[A] = A;` and `s.ident = A;` (the named setter is `setItem`)
//! - `delete s[A];` (the named deleter is `removeItem`)
//! - `assert_equals(E, V[, message]);` with `E` one of `s.getItem(A)`,
//!   `s[A]`, `s.ident` and `s.length`, and `V` a string literal,
//!   `null`, `undefined` or a number (the named getter returns `undefined`
//!   where `getItem` returns `null`; both are "no such key")
//! - `assert_true(A in s[, message]);` and `assert_false(A in s[, message]);`
//!   (`A in s` is whether the key exists, for names that are not built-ins)
//! - a nested `test(function() { ... }, "name");`, which becomes a case of
//!   its own that runs the parent's statements before it, then its own.
//!
//! Strings are JavaScript (UTF-16); a key or value goes over the wire as its
//! UTF-8, which a lone surrogate has none.

use std::fmt::Write as _;
use std::path::Path;

/// The vendored files the converter reads.
pub const FILES: &[&str] = &[
    "storage_clear.window.js",
    "storage_getitem.window.js",
    "storage_key_empty_string.window.js",
    "storage_length.window.js",
    "storage_removeitem.window.js",
    "storage_setitem.window.js",
];

#[derive(Debug, Clone, PartialEq, Eq)]
enum Tok {
    Id(String),
    Str(Vec<u16>),
    Num(u64),
    P(char),
}

fn tokenize(src: &str) -> Result<Vec<Tok>, String> {
    let chars: Vec<char> = src.chars().collect();
    let mut toks = Vec::new();
    let mut i = 0usize;
    while let Some(&c) = chars.get(i) {
        if c.is_whitespace() {
            i = i.saturating_add(1);
        } else if c == '/' && chars.get(i.saturating_add(1)) == Some(&'/') {
            while chars.get(i).is_some_and(|c| *c != '\n') {
                i = i.saturating_add(1);
            }
        } else if c == '/' && chars.get(i.saturating_add(1)) == Some(&'*') {
            i = i.saturating_add(2);
            while chars.get(i).is_some()
                && !(chars.get(i) == Some(&'*') && chars.get(i.saturating_add(1)) == Some(&'/'))
            {
                i = i.saturating_add(1);
            }
            i = i.saturating_add(2);
        } else if c == '"' || c == '\'' {
            i = i.saturating_add(1);
            let mut units: Vec<u16> = Vec::new();
            loop {
                let Some(&d) = chars.get(i) else {
                    return Err("unterminated string".to_owned());
                };
                i = i.saturating_add(1);
                if d == c {
                    break;
                }
                if d != '\\' {
                    let mut buf = [0u16; 2];
                    units.extend_from_slice(d.encode_utf16(&mut buf));
                    continue;
                }
                let Some(&e) = chars.get(i) else {
                    return Err("unterminated escape".to_owned());
                };
                i = i.saturating_add(1);
                let unit: u32 = match e {
                    '0' => 0,
                    'n' => 0x0A,
                    'r' => 0x0D,
                    't' => 0x09,
                    '\\' | '\'' | '"' => u32::from(e),
                    'x' | 'u' => {
                        let n = if e == 'x' { 2 } else { 4 };
                        let hex: String = chars.iter().skip(i).take(n).collect();
                        i = i.saturating_add(n);
                        u32::from_str_radix(&hex, 16)
                            .map_err(|e| format!("bad escape {hex:?}: {e}"))?
                    }
                    _ => return Err(format!("unsupported escape \\{e}")),
                };
                units.push(u16::try_from(unit).map_err(|e| e.to_string())?);
            }
            toks.push(Tok::Str(units));
        } else if c.is_ascii_digit() {
            let start = i;
            while chars.get(i).is_some_and(|c| c.is_ascii_alphanumeric()) {
                i = i.saturating_add(1);
            }
            let text: String = chars
                .iter()
                .skip(start)
                .take(i.saturating_sub(start))
                .collect();
            let n = match text.strip_prefix("0x") {
                Some(h) => u64::from_str_radix(h, 16),
                None => text.parse::<u64>(),
            }
            .map_err(|e| format!("bad number {text:?}: {e}"))?;
            toks.push(Tok::Num(n));
        } else if c.is_ascii_alphabetic() || c == '_' || c == '$' {
            let start = i;
            while chars
                .get(i)
                .is_some_and(|c| c.is_ascii_alphanumeric() || *c == '_' || *c == '$')
            {
                i = i.saturating_add(1);
            }
            toks.push(Tok::Id(
                chars
                    .iter()
                    .skip(start)
                    .take(i.saturating_sub(start))
                    .collect(),
            ));
        } else {
            toks.push(Tok::P(c));
            i = i.saturating_add(1);
        }
    }
    Ok(toks)
}

/// One operation of a case.
#[derive(Debug, Clone)]
enum Op {
    Clear,
    Set(Vec<u8>, Vec<u8>),
    Remove(Vec<u8>),
    /// `getItem(key)` is the value, or `None` for "no such key".
    Get(Vec<u8>, Option<Vec<u8>>),
    /// The key exists, or not.
    Has(Vec<u8>, bool),
    Length(u64),
}

struct Case {
    file: String,
    name: String,
    ops: Vec<Op>,
}

struct Reader {
    toks: Vec<Tok>,
    i: usize,
}

type Res<T> = Result<T, String>;

impl Reader {
    fn peek(&self) -> Option<&Tok> {
        self.toks.get(self.i)
    }

    fn bump(&mut self) -> Option<Tok> {
        let t = self.toks.get(self.i).cloned();
        self.i = self.i.saturating_add(1);
        t
    }

    fn eat_p(&mut self, c: char) -> bool {
        if self.peek() == Some(&Tok::P(c)) {
            self.i = self.i.saturating_add(1);
            true
        } else {
            false
        }
    }

    fn expect_p(&mut self, c: char) -> Res<()> {
        if self.eat_p(c) {
            Ok(())
        } else {
            Err(format!("expected {c:?}, found {:?}", self.peek()))
        }
    }

    fn eat_id(&mut self, id: &str) -> bool {
        if matches!(self.peek(), Some(Tok::Id(x)) if x == id) {
            self.i = self.i.saturating_add(1);
            true
        } else {
            false
        }
    }

    fn expect_id(&mut self, id: &str) -> Res<()> {
        if self.eat_id(id) {
            Ok(())
        } else {
            Err(format!("expected {id:?}, found {:?}", self.peek()))
        }
    }

    fn ident(&mut self) -> Res<String> {
        match self.bump() {
            Some(Tok::Id(x)) => Ok(x),
            other => Err(format!("expected an identifier, found {other:?}")),
        }
    }

    /// Skip tokens up to and including the `)` that closes the group opened
    /// just before `self.i` (depth 1), counting `(`, `[` and `{`.
    fn skip_group(&mut self) {
        let mut depth = 1usize;
        while let Some(t) = self.bump() {
            match t {
                Tok::P('(' | '[' | '{') => depth = depth.saturating_add(1),
                Tok::P(')' | ']' | '}') => {
                    depth = depth.saturating_sub(1);
                    if depth == 0 {
                        return;
                    }
                }
                _ => {}
            }
        }
    }

    /// Skip a statement from `self.i` to its `;` (or past a closing group).
    fn skip_statement(&mut self) {
        while let Some(t) = self.bump() {
            match t {
                Tok::P('(' | '[') => self.skip_group(),
                Tok::P('{') => {
                    // A block (a loop's body, or an object literal) ends
                    // the statement; a `;` after it is an empty statement.
                    self.skip_group();
                    return;
                }
                Tok::P(';') => return,
                _ => {}
            }
        }
    }

    /// A DOMString argument: a string, `null`, `undefined` or a number.
    fn arg(&mut self) -> Res<Vec<u8>> {
        match self.bump() {
            Some(Tok::Str(units)) => String::from_utf16(&units)
                .map(String::into_bytes)
                .map_err(|_| "a string with a lone surrogate has no UTF-8".to_owned()),
            Some(Tok::Id(x)) if x == "null" || x == "undefined" => Ok(x.into_bytes()),
            Some(Tok::Num(n)) => Ok(n.to_string().into_bytes()),
            other => Err(format!("unsupported argument {other:?}")),
        }
    }

    /// The expected value of an assertion: a string, `null` or `undefined`
    /// (no such key), or a number.
    fn expected(&mut self) -> Res<Expect> {
        match self.bump() {
            Some(Tok::Str(units)) => String::from_utf16(&units)
                .map(|s| Expect::Str(s.into_bytes()))
                .map_err(|_| "a string with a lone surrogate has no UTF-8".to_owned()),
            Some(Tok::Id(x)) if x == "null" || x == "undefined" => Ok(Expect::Missing),
            Some(Tok::Num(n)) => Ok(Expect::Num(n)),
            other => Err(format!("unsupported expected value {other:?}")),
        }
    }

    /// The tail of an `assert_*` call: an optional message string, then `)` and `;`.
    fn assertion_end(&mut self) -> Res<()> {
        if self.eat_p(',') {
            match self.bump() {
                Some(Tok::Str(_)) => {}
                other => return Err(format!("unsupported assertion message {other:?}")),
            }
        }
        self.expect_p(')')?;
        // A statement may end without a `;` (automatic semicolon insertion).
        self.eat_p(';');
        Ok(())
    }

    /// `test(function() { ... }, name);` with `test` already read: reads up
    /// to and including the `;`, pushing the cases it holds (nested tests
    /// first, as they run in the body).
    fn test_call(
        &mut self,
        file: &str,
        prefix: &[Op],
        inherited: &Option<String>,
        out: &mut Vec<Case>,
    ) -> Res<()> {
        self.expect_p('(')?;
        self.expect_id("function")?;
        self.expect_p('(')?;
        self.expect_p(')')?;
        self.expect_p('{')?;
        let mut ops: Vec<Op> = prefix.to_vec();
        let mut nested: Vec<Case> = Vec::new();
        let mut own_checks = false;
        let mut storage: Option<String> = inherited.clone();
        loop {
            if self.eat_p('}') {
                break;
            }
            let Some(Tok::Id(head)) = self.peek().cloned() else {
                return Err(format!("unsupported statement start {:?}", self.peek()));
            };
            self.i = self.i.saturating_add(1);
            match head.as_str() {
                "var" => {
                    let v = self.ident()?;
                    self.expect_p('=')?;
                    self.expect_id("window")?;
                    self.expect_p('[')?;
                    self.expect_id("name")?;
                    self.expect_p(']')?;
                    self.eat_p(';');
                    storage = Some(v);
                }
                "test" => {
                    self.test_call(file, &ops, &storage, &mut nested)?;
                }
                "delete" => {
                    self.storage(&storage)?;
                    self.expect_p('[')?;
                    let key = self.arg()?;
                    self.expect_p(']')?;
                    self.eat_p(';');
                    ops.push(Op::Remove(key));
                }
                "assert_true" | "assert_false" => {
                    self.expect_p('(')?;
                    let key = self.arg()?;
                    self.expect_id("in")?;
                    self.storage(&storage)?;
                    self.assertion_end()?;
                    ops.push(Op::Has(key, head == "assert_true"));
                    own_checks = true;
                }
                "assert_equals" => {
                    self.expect_p('(')?;
                    self.storage(&storage)?;
                    let op = self.assert_equals_rest()?;
                    ops.push(op);
                    own_checks = true;
                }
                v if storage.as_deref() == Some(v) => {
                    self.statement_on_storage(&mut ops)?;
                }
                other => return Err(format!("unsupported statement {other:?}")),
            }
        }
        self.expect_p(',')?;
        let name = self.name_expr()?;
        self.expect_p(')')?;
        self.eat_p(';');
        if nested.is_empty() || own_checks {
            out.push(Case {
                file: file.to_owned(),
                name,
                ops,
            });
        }
        out.extend(nested);
        Ok(())
    }

    /// The storage variable.
    fn storage(&mut self, storage: &Option<String>) -> Res<()> {
        let v = self.ident()?;
        if storage.as_deref() == Some(v.as_str()) {
            Ok(())
        } else {
            Err(format!("{v:?} is not the storage"))
        }
    }

    /// A statement `s.clear();`, `s.setItem(a, b);`, `s.removeItem(a);`,
    /// `s[a] = b;` or `s.ident = b;`, with `s` read.
    fn statement_on_storage(&mut self, ops: &mut Vec<Op>) -> Res<()> {
        if self.eat_p('.') {
            let m = self.ident()?;
            if self.eat_p('(') {
                match m.as_str() {
                    "clear" => {
                        self.expect_p(')')?;
                        ops.push(Op::Clear);
                    }
                    "setItem" => {
                        let k = self.arg()?;
                        self.expect_p(',')?;
                        let v = self.arg()?;
                        self.expect_p(')')?;
                        ops.push(Op::Set(k, v));
                    }
                    "removeItem" => {
                        let k = self.arg()?;
                        self.expect_p(')')?;
                        ops.push(Op::Remove(k));
                    }
                    other => return Err(format!("unsupported method {other:?}")),
                }
            } else {
                self.expect_p('=')?;
                let v = self.arg()?;
                ops.push(Op::Set(m.into_bytes(), v));
            }
        } else {
            self.expect_p('[')?;
            let k = self.arg()?;
            self.expect_p(']')?;
            self.expect_p('=')?;
            let v = self.arg()?;
            ops.push(Op::Set(k, v));
        }
        self.eat_p(';');
        Ok(())
    }

    /// After `assert_equals(s`: the rest of the call.
    fn assert_equals_rest(&mut self) -> Res<Op> {
        enum Read {
            Get(Vec<u8>),
            Length,
        }
        let read = if self.eat_p('.') {
            let m = self.ident()?;
            match m.as_str() {
                "getItem" => {
                    self.expect_p('(')?;
                    let k = self.arg()?;
                    self.expect_p(')')?;
                    Read::Get(k)
                }
                "length" => Read::Length,
                other => Read::Get(other.as_bytes().to_vec()),
            }
        } else {
            self.expect_p('[')?;
            let k = self.arg()?;
            self.expect_p(']')?;
            Read::Get(k)
        };
        self.expect_p(',')?;
        let expect = self.expected()?;
        self.assertion_end()?;
        match (read, expect) {
            (Read::Get(k), Expect::Str(v)) => Ok(Op::Get(k, Some(v))),
            (Read::Get(k), Expect::Missing) => Ok(Op::Get(k, None)),
            (Read::Length, Expect::Num(n)) => Ok(Op::Length(n)),
            _ => Err("unsupported assertion".to_owned()),
        }
    }

    /// A test name: string literals and `name` joined by `+`.
    fn name_expr(&mut self) -> Res<String> {
        let mut out = String::new();
        loop {
            match self.bump() {
                Some(Tok::Str(units)) => out.push_str(
                    &String::from_utf16(&units)
                        .map_err(|_| "lone surrogate in a test name".to_owned())?,
                ),
                Some(Tok::Id(x)) if x == "name" => out.push_str("localStorage"),
                other => return Err(format!("unsupported test name {other:?}")),
            }
            if !self.eat_p('+') {
                return Ok(out);
            }
        }
    }
}

enum Expect {
    Str(Vec<u8>),
    Missing,
    Num(u64),
}

/// The cases of one file, and the tests skipped with the reason.
fn convert_file(file: &str, src: &str) -> Res<(Vec<Case>, Vec<String>)> {
    let mut r = Reader {
        toks: tokenize(src)?,
        i: 0,
    };
    // ["localStorage", "sessionStorage"].forEach(function(name) {
    r.expect_p('[')?;
    for want in ["localStorage", "sessionStorage"] {
        match r.bump() {
            Some(Tok::Str(u)) if String::from_utf16_lossy(&u) == want => {}
            other => return Err(format!("{file}: expected {want:?}, found {other:?}")),
        }
        r.eat_p(',');
    }
    r.expect_p(']')?;
    r.expect_p('.')?;
    r.expect_id("forEach")?;
    r.expect_p('(')?;
    r.expect_id("function")?;
    r.expect_p('(')?;
    r.expect_id("name")?;
    r.expect_p(')')?;
    r.expect_p('{')?;
    let mut cases = Vec::new();
    let mut skipped = Vec::new();
    loop {
        if r.eat_p('}') {
            break;
        }
        let start = r.i;
        if r.eat_id("test") {
            let mut got = Vec::new();
            match r.test_call(file, &[], &None, &mut got) {
                Ok(()) => cases.extend(got),
                Err(why) => {
                    // Skip the whole call and name it.
                    r.i = start.saturating_add(1);
                    r.expect_p('(')?;
                    r.skip_group();
                    r.eat_p(';');
                    let name = skipped_name(&r.toks, start, r.i);
                    skipped.push(format!("{file}: {name}: {why}"));
                }
            }
        } else if r.eat_id("for") {
            r.skip_statement();
            skipped.push(format!(
                "{file}: a loop over generated keys and values: not a fixed table"
            ));
        } else {
            r.skip_statement();
        }
        if r.peek().is_none() {
            return Err(format!("{file}: ran past the end of the file"));
        }
    }
    Ok((cases, skipped))
}

/// The name expression of the skipped call in `toks[start..end]`: the
/// tokens after the last top-level comma of the call.
fn skipped_name(toks: &[Tok], start: usize, end: usize) -> String {
    let mut depth = 0usize;
    let mut last_comma: Option<usize> = None;
    let window = toks.get(start..end).unwrap_or(&[]);
    for (k, t) in window.iter().enumerate().skip(1) {
        let k = start.saturating_add(k);
        match t {
            Tok::P('(' | '[' | '{') => depth = depth.saturating_add(1),
            Tok::P(')' | ']' | '}') => depth = depth.saturating_sub(1),
            Tok::P(',') if depth == 1 => last_comma = Some(k),
            _ => {}
        }
    }
    let mut out = String::new();
    let name_from = last_comma.map_or(end, |k| k.saturating_add(1));
    for t in toks.get(name_from..end).unwrap_or(&[]) {
        match t {
            Tok::Str(u) => out.push_str(&String::from_utf16_lossy(u)),
            Tok::Id(x) if x == "name" => out.push_str("localStorage"),
            Tok::P('+') => {}
            Tok::Id(x) => {
                out.push('<');
                out.push_str(x);
                out.push('>');
            }
            _ => break,
        }
    }
    if out.is_empty() {
        "(unnamed)".to_owned()
    } else {
        out
    }
}

fn bytes(b: &[u8]) -> String {
    let items: Vec<String> = b.iter().map(|x| format!("0x{x:02X}")).collect();
    format!("&[{}]", items.join(", "))
}

fn op_source(op: &Op) -> String {
    match op {
        Op::Clear => "Op::Clear".to_owned(),
        Op::Set(k, v) => format!("Op::Set({}, {})", bytes(k), bytes(v)),
        Op::Remove(k) => format!("Op::Remove({})", bytes(k)),
        Op::Get(k, None) => format!("Op::Get({}, None)", bytes(k)),
        Op::Get(k, Some(v)) => format!("Op::Get({}, Some({}))", bytes(k), bytes(v)),
        Op::Has(k, b) => format!("Op::Has({}, {b})", bytes(k)),
        Op::Length(n) => format!("Op::Length({n})"),
    }
}

/// Convert the vendored files in `dir` to the source of
/// `tests/generated/wpt_webstorage.rs`.
pub fn convert(dir: &Path) -> Result<String, String> {
    let mut out = String::from(
        "// @generated by `cargo xtask testdata` from tests/data/wpt-webstorage/.\n\
         // Do not edit: `cargo xtask verify` fails if this differs from what the\n\
         // converter (xtask/src/testdata/wpt_webstorage.rs) produces.\n\
         // Source, commit and license: tests/data/wpt-webstorage/SOURCE.md.\n",
    );
    let mut cases: Vec<Case> = Vec::new();
    let mut skipped: Vec<String> = Vec::new();
    for file in FILES {
        let path = dir.join(file);
        let src = std::fs::read_to_string(&path).map_err(|e| format!("{}: {e}", path.display()))?;
        let (c, s) = convert_file(file, &src)?;
        cases.extend(c);
        skipped.extend(s);
    }
    for s in &skipped {
        let _ = writeln!(out, "// skipped: {s}");
    }
    out.push_str("const WPT_WEBSTORAGE: &[Case] = &[\n");
    let mut index_in_file: Vec<(String, usize)> = Vec::new();
    for c in &cases {
        let slot = match index_in_file.iter().position(|(f, _)| *f == c.file) {
            Some(p) => p,
            None => {
                index_in_file.push((c.file.clone(), 0));
                index_in_file.len().saturating_sub(1)
            }
        };
        let index = index_in_file.get(slot).map_or(0, |(_, n)| *n);
        if let Some((_, n)) = index_in_file.get_mut(slot) {
            *n = n.saturating_add(1);
        }
        let ops: Vec<String> = c.ops.iter().map(op_source).collect();
        let _ = writeln!(
            out,
            "    Case {{ file: {:?}, index: {index}, name: {:?}, ops: &[{}] }},",
            c.file,
            c.name,
            ops.join(", ")
        );
    }
    out.push_str("];\n");
    if cases.is_empty() {
        return Err("no case converted".to_owned());
    }
    Ok(out)
}
