//! The Public Suffix List tables for `clazel-psl` (Phase 2 item 2.4).
//!
//! `public_suffix_list.dat` and the list's own `tests/tests.txt` are
//! vendored, byte for byte, under `crates/clazel-psl/data/publicsuffix-<commit>/`
//! with a `SOURCE.md` giving the upstream commit, URLs and SHA-256 of each.
//! This module turns the list into `crates/clazel-psl/src/data.rs`, a Rust
//! file of constant arrays that is committed (the chunked opaque tables of
//! `unicode.rs`). `cargo xtask tables` writes it; `check` and `verify` fail
//! if a vendored file's hash differs from `SOURCE.md` or the committed file
//! differs from what this produces.
//!
//! The proofs are relative to these tables, so what this module derives is
//! part of the trusted base and is kept to simple, stated steps (each is
//! listed in the generated file's header):
//! - a line is read up to its first whitespace; a line that is empty or
//!   starts with `//` holds no rule (publicsuffix.org "Format");
//! - a rule that starts with `!` is an exception rule, and its text is
//!   what follows the `!`;
//! - each label of the text that is not ASCII is converted to its A-label
//!   (`xn--` and RFC 3492 Punycode); ASCII labels are used as they are
//!   (the list is already lower case, which is checked);
//! - rules keep the order they have in the file, which is the order of
//!   `PSL_RULES`; no sorting.
//!
//! It also rejects, so the tables can rely on it: an empty label; a `*`
//! anywhere but as the whole leftmost label of a non-exception rule; an
//! upper-case ASCII letter; a duplicate rule; and two exception rules one
//! of which is a label suffix of the other (so that no domain has two
//! matching exception rules, where the standard does not say which
//! prevails).

use std::fmt::Write as _;
use std::path::{Path, PathBuf};

use crate::reviews;
use crate::unicode::{Table, emit};
use crate::workspace;

/// The vendored data directory, relative to the repository root.
const DATA_DIR: &str = "crates/clazel-psl/data/publicsuffix-5dd321ff";
/// The generated file, relative to the repository root.
const OUTPUT: &str = "crates/clazel-psl/src/data.rs";
/// The files `SOURCE.md` must list, besides itself and LICENSE.
const FILES: &[&str] = &["public_suffix_list.dat", "tests.txt"];

/// Compare (or, with `write`, rewrite) the generated tables. Returns
/// (problems, notes).
pub fn run(write: bool) -> (Vec<String>, Vec<String>) {
    let dir = PathBuf::from(DATA_DIR);
    let mut problems = check_sources(&dir);
    let mut notes = Vec::new();
    if !problems.is_empty() {
        return (problems, notes);
    }
    let fresh = match std::fs::read_to_string(dir.join("public_suffix_list.dat"))
        .map_err(|e| e.to_string())
        .and_then(|t| generate(&t))
    {
        Ok(f) => f,
        Err(e) => return (vec![format!("{DATA_DIR}: {e}")], notes),
    };
    let current = std::fs::read_to_string(OUTPUT).ok();
    if current.as_deref() == Some(fresh.as_str()) {
        notes.push(format!("{OUTPUT}: up to date"));
    } else if write {
        match std::fs::write(OUTPUT, &fresh) {
            Ok(()) => notes.push(format!("{OUTPUT}: written")),
            Err(e) => problems.push(format!("{OUTPUT}: {e}")),
        }
    } else if current.is_none() {
        problems.push(format!("{OUTPUT}: missing; run `cargo xtask tables`"));
    } else {
        problems.push(format!(
            "{OUTPUT}: stale (differs from what xtask/src/psl.rs produces); \
             run `cargo xtask tables` and commit the result"
        ));
    }
    (problems, notes)
}

/// Every vendored file is listed in `SOURCE.md` with its SHA-256, and
/// matches it; nothing else is in the directory.
fn check_sources(dir: &Path) -> Vec<String> {
    let rel = workspace::relative(dir);
    let source = match std::fs::read_to_string(dir.join("SOURCE.md")) {
        Ok(s) => s,
        Err(e) => return vec![format!("{rel}/SOURCE.md: {e}")],
    };
    let mut problems = Vec::new();
    for file in FILES {
        let listed = source.lines().find_map(|l| {
            let rest = l.trim().strip_prefix("SHA-256:")?.trim();
            let (hash, name) = rest.split_once(char::is_whitespace)?;
            (name.trim().trim_matches('`') == *file).then(|| hash.to_ascii_lowercase())
        });
        let Some(listed) = listed else {
            problems.push(format!(
                "{rel}/SOURCE.md: no \"SHA-256: <hash> {file}\" line"
            ));
            continue;
        };
        match reviews::sha256(&dir.join(file)) {
            Ok(actual) if actual == listed => {}
            Ok(actual) => problems.push(format!(
                "{rel}/{file}: SHA-256 {actual} differs from SOURCE.md ({listed})"
            )),
            Err(e) => problems.push(e),
        }
    }
    if !source.lines().any(|l| l.trim().starts_with("License:")) {
        problems.push(format!("{rel}/SOURCE.md: no \"License:\" line"));
    }
    if !source.lines().any(|l| l.trim().starts_with("Commit:")) {
        problems.push(format!("{rel}/SOURCE.md: no \"Commit:\" line"));
    }
    match std::fs::read_dir(dir) {
        Ok(entries) => {
            for entry in entries.flatten() {
                let name = entry.file_name().to_string_lossy().into_owned();
                if !FILES.contains(&name.as_str()) && name != "SOURCE.md" && name != "LICENSE" {
                    problems.push(format!(
                        "{rel}/{name}: not an input of xtask/src/psl.rs"
                    ));
                }
            }
        }
        Err(e) => problems.push(format!("{rel}: {e}")),
    }
    problems
}

/// RFC 3492 section 6.3, "Encoding procedure", for `input` (code points).
fn punycode_encode(input: &[u32]) -> Option<String> {
    const BASE: u32 = 36;
    const T_MIN: u32 = 1;
    const T_MAX: u32 = 26;
    const SKEW: u32 = 38;
    const DAMP: u32 = 700;
    fn digit(d: u32) -> Option<char> {
        match d {
            0..=25 => char::from_u32(d.checked_add(u32::from(b'a'))?),
            26..=35 => char::from_u32(d.checked_sub(26)?.checked_add(u32::from(b'0'))?),
            _ => None,
        }
    }
    fn adapt(delta: u32, num_points: u32, first: bool) -> Option<u32> {
        let mut delta = if first { delta.checked_div(DAMP)? } else { delta.checked_div(2)? };
        delta = delta.checked_add(delta.checked_div(num_points)?)?;
        let mut k = 0u32;
        while delta > BASE.saturating_sub(T_MIN).checked_mul(T_MAX)?.checked_div(2)? {
            delta = delta.checked_div(BASE.saturating_sub(T_MIN))?;
            k = k.checked_add(BASE)?;
        }
        k.checked_add(BASE.saturating_sub(T_MIN).saturating_add(1).checked_mul(delta)?.checked_div(delta.checked_add(SKEW)?)?)
    }
    let mut out = String::new();
    for &c in input {
        if c < 0x80 {
            out.push(char::from_u32(c)?);
        }
    }
    let b = u32::try_from(out.len()).ok()?;
    let mut h = b;
    if b > 0 {
        out.push('-');
    }
    let mut n = 128u32;
    let mut delta = 0u32;
    let mut bias = 72u32;
    let total = u32::try_from(input.len()).ok()?;
    while h < total {
        let m = input.iter().copied().filter(|&c| c >= n).min()?;
        delta = delta.checked_add(m.saturating_sub(n).checked_mul(h.checked_add(1)?)?)?;
        n = m;
        for &c in input {
            if c < n {
                delta = delta.checked_add(1)?;
            }
            if c == n {
                let mut q = delta;
                let mut k = BASE;
                loop {
                    let t = if k <= bias {
                        T_MIN
                    } else if k >= bias.checked_add(T_MAX)? {
                        T_MAX
                    } else {
                        k.saturating_sub(bias)
                    };
                    if q < t {
                        break;
                    }
                    let width = BASE.saturating_sub(t);
                    let rest = q.saturating_sub(t);
                    out.push(digit(t.checked_add(rest.checked_rem(width)?)?)?);
                    q = rest.checked_div(width)?;
                    k = k.checked_add(BASE)?;
                }
                out.push(digit(q)?);
                bias = adapt(delta, h.checked_add(1)?, h == b)?;
                delta = 0;
                h = h.checked_add(1)?;
            }
        }
        delta = delta.checked_add(1)?;
        n = n.checked_add(1)?;
    }
    Some(out)
}

/// A label as an A-label.
fn to_ascii_label(label: &str) -> Result<String, String> {
    if label.is_ascii() {
        return Ok(label.to_owned());
    }
    let cps: Vec<u32> = label.chars().map(u32::from).collect();
    let p = punycode_encode(&cps).ok_or_else(|| format!("cannot Punycode {label:?}"))?;
    Ok(format!("xn--{p}"))
}

/// One rule of the list.
struct Rule {
    /// The text after any `!`, with every label an A-label.
    text: String,
    exception: bool,
}

/// The rules of the list, in file order, checked as the module docs say.
fn rules(list: &str) -> Result<Vec<Rule>, String> {
    let mut out: Vec<Rule> = Vec::new();
    for (i, line) in list.lines().enumerate() {
        let at = i.saturating_add(1);
        let Some(first) = line.split_whitespace().next() else {
            continue;
        };
        if first.starts_with("//") {
            continue;
        }
        let (exception, body) = match first.strip_prefix('!') {
            Some(rest) => (true, rest),
            None => (false, first),
        };
        let mut labels = Vec::new();
        for (j, label) in body.split('.').enumerate() {
            if label.is_empty() {
                return Err(format!("line {at}: empty label in {first:?}"));
            }
            if label.contains('*') && (label != "*" || j != 0 || exception) {
                return Err(format!(
                    "line {at}: `*` must be the whole leftmost label of a non-exception rule: {first:?}"
                ));
            }
            let a = to_ascii_label(label).map_err(|e| format!("line {at}: {e}"))?;
            if a.bytes().any(|c| c.is_ascii_uppercase() || c == b'!' || c <= b' ') {
                return Err(format!("line {at}: label {a:?} is not lower case"));
            }
            labels.push(a);
        }
        let text = labels.join(".");
        if out.iter().any(|r| r.text == text && r.exception == exception) {
            return Err(format!("line {at}: duplicate rule {first:?}"));
        }
        out.push(Rule { text, exception });
    }
    let exceptions: Vec<&Rule> = out.iter().filter(|r| r.exception).collect();
    for a in &exceptions {
        for b in &exceptions {
            if !std::ptr::eq(*a, *b) && a.text.ends_with(&format!(".{}", b.text)) {
                return Err(format!(
                    "exception rule {:?} is a label suffix of exception rule {:?}",
                    b.text, a.text
                ));
            }
        }
    }
    if out.is_empty() {
        return Err("no rules".into());
    }
    Ok(out)
}

fn generate(list: &str) -> Result<String, String> {
    let rules = rules(list)?;
    let mut chars: Vec<u8> = Vec::new();
    let mut rows = Vec::new();
    for r in &rules {
        let start = chars.len();
        chars.extend_from_slice(r.text.as_bytes());
        rows.push(format!(
            "RuleRow {{ start: {start}, len: {}, exception: {} }}",
            r.text.len(),
            r.exception
        ));
    }
    let mut out = String::new();
    out.push_str(HEADER);
    emit(
        &mut out,
        &Table {
            name: "psl_rules",
            doc: "public_suffix_list.dat, one row per rule, in file order.",
            row_type: "RuleRow",
            row_bytes: 12,
            rows,
        },
    );
    emit(
        &mut out,
        &Table {
            name: "psl_chars",
            doc: "The rules' text, concatenated (ASCII).",
            row_type: "u8",
            row_bytes: 1,
            rows: chars.iter().map(|c| format!("0x{c:X}")).collect(),
        },
    );
    let _ = writeln!(out, "}} // verus!");
    Ok(out)
}

const HEADER: &str = "\
//! The Public Suffix List's rules.
//!
// @generated by `cargo xtask tables` (xtask/src/psl.rs) from
// crates/clazel-psl/data/publicsuffix-5dd321ff/ (the publicsuffix/list commit
// and SHA-256 of each file are in SOURCE.md there). Do not edit: `cargo xtask
// check` fails if this differs from what the generator produces.
//
// What the generator derives (the proofs are relative to these tables):
// - PSL_RULES has one row per rule of public_suffix_list.dat, in file order.
//   A line is read up to its first whitespace; a line that is empty or starts
//   with `//` has no rule. A row's `exception` is whether the rule started
//   with `!`; the rule's text is PSL_CHARS[start .. start + len], the rest of
//   the rule after any `!`, with each non-ASCII label replaced by its A-label
//   (`xn--` and RFC 3492 Punycode).
// - Checked when generating: no empty label; `*` only as the whole leftmost
//   label of a non-exception rule; no upper-case ASCII letter; no duplicate
//   rule; no exception rule is a label suffix of another exception rule.

use super::tables::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

";
