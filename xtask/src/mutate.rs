//! Proof mutation testing (Phase 0 item 0.6).
//!
//! A proof that passes whatever the spec says proves nothing. Each Verus
//! crate may list mutations in `mutations.json`: a small edit to a spec, and
//! whether the proofs are expected to catch it. Every mutation is applied
//! to a copy of the crate in `target/xtask-mutate/`, never to the working
//! tree, so an interrupted run cannot leave a broken spec behind.
//!
//! ```json
//! { "mutations": [ {
//!     "id": "ed-upper-boundary",
//!     "file": "src/utf8/spec.rs",
//!     "find": "if byte == 0xED { 0x9F }",
//!     "replace": "if byte == 0xED { 0xBF }",
//!     "expect": "killed",
//!     "reason": "admits surrogates; lemma_output_scalar_values must fail"
//! } ] }
//! ```
//!
//! `expect` is one of:
//! - `"killed"`: the proofs must fail, *because a proven theorem is false
//!   for the mutant*. This is real coverage.
//! - `"killed-incidentally"`: the proofs must fail, but every theorem still
//!   holds for the mutant; only the proof script (an invariant, a case
//!   split) breaks. Not counted as coverage. The reason says which part.
//! - `"survives"`: a known gap. The reason says what will cover it.
//!
//! The tool checks killed vs. survived. Which kind of kill it is depends on
//! whether the theorem holds for the mutant, which a human reviewing
//! `mutations.json` must judge; the reason states the argument. A mutation
//! whose result does not match `expect` fails the run, so the list can
//! never overstate or understate what is covered.

use std::path::{Path, PathBuf};

use serde_json::Value;

use crate::verus::{self, Run};
use crate::workspace::Crate;

pub const FILE: &str = "mutations.json";

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Expect {
    Killed,
    KilledIncidentally,
    Survives,
}

struct Mutation {
    id: String,
    file: String,
    find: String,
    replace: String,
    expect: Expect,
    reason: String,
}

/// Outcome of mutation testing one crate.
pub struct Report {
    /// One line per mutation.
    pub lines: Vec<String>,
    /// Mutations whose result did not match `expect`, or that are invalid.
    pub problems: Vec<String>,
    /// Killed because a theorem is false for the mutant.
    pub killed: usize,
    /// Killed, but only by the proof script.
    pub incidental: usize,
    pub survived: usize,
    pub total: usize,
}

/// The crate has a mutations file.
pub fn has_mutations(c: &Crate) -> bool {
    c.dir.join(FILE).is_file()
}

/// For the tier check: (mutations not expected to be `killed`, total), or
/// `None` if the crate has no mutations file.
pub fn gaps(c: &Crate) -> Result<Option<(usize, usize)>, String> {
    if !has_mutations(c) {
        return Ok(None);
    }
    let all = load(c)?;
    let gaps = all.iter().filter(|m| m.expect != Expect::Killed).count();
    Ok(Some((gaps, all.len())))
}

fn load(c: &Crate) -> Result<Vec<Mutation>, String> {
    let path = c.dir.join(FILE);
    let text = std::fs::read_to_string(&path).map_err(|e| format!("{}: {e}", path.display()))?;
    let json: Value =
        serde_json::from_str(&text).map_err(|e| format!("{}: {e}", path.display()))?;
    let list = json
        .get("mutations")
        .and_then(Value::as_array)
        .ok_or_else(|| format!("{}: expected {{\"mutations\": [...]}}", path.display()))?;
    list.iter()
        .map(|m| {
            let field = |k: &str| {
                m.get(k)
                    .and_then(Value::as_str)
                    .map(str::to_owned)
                    .ok_or_else(|| {
                        format!("{}: mutation missing string field {k:?}", path.display())
                    })
            };
            let id = field("id")?;
            let expect = match field("expect")?.as_str() {
                "killed" => Expect::Killed,
                "killed-incidentally" => Expect::KilledIncidentally,
                "survives" => Expect::Survives,
                other => {
                    return Err(format!(
                        "{}: {id}: expect must be \"killed\", \"killed-incidentally\" or \"survives\", not {other:?}",
                        path.display()
                    ));
                }
            };
            Ok(Mutation {
                file: field("file")?,
                find: field("find")?,
                replace: field("replace")?,
                reason: field("reason")?,
                expect,
                id,
            })
        })
        .collect()
}

/// Run every mutation for one crate.
pub fn run(c: &Crate, root: &Path) -> Result<Report, String> {
    let mutations = load(c)?;
    let sandbox = make_sandbox(c, root)?;
    let crate_dir = sandbox.join("crates").join(&c.name);
    let mut report = Report {
        lines: Vec::new(),
        problems: Vec::new(),
        killed: 0,
        incidental: 0,
        survived: 0,
        total: 0,
    };

    // Baseline: the unmutated copy must verify, or every mutation would
    // look "killed" for the wrong reason.
    match verus::run(&crate_dir, &c.name, false)? {
        Run::Verified(s) => report.lines.push(format!("baseline   {s}")),
        Run::ProofFailed(s, _) => return Err(format!("unmutated copy does not verify: {s}")),
        Run::BuildFailed(out) => return Err(format!("unmutated copy does not build:\n{out}")),
    }

    for m in &mutations {
        report.total = report.total.saturating_add(1);
        let target = crate_dir.join(&m.file);
        let original =
            std::fs::read_to_string(&target).map_err(|e| format!("{}: {e}", target.display()))?;
        let hits = original.matches(&m.find).count();
        if hits != 1 {
            report.problems.push(format!(
                "{}: `find` occurs {hits} times in {} (must be exactly once; the mutation is stale)",
                m.id, m.file
            ));
            continue;
        }
        let mutated = original.replacen(&m.find, &m.replace, 1);
        std::fs::write(&target, mutated).map_err(|e| format!("{}: {e}", target.display()))?;
        let result = verus::run(&crate_dir, &c.name, false);
        std::fs::write(&target, &original).map_err(|e| format!("{}: {e}", target.display()))?;
        match (result?, m.expect) {
            (Run::ProofFailed(_, out), Expect::Killed) => {
                report.killed = report.killed.saturating_add(1);
                report.lines.push(format!(
                    "killed     {}  (first failure: {})",
                    m.id,
                    first_failure(&out)
                ));
            }
            (Run::ProofFailed(_, out), Expect::KilledIncidentally) => {
                report.incidental = report.incidental.saturating_add(1);
                report.lines.push(format!(
                    "incidental {}  (first failure: {}; {})",
                    m.id,
                    first_failure(&out),
                    m.reason
                ));
            }
            (Run::ProofFailed(s, out), Expect::Survives) => {
                report.problems.push(format!(
                    "{}: expected to survive but was killed ({s}; first failure: {}); \
                     find out why before changing expect",
                    m.id,
                    first_failure(&out)
                ));
            }
            (Run::Verified(_), Expect::Survives) => {
                report.survived = report.survived.saturating_add(1);
                report
                    .lines
                    .push(format!("survives   {}  (known gap: {})", m.id, m.reason));
            }
            (Run::Verified(_), Expect::Killed | Expect::KilledIncidentally) => {
                report.problems.push(format!(
                    "{}: SURVIVED, but must be killed: {}",
                    m.id, m.reason
                ));
            }
            (Run::BuildFailed(out), _) => {
                report.problems.push(format!(
                    "{}: mutated crate does not build, so it tests nothing:\n{out}",
                    m.id
                ));
            }
        }
    }
    Ok(report)
}

/// The first error message and its location in Verus output, e.g.
/// "postcondition not satisfied at src/utf8/lemmas.rs:182:1".
fn first_failure(out: &str) -> String {
    let mut lines = out.lines();
    while let Some(l) = lines.next() {
        if let Some(msg) = l.strip_prefix("error: ") {
            let loc = lines
                .find_map(|l| l.trim_start().strip_prefix("--> "))
                .map(|loc| loc.rsplit_once("crates/").map_or(loc, |(_, rest)| rest))
                .and_then(|loc| loc.split_once('/').map(|(_, path)| path))
                .unwrap_or("unknown location");
            return format!("{msg} at {loc}");
        }
    }
    "no error message found".into()
}

/// A one-crate copy of the workspace under `target/xtask-mutate/<crate>/`.
/// Its own target directory keeps dependency builds warm between runs.
fn make_sandbox(c: &Crate, root: &Path) -> Result<PathBuf, String> {
    let sandbox = root.join("target").join("xtask-mutate").join(&c.name);
    let crate_copy = sandbox.join("crates").join(&c.name);
    if crate_copy.exists() {
        std::fs::remove_dir_all(&crate_copy)
            .map_err(|e| format!("{}: {e}", crate_copy.display()))?;
    }
    copy_dir(&c.dir, &crate_copy)?;
    for f in ["Cargo.lock", "rust-toolchain.toml"] {
        std::fs::copy(root.join(f), sandbox.join(f)).map_err(|e| format!("copy {f}: {e}"))?;
    }
    // The workspace manifest, with only this crate as a member.
    let manifest =
        std::fs::read_to_string(root.join("Cargo.toml")).map_err(|e| format!("Cargo.toml: {e}"))?;
    let members = format!("members = [\"crates/{}\"]", c.name);
    let mut replaced = false;
    let rewritten: Vec<String> = manifest
        .lines()
        .map(|l| {
            if l.trim_start().starts_with("members =") {
                replaced = true;
                members.clone()
            } else {
                l.to_owned()
            }
        })
        .collect();
    if !replaced {
        return Err("Cargo.toml: no `members = [...]` line to rewrite".into());
    }
    std::fs::write(sandbox.join("Cargo.toml"), rewritten.join("\n"))
        .map_err(|e| format!("sandbox Cargo.toml: {e}"))?;
    Ok(sandbox)
}

fn copy_dir(from: &Path, to: &Path) -> Result<(), String> {
    std::fs::create_dir_all(to).map_err(|e| format!("{}: {e}", to.display()))?;
    let entries = std::fs::read_dir(from).map_err(|e| format!("{}: {e}", from.display()))?;
    for entry in entries {
        let entry = entry.map_err(|e| format!("{}: {e}", from.display()))?;
        let path = entry.path();
        if path.file_name().is_some_and(|n| n == "target") {
            continue;
        }
        let dest = to.join(entry.file_name());
        if path.is_dir() {
            copy_dir(&path, &dest)?;
        } else {
            std::fs::copy(&path, &dest).map_err(|e| format!("{}: {e}", path.display()))?;
        }
    }
    Ok(())
}
