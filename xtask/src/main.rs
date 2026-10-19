//! `cargo xtask`: runs and enforces every check in `docs/VERIFICATION.md`.
//!
//! - `cargo xtask verify`: everything, with fresh proof runs. Exit 0 only if
//!   every check ran and passed; 1 if any failed; 2 if none failed but some
//!   were skipped because a tool is missing (never report that as verified).
//! - `cargo xtask check`: only the fast static checks (no build, no proofs).

mod pins;
mod scan;
mod workspace;

use std::path::Path;
use std::process::{Command, ExitCode};

use pins::Pins;
use workspace::Crate;

enum Outcome {
    Pass(Vec<String>),
    Fail(Vec<String>),
    Skip(String),
}

#[derive(Default)]
struct Runner {
    failed: bool,
    skipped: bool,
}

impl Runner {
    fn step(&mut self, name: &str, outcome: Outcome) {
        println!("==> {name}");
        match outcome {
            Outcome::Pass(details) => {
                print_details(&details);
                println!("    PASS  {name}");
            }
            Outcome::Fail(details) => {
                print_details(&details);
                println!("    FAIL  {name}");
                self.failed = true;
            }
            Outcome::Skip(why) => {
                println!("    SKIP  {name} ({why})");
                self.skipped = true;
            }
        }
    }
}

fn print_details(details: &[String]) {
    for d in details {
        for line in d.lines() {
            println!("    {line}");
        }
    }
}

/// Pass if `problems` is empty, showing `notes` either way.
fn outcome(problems: Vec<String>, notes: Vec<String>) -> Outcome {
    if problems.is_empty() {
        Outcome::Pass(notes)
    } else {
        Outcome::Fail(problems.into_iter().chain(notes).collect())
    }
}

fn from_result(r: Result<Vec<String>, String>) -> Outcome {
    match r {
        Ok(details) => Outcome::Pass(details),
        Err(e) => Outcome::Fail(vec![e]),
    }
}

/// Run a command; Ok(stdout+stderr) on success, Err(stdout+stderr) otherwise.
fn run(cmd: &mut Command) -> Result<String, String> {
    let shown = format!("{cmd:?}");
    let out = cmd
        .output()
        .map_err(|e| format!("cannot run {shown}: {e}"))?;
    let text = format!(
        "{}{}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    );
    if out.status.success() {
        Ok(text)
    } else {
        Err(format!("{shown} failed:\n{text}"))
    }
}

fn on_path(bin: &str) -> bool {
    std::env::var_os("PATH")
        .is_some_and(|paths| std::env::split_paths(&paths).any(|d| d.join(bin).is_file()))
}

fn static_checks(r: &mut Runner, crates: &[Crate], pins: &Pins) {
    // Source scan and tier declarations share one pass over the sources.
    let mut violations = Vec::new();
    let mut decl_problems = Vec::new();
    let mut decl_notes = Vec::new();
    let mut axioms = 0usize;
    for c in crates {
        match workspace::scan_crate(c) {
            Ok(s) => {
                violations.extend(s.violations);
                axioms = axioms.saturating_add(s.axioms);
                let (bad, notes) = workspace::check_tiers(c, s.kani_proofs);
                decl_problems.extend(bad);
                decl_notes.extend(notes);
            }
            Err(e) => violations.push(e),
        }
        match workspace::inherits_workspace_lints(c) {
            Ok(true) => {}
            Ok(false) => {
                decl_problems.push(format!(
                    "{}: missing [lints] workspace = true",
                    workspace::relative(&c.manifest)
                ));
            }
            Err(e) => decl_problems.push(e),
        }
    }
    r.step(
        "no unsafe, lint overrides or proof escape hatches",
        outcome(violations, vec![format!("documented axioms: {axioms}")]),
    );
    r.step(
        "crate tier declarations",
        outcome(decl_problems, decl_notes),
    );
    r.step("pinned versions", from_result(check_pins(crates, pins)));
}

fn check_pins(crates: &[Crate], pins: &Pins) -> Result<Vec<String>, String> {
    let rust = pins.get("RUST_TOOLCHAIN")?;
    let toolchain = std::fs::read_to_string("rust-toolchain.toml")
        .map_err(|e| format!("rust-toolchain.toml: {e}"))?;
    if !toolchain
        .lines()
        .any(|l| l.trim() == format!("channel = \"{rust}\""))
    {
        return Err(format!(
            "rust-toolchain.toml does not pin channel = \"{rust}\""
        ));
    }
    let vstd = format!("={}", pins.get("VSTD_VERSION")?);
    for c in crates.iter().filter(|c| c.verus) {
        let req = c
            .deps
            .iter()
            .find(|(n, _)| n == "vstd")
            .map(|(_, r)| r.as_str());
        if req != Some(vstd.as_str()) {
            return Err(format!(
                "{}: vstd must be pinned to \"{vstd}\", found {req:?}",
                c.name
            ));
        }
    }
    Ok(vec![format!("rust {rust}, vstd {vstd}")])
}

fn build_checks(r: &mut Runner) {
    let cargo =
        |args: &[&str]| from_result(run(Command::new("cargo").args(args)).map(|_| Vec::new()));
    r.step("rustfmt", cargo(&["fmt", "--all", "--", "--check"]));
    r.step(
        "clippy",
        cargo(&[
            "clippy",
            "--workspace",
            "--all-targets",
            "--locked",
            "--",
            "-D",
            "warnings",
        ]),
    );
    r.step(
        "tests",
        cargo(&["test", "--workspace", "--locked", "--quiet"]),
    );
}

fn kani(r: &mut Runner, crates: &[Crate], pins: &Pins) {
    if !on_path("cargo-kani") {
        r.step("kani", Outcome::Skip("cargo-kani not installed".into()));
        return;
    }
    let version = pins.get("KANI_VERSION").map(str::to_owned);
    r.step(
        "kani version",
        from_result(version.and_then(|v| {
            let out = run(Command::new("cargo").args(["kani", "--version"]))?;
            if out.contains(&format!("Kani Rust Verifier {v} ")) {
                Ok(vec![v])
            } else {
                Err(format!("expected Kani {v}, got:\n{out}"))
            }
        })),
    );
    let mut any = false;
    for c in crates {
        let proofs = workspace::scan_crate(c).map(|s| s.kani_proofs).unwrap_or(0);
        if proofs == 0 {
            continue;
        }
        any = true;
        let res =
            run(Command::new("cargo").args(["kani", "--locked", "-p", &c.name])).and_then(|out| {
                let summary = out
                    .lines()
                    .filter(|l| l.starts_with("Complete -"))
                    .collect::<Vec<_>>()
                    .join("\n");
                if summary.contains(" 0 failures") {
                    Ok(vec![summary])
                } else {
                    Err(format!("unexpected Kani summary:\n{out}"))
                }
            });
        r.step(&format!("kani {}", c.name), from_result(res));
    }
    if !any {
        r.step(
            "kani",
            Outcome::Pass(vec!["no crate has Kani harnesses yet".into()]),
        );
    }
}

fn verus(r: &mut Runner, crates: &[Crate], pins: &Pins) {
    if !on_path("cargo-verus") || !on_path("verus") {
        r.step(
            "verus",
            Outcome::Skip("verus / cargo-verus not installed".into()),
        );
        return;
    }
    let version = pins.get("VERUS_VERSION").map(str::to_owned);
    r.step(
        "verus version",
        from_result(version.and_then(|v| {
            let out = run(Command::new("verus").arg("--version"))?;
            if out.lines().any(|l| l.trim() == format!("Version: {v}")) {
                Ok(vec![v])
            } else {
                Err(format!("expected Verus {v}, got:\n{out}"))
            }
        })),
    );
    for c in crates.iter().filter(|c| c.verus) {
        r.step(
            &format!("verus {}", c.name),
            from_result(verus_crate(&c.dir, &c.name)),
        );
    }
}

fn verus_crate(dir: &Path, name: &str) -> Result<Vec<String>, String> {
    // Cargo would otherwise replay a cached result; force a fresh proof run.
    run(Command::new("cargo")
        .current_dir(dir)
        .args(["clean", "--quiet", "-p", name]))?;
    // `-A missing_docs` reaches only Verus, silencing accessors it generates
    // (is_Byte, ...). Clippy still enforces missing_docs on our code.
    let out = run(Command::new("cargo").current_dir(dir).args([
        "verus",
        "verify",
        "--locked",
        "--",
        "-A",
        "missing_docs",
    ]))?;
    let results: Vec<&str> = out
        .lines()
        .filter(|l| l.starts_with("verification results::"))
        .collect();
    match results.last() {
        Some(last) if last.ends_with(" 0 errors") => Ok(vec![(*last).to_owned()]),
        Some(last) => Err(format!("{last}\n{out}")),
        None => Err(format!("no verification results reported:\n{out}")),
    }
}

fn main() -> ExitCode {
    let mode = std::env::args().nth(1);
    let full = match mode.as_deref() {
        Some("verify") => true,
        Some("check") => false,
        _ => {
            eprintln!("usage: cargo xtask <verify|check>");
            return ExitCode::from(64);
        }
    };
    let mut r = Runner::default();
    let setup = workspace::load().and_then(|crates| Ok((crates, Pins::load()?)));
    let (crates, pins) = match setup {
        Ok(s) => s,
        Err(e) => {
            r.step("load workspace", Outcome::Fail(vec![e]));
            println!("RESULT: FAILED");
            return ExitCode::from(1);
        }
    };
    static_checks(&mut r, &crates, &pins);
    if full {
        build_checks(&mut r);
        kani(&mut r, &crates, &pins);
        verus(&mut r, &crates, &pins);
    }
    if r.failed {
        println!("RESULT: FAILED");
        ExitCode::from(1)
    } else if r.skipped {
        println!("RESULT: INCOMPLETE (checks skipped; not verified)");
        ExitCode::from(2)
    } else if full {
        println!("RESULT: ALL CHECKS PASSED");
        ExitCode::SUCCESS
    } else {
        println!(
            "RESULT: STATIC CHECKS PASSED (no build, tests or proofs run; use `cargo xtask verify`)"
        );
        ExitCode::SUCCESS
    }
}
