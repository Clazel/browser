//! `cargo xtask`: runs and enforces every check in `docs/VERIFICATION.md`.
//!
//! - `cargo xtask verify`: everything, with fresh proof runs. Exit 0 only if
//!   every check ran and passed; 1 if any failed; 2 if none failed but some
//!   were skipped because a tool is missing (never report that as verified).
//! - `cargo xtask check`: only the fast static checks (no build, no proofs).
//! - `cargo xtask mutate`: only the proof mutation tests (also part of
//!   `verify`).
//! - `cargo xtask testdata`: regenerate the Rust tables converted from
//!   vendored conformance suites (`tests/generated/*.rs`). `check` and
//!   `verify` fail if a committed table is stale.
//! - `cargo xtask tables`: regenerate the Unicode tables generated from
//!   vendored Unicode data (`crates/clazel-idna/src/uts46/data.rs`).
//!   `check` and `verify` fail if they are stale or a data file's hash
//!   differs from its `SOURCE.md`.
//! - `cargo xtask report [--write]`: run the checks that produce the README
//!   status table (including each crate's conformance suites, see
//!   `conformance.rs`), print it, and with `--write` update README.md. `verify`
//!   fails if README.md's table differs from what it measured.

mod conformance;
mod deps;
mod mutate;
mod pins;
mod report;
mod reviews;
mod scan;
mod testdata;
mod unicode;
mod verus;
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
    /// What the checks measured, for the README status table.
    metrics: report::Table,
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
    let (review_status, review_problems) = match reviews::status(crates) {
        Ok(s) => s,
        Err(e) => (std::collections::BTreeMap::new(), vec![e]),
    };
    for c in crates {
        let files = review_status.get(&c.name).map_or(&[][..], Vec::as_slice);
        let current = files
            .iter()
            .filter(|f| f.status == reviews::Status::Current)
            .count();
        let m = r.metrics.entry(c.name.clone()).or_default();
        m.tier = c.tier;
        m.target_tier = c.target_tier;
        m.is_verus = c.verus;
        m.reviews = Some((current, files.len()));
        match workspace::scan_crate(c) {
            Ok(s) => {
                m.axioms = s.axioms;
                m.kani_harnesses = s.kani_proofs;
                violations.extend(s.violations);
                axioms = axioms.saturating_add(s.axioms);
                let evidence = mutate::gaps(c).and_then(|mutations| {
                    let (conformance_tests, independent_spec) = workspace::evidence_files(c)?;
                    Ok(workspace::TierEvidence {
                        kani_proofs: s.kani_proofs,
                        mutations,
                        conformance_tests,
                        independent_spec,
                    })
                });
                let (bad, notes) = match evidence {
                    Ok(ev) => workspace::check_tiers(c, &ev),
                    Err(e) => (vec![e], Vec::new()),
                };
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
    // Unreviewed specs are not a failure (agents must be able to edit
    // them), but every run lists them.
    let review_notes: Vec<String> = review_status
        .values()
        .flatten()
        .filter(|f| f.status != reviews::Status::Current)
        .map(|f| {
            let what = if f.status == reviews::Status::Stale {
                "stale     "
            } else {
                "unreviewed"
            };
            format!("{what} {}  sha256 {}", f.file, f.sha256)
        })
        .collect();
    let total: usize = review_status.values().map(Vec::len).sum();
    let mut notes = vec![format!(
        "{} of {total} spec files reviewed and current",
        total.saturating_sub(review_notes.len())
    )];
    notes.extend(review_notes);
    r.step("spec reviews", outcome(review_problems, notes));
    r.step("pinned versions", from_result(check_pins(crates, pins)));
    let (problems, notes) = testdata::run(crates, false);
    r.step("generated test data", outcome(problems, notes));
    let (problems, notes) = unicode::run(false);
    r.step("generated Unicode tables", outcome(problems, notes));
    let tooling = crates
        .iter()
        .filter(|c| c.tooling)
        .map(|c| c.name.clone())
        .collect();
    r.step(
        "dependency allowlist",
        match deps::check(&tooling) {
            Ok(summary) => Outcome::Pass(vec![summary]),
            Err(problems) => Outcome::Fail(problems),
        },
    );
}

const CHECKSUMS: &str = "scripts/checksums.txt";

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
    // Test-only engines are pinned exactly too, so a differential test
    // always compares against the version on the allowlist.
    for c in crates.iter().filter(|c| !c.tooling) {
        if let Some((n, req)) = c.dev_deps.iter().find(|(_, r)| !r.starts_with('=')) {
            return Err(format!(
                "{}: dev-dependency {n} must be pinned to an exact version (\"=x.y.z\"), found {req:?}",
                c.name
            ));
        }
    }
    // Every file setup.sh downloads for the pinned versions has a checksum.
    let verus_v = pins.get("VERUS_VERSION")?;
    let kani_v = pins.get("KANI_VERSION")?;
    let mut needed: Vec<String> = ["arm64-macos", "x86-macos", "x86-linux"]
        .iter()
        .map(|p| format!("verus-{verus_v}-{p}.zip"))
        .collect();
    needed.extend(
        [
            "aarch64-apple-darwin",
            "x86_64-apple-darwin",
            "x86_64-unknown-linux-gnu",
        ]
        .iter()
        .map(|t| format!("kani-{kani_v}-{t}.tar.gz")),
    );
    // The Dockerfile's rustup.
    needed.push(format!(
        "rustup-init-{}-x86_64-unknown-linux-gnu",
        pins.get("RUSTUP_VERSION")?
    ));
    let sums = std::fs::read_to_string(CHECKSUMS).map_err(|e| format!("{CHECKSUMS}: {e}"))?;
    let listed: Vec<&str> = sums
        .lines()
        .filter(|l| !l.trim_start().starts_with('#'))
        .filter_map(
            |l| match l.split_whitespace().collect::<Vec<_>>().as_slice() {
                [sum, name] if sum.len() == 64 && sum.chars().all(|c| c.is_ascii_hexdigit()) => {
                    Some(*name)
                }
                _ => None,
            },
        )
        .collect();
    let missing: Vec<&String> = needed
        .iter()
        .filter(|n| !listed.contains(&n.as_str()))
        .collect();
    if !missing.is_empty() {
        return Err(format!("{CHECKSUMS}: no SHA-256 for {missing:?}"));
    }
    Ok(vec![format!(
        "rust {rust}, vstd {vstd}, checksums for {} downloads",
        needed.len()
    )])
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

/// Run every test under Miri, which reports undefined behaviour (Tier 0).
/// Our code has no `unsafe`, so this mostly checks dependency code that the
/// tests execute, and it will check the audited `sys` crate once it exists.
fn miri(r: &mut Runner, pins: &Pins) {
    const NAME: &str = "tests under Miri";
    let nightly = match pins.get("MIRI_NIGHTLY") {
        Ok(n) => format!("+{n}"),
        Err(e) => {
            r.step(NAME, Outcome::Fail(vec![e]));
            return;
        }
    };
    if run(Command::new("cargo").args([nightly.as_str(), "miri", "--version"])).is_err() {
        r.step(
            NAME,
            Outcome::Skip(format!(
                "Miri not installed on {}; run scripts/setup.sh",
                nightly.trim_start_matches('+')
            )),
        );
        return;
    }
    let res = run(Command::new("cargo").args([
        nightly.as_str(),
        "miri",
        "test",
        "--workspace",
        "--locked",
    ]))
    .map(|out| {
        let passed: u64 = out
            .lines()
            .filter_map(|l| l.strip_prefix("test result: ok. "))
            .filter_map(|l| l.split(' ').next()?.parse::<u64>().ok())
            .sum();
        vec![format!(
            "{passed} tests passed under Miri ({})",
            nightly.trim_start_matches('+')
        )]
    });
    r.step(NAME, from_result(res));
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
            run(Command::new("cargo").args(["kani", "-p", &c.name])).and_then(|out| {
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
        if let Ok(lines) = &res {
            let summary = lines.join(" ");
            let summary = summary
                .trim_start_matches("Complete - ")
                .trim_end_matches('.');
            r.metrics.entry(c.name.clone()).or_default().kani = Some(summary.to_owned());
        }
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
        let res = verus_crate(&c.dir, &c.name);
        if let Ok(lines) = &res
            && let Some(summary) = lines.first()
        {
            let summary = summary.trim_start_matches("verification results:: ");
            r.metrics.entry(c.name.clone()).or_default().verus = Some(summary.to_owned());
        }
        r.step(&format!("verus {}", c.name), from_result(res));
        let counted = report::line_count(&c.dir);
        if let Ok(l) = &counted {
            r.metrics.entry(c.name.clone()).or_default().lines = Some(l.clone());
        }
        r.step(
            &format!("line count {}", c.name),
            from_result(counted.map(|l| {
                vec![format!(
                    "spec {}, proof {}, exec {}",
                    l.spec, l.proof, l.exec
                )]
            })),
        );
    }
}

fn verus_crate(dir: &Path, name: &str) -> Result<Vec<String>, String> {
    match verus::run(dir, name, true)? {
        verus::Run::Verified(s) => Ok(vec![s]),
        verus::Run::ProofFailed(s, out) => Err(format!("{s}\n{out}")),
        verus::Run::BuildFailed(out) => Err(format!("no verification results reported:\n{out}")),
    }
}

/// Mutation tests for every Verus crate, or only the one named `only`.
fn mutations(r: &mut Runner, crates: &[Crate], root: &Path, only: Option<&str>) {
    if !on_path("cargo-verus") || !on_path("verus") {
        r.step(
            "proof mutation tests",
            Outcome::Skip("verus / cargo-verus not installed".into()),
        );
        return;
    }
    for c in crates
        .iter()
        .filter(|c| c.verus && only.is_none_or(|n| n == c.name))
    {
        let name = format!("proof mutation tests {}", c.name);
        if !mutate::has_mutations(c) {
            // A Verus crate with no mutations has unchecked proofs.
            r.step(
                &name,
                Outcome::Fail(vec![format!(
                    "{}: Verus crate has no {}",
                    c.name,
                    mutate::FILE
                )]),
            );
            continue;
        }
        let outcome = match mutate::run(c, root) {
            Ok(rep) => {
                r.metrics.entry(c.name.clone()).or_default().mutations = Some(report::Mutations {
                    killed: rep.killed,
                    incidental: rep.incidental,
                    survived: rep.survived,
                    total: rep.total,
                });
                let mut lines = rep.lines;
                lines.push(format!(
                    "{} mutations: {} killed by a theorem, {} killed incidentally (not coverage), {} survived (known gaps)",
                    rep.total, rep.killed, rep.incidental, rep.survived
                ));
                outcome(rep.problems, lines)
            }
            Err(e) => Outcome::Fail(vec![e]),
        };
        r.step(&name, outcome);
    }
}

/// Run every crate's conformance tests and record the suites they report
/// (format: `conformance.rs`).
fn conformance_suites(r: &mut Runner, crates: &[Crate]) {
    for c in crates {
        let res = conformance::run(c);
        let outcome = match res {
            Ok(suites) if suites.is_empty() => {
                r.metrics.entry(c.name.clone()).or_default().conformance = Some(Vec::new());
                continue;
            }
            Ok(suites) => {
                let notes = suites
                    .iter()
                    .map(|s| {
                        format!(
                            "{}: {} pass, {} expected failures, {} fail, of {}",
                            s.name, s.pass, s.xfail, s.fail, s.total
                        )
                    })
                    .collect();
                r.metrics.entry(c.name.clone()).or_default().conformance = Some(suites);
                Outcome::Pass(notes)
            }
            Err(problems) => Outcome::Fail(problems),
        };
        r.step(&format!("conformance {}", c.name), outcome);
    }
}

/// Compare (or, with `write`, update) README.md's status table against what
/// this run measured.
fn readme_table(r: &mut Runner, write: bool) {
    const NAME: &str = "README status table";
    let incomplete: Vec<&String> = r
        .metrics
        .iter()
        .filter(|(_, m)| !m.complete())
        .map(|(n, _)| n)
        .collect();
    if !incomplete.is_empty() {
        r.step(
            NAME,
            Outcome::Skip(format!("not all metrics were measured, for {incomplete:?}")),
        );
        return;
    }
    let block = report::render(&r.metrics);
    let readme = match std::fs::read_to_string(report::README) {
        Ok(t) => t,
        Err(e) => {
            r.step(
                NAME,
                Outcome::Fail(vec![format!("{}: {e}", report::README)]),
            );
            return;
        }
    };
    if write {
        // Never publish numbers from a run where something failed.
        let outcome = if r.failed {
            Outcome::Fail(vec!["refusing to write: a check above failed".into()])
        } else {
            match report::splice(&readme, &block)
                .and_then(|new| std::fs::write(report::README, new).map_err(|e| e.to_string()))
            {
                Ok(()) => Outcome::Pass(vec![format!("wrote {}", report::README), block]),
                Err(e) => Outcome::Fail(vec![e]),
            }
        };
        r.step(NAME, outcome);
        return;
    }
    let outcome = match report::current(&readme) {
        Some(cur) if cur == block => Outcome::Pass(Vec::new()),
        Some(_) => Outcome::Fail(vec![
            "README.md's table differs from what this run measured.".into(),
            "Run `cargo xtask report --write` and commit the result. Measured:".into(),
            block,
        ]),
        None => Outcome::Fail(vec![format!(
            "{} has no {} … {} block",
            report::README,
            report::BEGIN,
            report::END
        )]),
    };
    r.step(NAME, outcome);
}

/// `cargo xtask testdata`: rewrite every stale generated table.
fn generate_testdata() -> ExitCode {
    let mut r = Runner::default();
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).parent();
    if !root.is_some_and(|p| std::env::set_current_dir(p).is_ok()) {
        r.step(
            "find repository root",
            Outcome::Fail(vec!["cannot enter the repository root".into()]),
        );
        return ExitCode::from(1);
    }
    let res = workspace::load().map(|crates| testdata::run(&crates, true));
    match res {
        Ok((problems, notes)) => r.step("generate test data", outcome(problems, notes)),
        Err(e) => r.step("load workspace", Outcome::Fail(vec![e])),
    }
    if r.failed {
        println!("RESULT: FAILED");
        ExitCode::from(1)
    } else {
        println!("RESULT: TEST DATA UP TO DATE");
        ExitCode::SUCCESS
    }
}

/// `cargo xtask tables`: rewrite the generated Unicode tables if stale.
fn generate_tables() -> ExitCode {
    let mut r = Runner::default();
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).parent();
    if !root.is_some_and(|p| std::env::set_current_dir(p).is_ok()) {
        r.step(
            "find repository root",
            Outcome::Fail(vec!["cannot enter the repository root".into()]),
        );
        return ExitCode::from(1);
    }
    let (problems, notes) = unicode::run(true);
    r.step("generate Unicode tables", outcome(problems, notes));
    if r.failed {
        println!("RESULT: FAILED");
        ExitCode::from(1)
    } else {
        println!("RESULT: UNICODE TABLES UP TO DATE");
        ExitCode::SUCCESS
    }
}

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let args: Vec<&str> = args.iter().map(String::as_str).collect();
    // `mutate <crate>` runs one crate's mutations, for iterating on them.
    let mut only_crate: Option<&str> = None;
    let (full, only_mutate, report_mode, write) = match args.as_slice() {
        ["testdata"] => return generate_testdata(),
        ["tables"] => return generate_tables(),
        ["verify"] => (true, false, false, false),
        ["check"] => (false, false, false, false),
        ["mutate"] => (false, true, false, false),
        ["mutate", name] => {
            only_crate = Some(name);
            (false, true, false, false)
        }
        ["report"] => (false, false, true, false),
        ["report", "--write"] => (false, false, true, true),
        _ => {
            eprintln!(
                "usage: cargo xtask <verify|check|mutate [crate]|testdata|tables|report [--write]>"
            );
            return ExitCode::from(64);
        }
    };
    let mut r = Runner::default();
    // Always work from the repository root, wherever cargo was invoked.
    let root = Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .map(Path::to_path_buf);
    let Some(root) = root.filter(|p| std::env::set_current_dir(p).is_ok()) else {
        r.step(
            "find repository root",
            Outcome::Fail(vec!["cannot enter the repository root".into()]),
        );
        println!("RESULT: FAILED");
        return ExitCode::from(1);
    };
    let setup = workspace::load().and_then(|crates| Ok((crates, Pins::load()?)));
    let (crates, pins) = match setup {
        Ok(s) => s,
        Err(e) => {
            r.step("load workspace", Outcome::Fail(vec![e]));
            println!("RESULT: FAILED");
            return ExitCode::from(1);
        }
    };
    if only_mutate {
        if only_crate.is_some_and(|n| !crates.iter().any(|c| c.name == n)) {
            r.step(
                "select crate",
                Outcome::Fail(vec![format!("no workspace crate named {only_crate:?}")]),
            );
        }
        mutations(&mut r, &crates, &root, only_crate);
    } else {
        static_checks(&mut r, &crates, &pins);
    }
    if full {
        build_checks(&mut r);
        miri(&mut r, &pins);
    }
    if full || report_mode {
        kani(&mut r, &crates, &pins);
        verus(&mut r, &crates, &pins);
        mutations(&mut r, &crates, &root, None);
        conformance_suites(&mut r, &crates);
        readme_table(&mut r, write);
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
    } else if only_mutate {
        println!("RESULT: MUTATION TESTS PASSED (other checks not run)");
        ExitCode::SUCCESS
    } else if report_mode {
        println!("RESULT: REPORT CHECKS PASSED (fmt, clippy and tests not run)");
        ExitCode::SUCCESS
    } else {
        println!(
            "RESULT: STATIC CHECKS PASSED (no build, tests or proofs run; use `cargo xtask verify`)"
        );
        ExitCode::SUCCESS
    }
}
