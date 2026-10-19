//! Running Verus on one crate and classifying the result.

use std::path::Path;
use std::process::Command;

/// What a fresh Verus run on a crate produced.
pub enum Run {
    /// Every proof obligation verified. Holds the summary line.
    Verified(String),
    /// The crate compiled, and at least one obligation failed. Holds the
    /// summary line (or the failing evaluation) and the full output.
    ProofFailed(String, String),
    /// No verification summary: the crate did not get as far as proving
    /// (syntax, type or build error). Holds the full output.
    BuildFailed(String),
}

/// Run Verus on the whole crate in `dir`, from scratch. `Err` only if the
/// tools could not be started at all.
pub fn run(dir: &Path, name: &str, locked: bool) -> Result<Run, String> {
    let mut args = vec!["verus", "verify"];
    if locked {
        args.push("--locked");
    }
    // `-A missing_docs` reaches only Verus, silencing accessors it generates
    // (is_Byte, ...). Clippy still enforces missing_docs on our code.
    args.extend(["--", "-A", "missing_docs"]);
    invoke(dir, name, &args)
}

/// Verify only `function` in `module` (e.g. `utf8::lemmas`), from scratch.
pub fn focus(dir: &Path, name: &str, module: &str, function: &str) -> Result<Run, String> {
    invoke(
        dir,
        name,
        &[
            "verus",
            "focus",
            "--",
            "-A",
            "missing_docs",
            "--verify-only-module",
            module,
            "--verify-function",
            function,
        ],
    )
}

fn invoke(dir: &Path, name: &str, args: &[&str]) -> Result<Run, String> {
    // Cargo would otherwise replay a cached result; force a fresh proof run.
    let clean = Command::new("cargo")
        .current_dir(dir)
        .args(["clean", "--quiet", "-p", name])
        .output()
        .map_err(|e| format!("cannot run cargo clean: {e}"))?;
    if !clean.status.success() {
        return Err(format!(
            "cargo clean -p {name} failed:\n{}",
            String::from_utf8_lossy(&clean.stderr)
        ));
    }
    let out = Command::new("cargo")
        .current_dir(dir)
        .args(args)
        .output()
        .map_err(|e| format!("cannot run cargo verus: {e}"))?;
    let text = format!(
        "{}{}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    );
    // Verus prints one summary per verified crate; ours is the last. A
    // partial run appends "(partial verification ...)" to it.
    let summary = text
        .lines()
        .rfind(|l| l.starts_with("verification results::"))
        .map(str::to_owned);
    // An `assert(..) by (compute_only)` that evaluates to false stops Verus
    // before it prints a summary; it is still a failed proof, not a build error.
    let compute_false = text
        .lines()
        .find(|l| l.starts_with("error: expression simplifies to false"))
        .map(str::to_owned);
    Ok(match (summary, compute_false) {
        (Some(s), _) if out.status.success() && s.contains(" 0 errors") => Run::Verified(s),
        (Some(s), _) if !s.contains(" 0 errors") => Run::ProofFailed(s, text),
        (_, Some(e)) => Run::ProofFailed(e, text),
        _ => Run::BuildFailed(text),
    })
}
