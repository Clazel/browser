//! Running Verus on one crate and classifying the result.

use std::path::Path;
use std::process::Command;

/// What a fresh Verus run on a crate produced.
pub enum Run {
    /// Every proof obligation verified. Holds the summary line.
    Verified(String),
    /// The crate compiled, and at least one obligation failed. Holds the
    /// summary line and the full output.
    ProofFailed(String, String),
    /// No verification summary: the crate did not get as far as proving
    /// (syntax, type or build error). Holds the full output.
    BuildFailed(String),
}

/// Run Verus on the crate in `dir` from scratch. `Err` only if the tools
/// could not be started at all.
pub fn run(dir: &Path, name: &str, locked: bool) -> Result<Run, String> {
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
    let mut args = vec!["verus", "verify"];
    if locked {
        args.push("--locked");
    }
    // `-A missing_docs` reaches only Verus, silencing accessors it generates
    // (is_Byte, ...). Clippy still enforces missing_docs on our code.
    args.extend(["--", "-A", "missing_docs"]);
    let out = Command::new("cargo")
        .current_dir(dir)
        .args(&args)
        .output()
        .map_err(|e| format!("cannot run cargo verus: {e}"))?;
    let text = format!(
        "{}{}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    );
    // Verus prints one summary per verified crate; ours is the last.
    let summary = text
        .lines()
        .rfind(|l| l.starts_with("verification results::"))
        .map(str::to_owned);
    Ok(match summary {
        Some(s) if out.status.success() && s.ends_with(" 0 errors") => Run::Verified(s),
        Some(s) if !s.ends_with(" 0 errors") => Run::ProofFailed(s, text),
        _ => Run::BuildFailed(text),
    })
}
