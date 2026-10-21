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

/// Verify only `module` (e.g. `uts46::process`), from scratch.
pub fn module(dir: &Path, name: &str, module: &str) -> Result<Run, String> {
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
    // CI sets CARGO_TERM_COLOR=always, which colours Verus's diagnostics and
    // would hide the lines `classify` looks for.
    let out = Command::new("cargo")
        .current_dir(dir)
        .env("CARGO_TERM_COLOR", "never")
        .args(args)
        .output()
        .map_err(|e| format!("cannot run cargo verus: {e}"))?;
    let text = format!(
        "{}{}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    );
    Ok(classify(text, out.status.success()))
}

/// Classify the combined output of one Verus run that exited with `success`.
fn classify(text: String, success: bool) -> Run {
    // Colour can still reach us (a tool that ignores CARGO_TERM_COLOR); the
    // line prefixes below are matched on the plain text.
    let text = strip_ansi(&text);
    // Verus prints one summary per verified crate; ours is the last. A
    // partial run appends "(partial verification ...)" to it.
    let summary = text
        .lines()
        .rfind(|l| l.starts_with("verification results::"))
        .map(str::to_owned);
    // An `assert(..) by (compute_only)` that does not evaluate to true stops
    // Verus before it prints a summary; it is still a failed proof, not a
    // build error. The message names what the expression reduced to: plain
    // "false" for a conjunction, "`1 == 0`, which evaluates to false" for a
    // single comparison.
    let compute_false = text
        .lines()
        .find(|l| l.starts_with("error: expression simplifies to "))
        .map(str::to_owned);
    match (summary, compute_false) {
        (Some(s), _) if success && s.contains(" 0 errors") => Run::Verified(s),
        (Some(s), _) if !s.contains(" 0 errors") => Run::ProofFailed(s, text),
        (_, Some(e)) => Run::ProofFailed(e, text),
        _ => Run::BuildFailed(text),
    }
}

/// `text` without ANSI CSI escape sequences (ESC `[`, parameters, one final
/// byte in `@`..=`~`), which is all a terminal colour code is.
fn strip_ansi(text: &str) -> String {
    let mut out = String::with_capacity(text.len());
    let mut chars = text.chars().peekable();
    while let Some(c) = chars.next() {
        if c == '\u{1b}' && chars.peek() == Some(&'[') {
            chars.next();
            for f in chars.by_ref() {
                if ('@'..='~').contains(&f) {
                    break;
                }
            }
        } else {
            out.push(c);
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::{Run, classify};

    fn kind(text: &str, success: bool) -> &'static str {
        match classify(text.to_owned(), success) {
            Run::Verified(_) => "verified",
            Run::ProofFailed(..) => "proof",
            Run::BuildFailed(_) => "build",
        }
    }

    #[test]
    fn compute_only_failures_are_proof_failures() {
        // A conjunction of false comparisons reduces all the way to `false`.
        let conjunction = "error: expression simplifies to false\n   --> src/utf8/lemmas.rs:9:12\n";
        assert_eq!(kind(conjunction, false), "proof");
        // A single comparison is reported with the comparison it reduced to
        // (output of Verus 0.2026.10.04).
        let single = "note: verifying module utf8::lemmas (selected functions)\n\n\
            error: expression simplifies to `1 == 4`, which evaluates to false\n   \
            --> crates/clazel-encoding/src/utf8/lemmas.rs:404:12\n\n\
            error: could not compile `clazel-encoding` (lib) due to 1 previous error\n";
        assert_eq!(kind(single, false), "proof");
    }

    #[test]
    fn coloured_output_is_classified_like_plain() {
        // As printed on GitHub Actions with CARGO_TERM_COLOR=always (CI run
        // 39570679453): every mutation was reported as a build failure.
        let single = "\u{1b}[1m\u{1b}[91merror\u{1b}[0m\u{1b}[1m: expression simplifies to \
            `1 == 4`, which evaluates to false\u{1b}[0m\n";
        assert_eq!(kind(single, false), "proof");
        let summary = "\u{1b}[1mverification results\u{1b}[0m:: 11 verified, 1 errors\n";
        assert_eq!(kind(summary, false), "proof");
        let type_error = "\u{1b}[1m\u{1b}[91merror[E0308]\u{1b}[0m: mismatched types\n";
        assert_eq!(kind(type_error, false), "build");
    }

    #[test]
    fn build_errors_stay_build_failures() {
        let type_error = "error[E0308]: mismatched types\n --> src/utf8/lemmas.rs:9:12\n\n\
            error: could not compile `clazel-encoding` (lib) due to 1 previous error\n";
        assert_eq!(kind(type_error, false), "build");
        // Mentioning the phrase mid-line is not a compute_only failure.
        let quoted = "error: cannot find function `f`: expression simplifies to nothing\n";
        assert_eq!(kind(quoted, false), "build");
    }

    #[test]
    fn summaries_decide_when_present() {
        let ok = "verification results:: 12 verified, 0 errors\n";
        assert_eq!(kind(ok, true), "verified");
        let failed = "verification results:: 11 verified, 1 errors\n";
        assert_eq!(kind(failed, false), "proof");
    }
}
