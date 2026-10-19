#!/usr/bin/env bash
# Runs every check in docs/VERIFICATION.md. Exit codes:
#   0  all checks ran and passed
#   1  a check failed
#   2  no failures, but some checks were skipped because a tool is missing
#      (never report this as "verified")
set -uo pipefail
cd "$(dirname "$0")/.."

failed=0
skipped=0

step() {
  local name=$1; shift
  printf '==> %s\n' "$name"
  if "$@"; then printf '    PASS  %s\n' "$name"
  else printf '    FAIL  %s\n' "$name"; failed=1; fi
}

skip() { printf '==> %s\n    SKIP  %s (%s)\n' "$1" "$1" "$2"; skipped=1; }

# Tier 0
step "rustfmt" cargo fmt --all -- --check
step "clippy"  cargo clippy --workspace --all-targets -- -D warnings
step "tests"   cargo test --workspace --quiet

# Ban proof escape hatches outside axioms.rs files (CLAUDE.md rule 4).
escape_hatches() {
  ! grep -rnE '\b(assume|admit)\s*\(|verifier::external_body|exec_allows_no_decreases_clause' \
      --include='*.rs' crates | grep -v '/axioms\.rs:'
}
step "no proof escape hatches" escape_hatches

# Tier 1
if command -v cargo-kani >/dev/null 2>&1; then
  step "kani" cargo kani --workspace
else
  skip "kani" "cargo-kani not installed"
fi

# Tier 2
if command -v verus >/dev/null 2>&1; then
  for lib in crates/*/src/lib.rs; do
    grep -q 'verus!' "$lib" || continue
    step "verus $(basename "$(dirname "$(dirname "$lib")")")" verus --crate-type=lib "$lib"
  done
else
  skip "verus" "verus not installed"
fi

if [ $failed -ne 0 ]; then echo "RESULT: FAILED"; exit 1; fi
if [ $skipped -ne 0 ]; then echo "RESULT: INCOMPLETE (checks skipped; not verified)"; exit 2; fi
echo "RESULT: ALL CHECKS PASSED"
