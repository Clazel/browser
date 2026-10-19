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
if command -v cargo-verus >/dev/null 2>&1; then
  verus_crate() {
    local out result
    # Cargo would otherwise replay a cached result; force a fresh proof run.
    (cd "$1" && cargo clean --quiet -p "$(basename "$1")")
    out=$(cd "$1" && cargo verus verify 2>&1) || { printf '%s\n' "$out"; return 1; }
    result=$(printf '%s\n' "$out" | grep 'verification results' | tail -1)
    [ -n "$result" ] || { echo "    no verification results reported"; return 1; }
    printf '    %s\n' "$result"
  }
  for manifest in crates/*/Cargo.toml; do
    grep -q '^\[package.metadata.verus\]' "$manifest" || continue
    dir=$(dirname "$manifest")
    step "verus $(basename "$dir")" verus_crate "$dir"
  done
else
  skip "verus" "cargo-verus not installed"
fi

if [ $failed -ne 0 ]; then echo "RESULT: FAILED"; exit 1; fi
if [ $skipped -ne 0 ]; then echo "RESULT: INCOMPLETE (checks skipped; not verified)"; exit 2; fi
echo "RESULT: ALL CHECKS PASSED"
