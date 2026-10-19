#!/usr/bin/env bash
# Runs every check in docs/VERIFICATION.md. Exit codes:
#   0  all checks ran and passed
#   1  a check failed
#   2  no failures, but some checks were skipped because a tool is missing
#      (never report this as "verified")
set -uo pipefail
cd "$(dirname "$0")/.."
# shellcheck source=toolchains.env
. scripts/toolchains.env

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

# Every crate declares its tier and inherits the workspace lints
# (docs/VERIFICATION.md). Whether the declared tier is true is checked by
# the xtask checker once it exists (Phase 0 item 0.4).
crate_declarations() {
  local m ok=0
  for m in crates/*/Cargo.toml; do
    grep -q '^\[package.metadata.clazel\]' "$m" &&
      grep -qE '^tier = [0-3]$' "$m" &&
      grep -qE '^target-tier = [0-3]$' "$m" ||
      { echo "    $m: missing [package.metadata.clazel] tier / target-tier"; ok=1; }
    grep -qx 'workspace = true' "$m" && grep -qx '\[lints\]' "$m" ||
      { echo "    $m: missing [lints] workspace = true"; ok=1; }
  done
  return $ok
}
step "crate tier declarations" crate_declarations

# Pinned versions (scripts/toolchains.env). A proof run with a different
# tool version is not the result we document, so a mismatch is a failure.
toolchain_pin() { grep -qx "channel = \"$RUST_TOOLCHAIN\"" rust-toolchain.toml; }
step "rust-toolchain.toml pins $RUST_TOOLCHAIN" toolchain_pin
vstd_pins() {
  local bad
  bad=$(grep -l '^\[package.metadata.verus\]' crates/*/Cargo.toml |
    xargs grep -L "^vstd = \"=$VSTD_VERSION\"")
  [ -z "$bad" ] || { echo "    vstd not pinned to =$VSTD_VERSION in: $bad"; return 1; }
}
step "vstd pinned to $VSTD_VERSION" vstd_pins

# Tier 1
if command -v cargo-kani >/dev/null 2>&1; then
  # Capture first: `tool | grep -q` fails under pipefail when grep exits early.
  kani_version() { local v; v=$(cargo kani --version) && grep -q "Kani Rust Verifier $KANI_VERSION " <<<"$v"; }
  step "kani version $KANI_VERSION" kani_version
  step "kani" cargo kani --workspace
else
  skip "kani" "cargo-kani not installed"
fi

# Tier 2
if command -v cargo-verus >/dev/null 2>&1; then
  verus_version() { local v; v=$(verus --version 2>&1) && grep -q "Version: $VERUS_VERSION\$" <<<"$v"; }
  step "verus version $VERUS_VERSION" verus_version
  verus_crate() {
    local out result
    # `-A missing_docs` applies only to the Verus run, where it silences
    # accessors Verus generates (is_Byte, ...). Clippy above still enforces
    # missing_docs on our code.
    # Cargo would otherwise replay a cached result; force a fresh proof run.
    (cd "$1" && cargo clean --quiet -p "$(basename "$1")")
    out=$(cd "$1" && cargo verus verify -- -A missing_docs 2>&1) || { printf '%s\n' "$out"; return 1; }
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
