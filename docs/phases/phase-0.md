# Phase 0: Foundations, detailed plan

**Goal:** before the browser itself gets much code, build the machinery that
makes every later claim checkable. When Phase 0 is done, anyone can clone
the repo, run one command, and get a fresh, honest answer to "what is
proven, what is only tested, and what is assumed?"

Most of this phase is tooling, not browser code. That is deliberate: the
project's credibility depends on the checks being stricter than the code
they check.

## Exit criteria

Phase 0 is done when all of these hold on both macOS and Linux:

1. `scripts/setup.sh` installs every pinned tool from a clean machine, and
   checksums each download.
2. `scripts/verify.sh` runs every check in `docs/VERIFICATION.md` from
   scratch (never a cached result) and exits 0.
3. Every crate declares its tier in machine-readable form, and the tier is
   enforced, not just documented.
4. The README verification table is generated, and `verify.sh` fails if it
   is stale.
5. Proof mutation tests show each Tier 2 proof fails when its spec is
   broken.
6. Every resolved dependency is on the allowlist.
7. Every spec file has a recorded human review that matches its current
   contents, or `verify.sh` reports it as unreviewed.

## Status at the time of writing

| Item | State |
|------|-------|
| Git repo, Cargo workspace, MIT license | done |
| Workspace lints (no `unsafe`, no panicking constructs) | done |
| `CLAUDE.md` contributor rules | done; needs additions (0.9) |
| Verus 0.2026.10.04 and Kani 0.68.0 on the dev Mac | done, by hand |
| `verify.sh`: fmt, clippy, tests, escape-hatch grep, Kani, Verus | done, basic version |
| Fresh (uncached) Verus runs | done |
| 0.1 Toolchain pin (`rust-toolchain.toml`, `scripts/toolchains.env`, version checks in `verify.sh`) | done |
| 0.3 Machine-readable tiers (declared and checked present; truth checked in 0.4) | done |
| 0.12 Verus output noise | done |
| 0.4 `xtask` checker (token scanner, tier truth, pins, runner; `verify.sh` wraps it) | done |
| 0.6 Proof mutation testing (`cargo xtask mutate`, part of `verify`) | done: 10 UTF-8 mutations, 2 killed by a theorem |
| Reproducible setup, tier enforcement, metrics, mutation tests, Miri, dependency allowlist, spec reviews, Linux | **not started** |
| GitHub Actions CI | **deferred** (by decision, 2026-10-19) |

The UTF-8 decoder spec (Phase 1 work) was started early to prove out the
toolchain. It is the first real user of everything below.

## Work items

Ordered by dependency. Size: S is under a day, M is a few days.

### 0.1 Pin the toolchain (S)

- Add `rust-toolchain.toml` pinning Rust `1.98.1`, the toolchain Verus
  0.2026.10.04 is built against, so `cargo build` and Verus see the same
  compiler. Kani keeps using its own pinned nightly (`nightly-2026-08-21`),
  which `cargo kani` selects by itself.
- Pin a nightly for Miri in one place (`scripts/toolchains.env`), next to
  the Verus and Kani versions.
- **Done when:** a fresh `cargo build` in the repo uses 1.98.1 without
  manual `rustup` commands.

### 0.2 `scripts/setup.sh`: reproducible install (M)

- Installs, in order: rustup toolchains from `toolchains.env`, Kani
  (`cargo install --locked kani-verifier --version 0.68.0` then
  `cargo kani setup`), Verus from the GitHub release zip, and Miri.
- Verus downloads are checked against SHA-256 sums committed in
  `scripts/checksums.txt`. A mismatch aborts the install. Proof tools are part of
  the trusted computing base, so a swapped binary would undermine
  everything.
- Platforms: macOS arm64, macOS x86-64, Linux x86-64. Verus publishes no
  Linux arm64 build, so on Linux arm64 the script fails with a clear message.
  Building Verus from source there is a later task.
- Installs into a user-local prefix (`~/.local/share/clazel-tools/`) and
  never needs `sudo`.
- **Done when:** on a machine with only rustup, `scripts/setup.sh &&
  scripts/verify.sh` passes.

### 0.3 Machine-readable tiers (S)

Each crate's `Cargo.toml` gets:

```toml
[package.metadata.clazel]
tier = 2          # what is actually proven today
target-tier = 2   # what docs/VERIFICATION.md requires for this crate
```

The checker (0.4) enforces:
- `tier >= 2` requires `[package.metadata.verus] verify = true`.
- `tier >= 1` requires at least one `#[kani::proof]` harness per public
  function that takes untrusted input. Initially this is approximated as "at
  least one harness per module that parses bytes".
- `tier < target-tier` is allowed but always shown in the report, so a
  shortfall is visible rather than hidden.
- Every crate has `[lints] workspace = true`.

`clazel-encoding` is declared `tier = 0, target-tier = 2` until the
decoder implementation is proven. The spec being proven does not make the
crate Tier 2.

### 0.4 `xtask`: replace shell checks with a real checker (M)

The grep-based checks in `verify.sh` will not scale. Move them into a
workspace `xtask` crate (`cargo xtask verify`), and keep `verify.sh` as a
thin wrapper around it.

- Reads `cargo metadata` output to find crates, tiers and dependencies.
- **Escape hatches:** bans `assume(`, `admit(`, `#[verifier::external_body]`,
  `#[verifier::external]`, `#[verifier::external_fn_specification]`,
  `assume_specification`, and `exec_allows_no_decreases_clause` outside
  `axioms.rs` files. Each axiom must have a `// AXIOM:` justification
  comment.
- **Lint overrides:** bans `#[allow]`, `#[expect]` and `#![allow]`, with
  one allowlisted exception: `#[allow(unused_imports)]` directly on a
  `use vstd::prelude::*` or `use super::spec::*` line. Ghost imports look
  unused to a normal build, so the exception is needed.
- Uses `syn` to parse source files instead of grepping text, so
  comments and strings cannot cause false hits or misses.
- `xtask` is build tooling and never ships in the browser, so its
  dependencies (`syn`, `serde_json`, `toml`) go in a separate "tooling"
  section of the allowlist (0.7). It is Tier 0 itself.
- **Done when:** every check now in `verify.sh` runs from `xtask`, and a
  planted violation of each kind is caught (see the self-tests in 0.6).

### 0.5 Honesty metrics and a generated README table (M)

`cargo xtask report` prints, per crate:

| Column | Source |
|--------|--------|
| Tier / target tier | `[package.metadata.clazel]` |
| Verus: verified / errors | `cargo verus verify` output |
| Kani: harnesses passed / total | `cargo kani` output |
| Axioms | count of `// AXIOM:` items |
| Spec / proof / exec lines | Verus's bundled `line_count` tool |
| Spec review | up to date / stale / missing (0.8) |
| Mutation score | killed / total (0.6) |

The README table lives between `<!-- BEGIN STATUS -->` and
`<!-- END STATUS -->` markers. `cargo xtask report --write` regenerates it,
and `verify` fails if the committed table differs from the real numbers.
The numbers can then never drift from reality. (Right now the README's "16"
is typed by hand.)

### 0.6 Proof mutation testing (M)

A proof that passes no matter what the spec says proves nothing. Each Verus
crate gets a `mutations.json` (JSON rather than TOML, because `xtask`
already depends on `serde_json`). The format is documented in
`xtask/src/mutate.rs`.

**As built:** `expect` has three values, not two. While seeding the UTF-8
mutations, most "kills" turned out to break only the proof *script* (an
invariant that restates the spec's boundaries, or a case split), not a
theorem: the mutant still satisfied every proven property. Counting those as
coverage would overstate what is proven. So:
- `killed`: a proven theorem is false for the mutant (real coverage);
- `killed-incidentally`: the proofs fail, but every theorem still holds;
- `survives`: a known gap.

The report names the first failing proof for each kill, so the
classification can be checked.

`cargo xtask mutate` applies each mutation to a scratch copy of the
crate, runs Verus, and **requires a failure**. A surviving mutation fails
the run. Seed the UTF-8 crate with at least:

- ED upper boundary 0x9F → 0xBF (surrogates). Already checked by hand, and it fails.
- F4 upper boundary 0x8F → 0xBF (code points above U+10FFFF).
- E0 lower boundary 0xA0 → 0x80 (overlong three-byte forms).
- `0xC2 <= byte` → `0xC0 <= byte` (overlong two-byte forms).
- Drop `restored: true` (the byte after an invalid continuation is lost).

Not every spec mutation should break the *current* lemmas. Some will only
be caught once the exec contract exists. Those go in with
`expect = "survives-until-impl"`, and the report lists them so the gap
stays visible.

The same harness gives `xtask` self-tests: plant an `admit()` and an
`#[allow(clippy::unwrap_used)]` and check that `verify` rejects both.

### 0.7 Dependency allowlist (S)

- Turn `docs/DEPENDENCIES.md` into a generated view of
  `deps-allowlist.toml`, which has two sections: `[shipped]` (code in the
  browser binary) and `[tooling]` (xtask, proof libraries).
- `xtask verify` resolves the full dependency graph and fails on any crate
  or version not listed.
- Current graph: `vstd` and its proc-macro chain (`verus_builtin`,
  `verus_builtin_macros`, `verus_syn`, `verus_prettyplease`,
  `verus_state_machines_macros`, `syn`, `quote`, `proc-macro2`,
  `unicode-ident`, `synstructure`, `convert_case`, `indexmap`, `hashbrown`,
  `equivalent`). All of these are proc-macro or ghost-code support. Record
  this and check it: `cargo tree -e normal` on a release build should show
  nothing from them in the final binary except erased stubs.
- `Cargo.lock` is committed (already the case) and `--locked` is used
  everywhere.

### 0.8 Spec review log (S)

The spec is the trust anchor: a proof only shows code matches the spec, and a
human has to check that the spec matches the standard. Make that review a
recorded artifact.

- `docs/spec-reviews.toml` holds, per spec file: reviewer, date, the standard's
  commit reviewed against, and the SHA-256 of the spec file at review time.
- `xtask report` marks a spec file **stale** if its current hash differs,
  and **missing** if it was never reviewed. Stale or missing reviews do not
  fail `verify` (otherwise AI agents couldn't edit specs at all), but they
  are always visible, and they block raising a crate's declared tier.
- Reviews are done by humans only. `CLAUDE.md` forbids agents from writing
  review entries.

### 0.9 `CLAUDE.md` additions (S)

- Rule: never write or edit `spec-reviews.toml`.
- Rule: raising a crate's `tier` requires the report showing all its proofs
  pass, no surviving mutations, and up-to-date spec reviews.
- How to write a Verus spec in this repo: the transcription conventions
  used in `utf8/spec.rs` (queue modelling, step-number comments, modelling
  choices written down at the top of the file).
- Errata process: record in `docs/ERRATA.md`, specify the evident intent,
  and never report upstream without a human's go-ahead.

### 0.10 Miri (S)

- `verify` runs `cargo +<pinned-nightly> miri test --workspace`.
- There is no exec code yet, so this is plumbing. It must be in place before
  the first exec code lands, so that the first unsound line ever written is
  caught.

### 0.11 Linux parity (M)

Without CI, Linux support has to be checkable locally.

- A `Dockerfile` (Linux x86-64) that runs `scripts/setup.sh` then
  `scripts/verify.sh`. This doubles as the "recheck every proof yourself"
  command for anyone reading the Show HN post:
  `docker build -t clazel-verify . && docker run --rm clazel-verify`.
- On Apple Silicon this runs under emulation and will be slow; that's fine
  for an occasional parity check.
- Fix whatever breaks: BSD vs GNU `sed`, `mktemp` and `grep` differences in
  scripts. Moving checks into `xtask` (0.4) removes most of them.

### 0.12 Clean up Verus output noise (S)

Verus warns about missing docs on accessor methods it generates for enums
(`is_Byte` and similar). Real warnings get lost among them. `missing_docs`
is already enforced by the normal clippy build, so the Verus run passes
`-A missing_docs` after `--` (Verus arguments only). This doesn't weaken
anything.

## Order of work

```
0.1 toolchain pin ─┬─> 0.2 setup.sh ──────────────> 0.11 Linux/Docker
                   └─> 0.12 noise
0.3 tiers ──> 0.4 xtask ─┬─> 0.5 metrics/README ─┐
                         ├─> 0.6 mutation tests ─┼─> exit criteria
                         ├─> 0.7 dep allowlist ──┤
                         └─> 0.8 spec reviews ───┘
0.9 CLAUDE.md (after 0.3, 0.8)        0.10 Miri (after 0.1)
```

0.1, 0.3, 0.4, 0.6 and 0.12 are done. Next: 0.5, 0.7, 0.8 and 0.2.

## Explicitly out of scope for Phase 0

- **GitHub Actions:** deferred by decision. Once `xtask` exists, CI is a
  short workflow that runs the Docker image.
- **The audited `sys` crate** for `unsafe` OS calls. It is created when the
  first OS call is needed (Phase 2 process sandbox). Until then the
  workspace has zero `unsafe`.
- **Test-suite vendoring (WPT, html5lib-tests):** done per phase, when a
  phase needs a suite, with its license and pinned upstream commit.
- **Reporting the Encoding "peek" erratum upstream:** a human decision.
