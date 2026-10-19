# Rules for AI contributors

This codebase is written by AI agents. These rules exist so that nobody has
to trust the agents. Read `docs/VERIFICATION.md` and `docs/ROADMAP.md` first.

## Hard rules
1. **No `unsafe`.** `unsafe_code` is forbidden workspace-wide. Do not add
   `#[allow]` overrides. The only exception is a future audited `sys` crate.
2. **Never weaken workspace lints** in a crate or with inline `#[allow]`.
   If a lint fires, restructure the code (use `get()`, checked arithmetic,
   explicit error types).
3. **Contracts before code.** In a Tier 2 crate, write the `spec fn` and the
   `requires`/`ensures` first and commit them separately, *then* the
   implementation and proof. The spec is the part humans review.
4. **No proof escape hatches.** `assume`, `admit`, `#[verifier::external_body]`
   and `#[verifier::exec_allows_no_decreases_clause]` are banned. A genuinely
   needed axiom goes in a crate's `axioms.rs` with a comment that justifies it,
   and is counted by `scripts/verify.sh`.
5. **Cite the spec.** Every function implementing a standard links to the
   exact algorithm and quotes the step numbers it covers, e.g.
   `// URL §4.4 basic URL parser, step 3.2`.
6. **Never mark something verified that isn't.** If a proof doesn't go through,
   say so in the PR and leave the crate at its real tier.
7. **Write our own parsers.** Any code that parses untrusted bytes is ours.
   Dependencies are allowed only for crypto (verified libraries), OS and windowing
   bindings, and GPU access, and each needs a line in `docs/DEPENDENCIES.md`.

## Workflow
- Run `scripts/verify.sh` before calling any work done. Report its output honestly.
- Keep changes small: one spec section or one proof per commit where practical.
- Test against official suites (WPT, html5lib-tests), vendored under `tests/`.
