# Verification policy

This browser is written by AI. We do not ask anyone to trust that code.
Instead, every component carries a machine-checked guarantee, and the strength
of that guarantee is stated, not implied.

Humans review **specifications and contracts** (small). Machines check
**implementations** (large).

## Tiers

| Tier | Guarantee | How it is checked |
|------|-----------|-------------------|
| 0 | Memory safe, no undefined behaviour | Safe Rust (`unsafe_code = "forbid"`), Miri on tests, workspace clippy deny-lints |
| 1 | Never panics, overflows or indexes out of bounds, on **any** input | Kani bounded model checking harnesses over all inputs up to a stated bound |
| 2 | Functionally correct: the implementation refines an executable spec | Verus proofs (SMT-backed, unbounded) |
| 3 | Empirically tested | Web Platform Tests, fuzzing, differential testing against other engines |

Every crate declares its tier in its `Cargo.toml` `description` and in the
crate-level doc comment. Machine-readable tiers, enforced by `verify.sh`, are
planned (Phase 0 item 0.3) but not implemented yet.

## What must be at which tier

- **Tier 2 required:** the browser kernel (origin isolation, cookie and storage
  policy, permission checks), the IPC message codec, and the parsers for URL,
  HTTP/1.1 framing, encodings, percent-encoding, base64, MIME sniffing, and the HTML
  tokenizer state machine.
- **Tier 1 minimum:** every other parser of untrusted bytes: CSS, image
  decoders, font tables, JS lexer and parser.
- **Tier 0 minimum:** everything else (layout, paint, JS interpreter, UI).

## Tools

- **Verus**: functional-correctness proofs written in Rust syntax inside
  `verus! { ... }`. Chosen over Lean/F*/Coq extraction because the proof and the
  shipped code are the same artifact, so no extraction step can go wrong.
- **Kani**: bit-precise bounded model checking of ordinary Rust. Used for
  panic-freedom and for cross-checking Verus specs on small inputs.
- **Miri**: catches UB in the one audited `unsafe` crate, and in dependencies.

Pinned versions (proofs must be reproducible):

| Tool | Version | Install |
|------|---------|---------|
| Verus | `0.2026.10.04.426d8b0` (needs Rust `1.98.1`) | GitHub release zip, `verus` on `PATH` |
| Kani | `0.68.0` (CBMC 6.11.0) | `cargo install --locked kani-verifier --version 0.68.0 && cargo kani setup` |

## Trusted computing base (what we do *not* prove)

We list this openly. Proofs are only as good as their assumptions.

- The Rust compiler, LLVM, and the Verus and Kani tools themselves
- The OS kernel and its sandboxing primitives (macOS Seatbelt, Linux seccomp and namespaces)
- Cryptography, which comes from formally verified libraries (libcrux / HACL\*), not our own code
- The contents of `spec` functions. A proof shows the code matches the spec;
  a human must check that the spec matches the WHATWG standard. This is why spec
  functions cite the standard step by step and are kept short.

## Honesty metrics

`scripts/verify.sh` reports, per crate: tier, number of proven functions,
`assume`/`admit`/`external_body` count (target: zero outside documented
axioms), and WPT pass rate where applicable. These numbers go in the README.
