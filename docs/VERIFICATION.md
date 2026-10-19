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

Each tier includes the ones below it, so a higher number is always a stronger
guarantee. **Testing is not a tier.** Web Platform Tests, fuzzing, and
differential testing against other engines apply at every tier. They catch
mistakes in specs, which proofs cannot, and they are the only evidence for
Tier 0 code.

Every crate declares its tier in `Cargo.toml`:

```toml
[package.metadata.clazel]
tier = 0          # what is proven about the shipped code today
target-tier = 2   # what this policy requires for the crate
```

`tier` is never raised for proofs about a spec alone; it describes the code
that runs. `cargo xtask verify` checks that every crate declares both, that the
declared tier is backed by tooling (Tier 2: Verus enabled for the crate,
since Verus also proves the absence of panics; Tier 1: the crate has Kani
harnesses), and it reports every crate whose `tier` is below its
`target-tier`.

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

Pinned versions (proofs must be reproducible). The source of truth is
`scripts/toolchains.env`; `verify.sh` fails if installed tools differ.

| Tool | Version |
|------|---------|
| Rust | `1.98.1` (stable; the toolchain Verus is built with) |
| Verus | `0.2026.10.04.426d8b0` |
| Kani | `0.68.0` (CBMC 6.11.0) |
| Miri | on `nightly-2026-08-21` (the nightly Kani uses) |

`scripts/setup.sh` installs all of them on macOS (arm64, x86-64) and Linux
(x86-64). It checks every download against `scripts/checksums.txt` and
installs nothing if a checksum differs.

## Trusted computing base (what we do *not* prove)

We list this openly. Proofs are only as good as their assumptions.

- The Rust compiler, LLVM, and the Verus and Kani tools themselves
- The OS kernel and its sandboxing primitives (macOS Seatbelt, Linux seccomp and namespaces)
- Cryptography, which comes from formally verified libraries (libcrux / HACL\*), not our own code
- The contents of `spec` functions. A proof shows the code matches the spec;
  a human must check that the spec matches the WHATWG standard. This is why spec
  functions cite the standard step by step and are kept short. Those human
  checks are recorded, with the file's hash, in
  [SPEC-REVIEWS.md](SPEC-REVIEWS.md). A crate cannot declare any tier above
  0 while one of its spec files is unreviewed or changed since review.

## Proof mutation testing

A proof can pass for the wrong reason, for example because its spec is too weak
to rule anything out. `cargo xtask mutate` (also run by `verify`) applies small,
deliberate bugs to each spec, listed in the crate's `mutations.json`, and checks
the proofs react as recorded: **killed** (a proven theorem is false for the
mutant), **killed incidentally** (only the proof script breaks, so this is not
coverage), or **survives** (a known gap, with what will close it). The report
counts these three separately.

## Honesty metrics

The README's status table is generated, never typed. For each crate it shows
the tier and target tier, the Verus result, Kani harness results, the number of
documented axioms (every other escape hatch is rejected outright), spec / proof /
exec line counts, and the three-way mutation result. `cargo xtask verify` fails
if the committed table differs from what that run measured, and `cargo xtask
report --write` refuses to update it while any check is failing.

Not yet in the table: WPT pass rates (added when a crate first runs a test
suite).
