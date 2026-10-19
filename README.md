# browser (working name)

A web browser built from the bottom up by AI, using formal verification
instead of trust.

- **Memory safe:** 100% safe Rust. `unsafe` is forbidden workspace-wide.
- **Verified where it matters:** the kernel's security policy and every parser
  of untrusted input carry machine-checked proofs (Verus, Kani).
- **Honest about it:** each crate declares its verification tier, and the
  trusted computing base is listed in [docs/VERIFICATION.md](docs/VERIFICATION.md).

Status: Phase 0 (foundations). See [docs/ROADMAP.md](docs/ROADMAP.md).

## Verification status

| Crate | Tier (target) | Tier (actual) | Proven fns | Axioms | WPT |
|-------|---------------|---------------|------------|--------|-----|
| encoding | 2 | n/a | 0 | 0 | n/a |

## Building

```sh
scripts/verify.sh
```
