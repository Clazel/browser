# Clazel

A web browser built from the bottom up by AI, using formal verification
instead of trust.

- **Memory safe:** 100% safe Rust. `unsafe` is forbidden workspace-wide.
- **Verified where it matters:** the kernel's security policy and every parser
  of untrusted input carry machine-checked proofs (Verus, Kani).
- **Honest about it:** each crate declares its verification tier, and the
  trusted computing base is listed in [docs/VERIFICATION.md](docs/VERIFICATION.md).

Status: Phase 1 (verified primitives). The UTF-8 decoder spec and contracts are proven; the implementation is next. See [docs/ROADMAP.md](docs/ROADMAP.md).

## Verification status

| Crate | Tier (target) | Tier (actual) | Proven fns | Axioms | WPT |
|-------|---------------|---------------|------------|--------|-----|
| clazel-encoding | 2 | 0 (spec proven, no implementation yet) | 16 | 0 | n/a |

Formalizing the standards has already found one spec bug: see
[docs/ERRATA.md](docs/ERRATA.md).

## Building

```sh
scripts/verify.sh
```

## License

MIT. See [LICENSE](LICENSE).
