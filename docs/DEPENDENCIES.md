# Dependencies

Every third-party crate needs an entry here (see CLAUDE.md rule 7).

| Crate | Version | Used by | Why |
|-------|---------|---------|-----|
| `vstd` | `=0.0.0-2026-10-04-0306` | Tier 2 crates | Verus standard library. Proof-only (`Seq`, `spec fn`s); ghost code is erased from normal builds. Pinned to match the installed Verus release. |
