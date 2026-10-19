# Dependencies

Every third-party crate needs an entry here (see CLAUDE.md rule 7).
Checking the resolved graph against this list automatically is Phase 0
item 0.7; until then this list is maintained by hand.

## Shipped (compiled into the browser)

None yet.

## Proof libraries

| Crate | Version | Used by | Why |
|-------|---------|---------|-----|
| `vstd` | `=0.0.0-2026-10-04-0306` | Tier 2 crates | Verus standard library. Proof-only (`Seq`, `spec fn`s); ghost code is erased from normal builds. Pinned to match the installed Verus release. |

`vstd` pulls in the Verus macro chain: `verus_builtin`, `verus_builtin_macros`,
`verus_syn`, `verus_prettyplease`, `verus_state_machines_macros`, `syn`,
`quote`, `proc-macro2`, `unicode-ident`, `synstructure`, `convert_case`,
`indexmap`, `hashbrown`, `equivalent`.

## Tooling (never shipped)

| Crate | Version | Used by | Why |
|-------|---------|---------|-----|
| `proc-macro2` | `1` (with `span-locations`) | `xtask` | Lexes Rust source into tokens with line numbers, so the checker cannot be fooled by comments or strings and can see inside `verus!` bodies. |
| `serde_json` | `1` | `xtask` | Parses `cargo metadata` output. |

Transitive: `unicode-ident`, `serde_core`, `itoa`, `memchr`, `zmij`.
