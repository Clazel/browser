//! WHATWG Encoding Standard, starting with UTF-8.
//!
//! Spec: <https://encoding.spec.whatwg.org/> (Living Standard, last updated
//! 19 October 2026, commit `dd7943441a861a60a073bffa55869d91cb6a8288`).
//! Tier: 0 today, target 2 (functional correctness proven with Verus); see
//! `[package.metadata.clazel]` in `Cargo.toml` and `docs/VERIFICATION.md`.

pub mod utf8;
