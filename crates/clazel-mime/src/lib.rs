//! WHATWG MIME Sniffing Standard: MIME types (§4), and later sniffing (§7).
//!
//! Spec: <https://mimesniff.spec.whatwg.org/> (Living Standard, last updated
//! 19 October 2026, commit `ba4b3c385b9765ddfe4a994e2bb89e0ab96068e2`).
//! Tier: 0 today, target 2 (functional correctness proven with Verus); see
//! `[package.metadata.clazel]` in `Cargo.toml` and `docs/VERIFICATION.md`.

pub mod mime_type;
