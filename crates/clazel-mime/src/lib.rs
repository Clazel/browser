//! WHATWG MIME Sniffing Standard: MIME types (§4) and sniffing (§5–§7; spec
//! and contract only so far).
//!
//! Spec: <https://mimesniff.spec.whatwg.org/> (Living Standard, last updated
//! 19 October 2026, commit `ba4b3c385b9765ddfe4a994e2bb89e0ab96068e2`).
//! Tier: 2 (functional correctness proven with Verus) for MIME types; see
//! `[package.metadata.clazel]` in `Cargo.toml` and `docs/VERIFICATION.md`.

pub mod mime_type;
pub mod sniff;
