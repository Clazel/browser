//! WHATWG Infra Standard §7 "Forgiving base64": forgiving-base64 decode
//! and forgiving-base64 encode.
//!
//! Spec: <https://infra.spec.whatwg.org/#forgiving-base64> (Living
//! Standard, commit `459b7829230ad256a690dabd315db974469af8e7`, 19 October
//! 2026), and RFC 4648 §4, which "forgiving-base64 encode" applies.
//! Tier: see `[package.metadata.clazel]` in `Cargo.toml` and
//! `docs/VERIFICATION.md`.
//!
//! - [`spec`]: a step-by-step transcription of the standard.
//! - [`contract`]: what the executable decoder and encoder are proven to
//!   satisfy.

pub mod contract;
pub mod spec;
