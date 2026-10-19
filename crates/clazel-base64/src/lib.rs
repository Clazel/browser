//! WHATWG Infra Standard §7 "Forgiving base64": forgiving-base64 decode
//! and forgiving-base64 encode.
//!
//! Spec: <https://infra.spec.whatwg.org/#forgiving-base64> (Living
//! Standard, commit `459b7829230ad256a690dabd315db974469af8e7`, 19 October
//! 2026), and RFC 4648 §4, which "forgiving-base64 encode" applies.
//! Tier: see `[package.metadata.clazel]` in `Cargo.toml` and
//! `docs/VERIFICATION.md`.
//!
//! - [`spec`]: a step-by-step transcription of the standard. This is the
//!   part a human must check against the standard.
//! - [`contract`]: what the executable decoder and encoder are proven to
//!   satisfy.
//! - [`decode`] and [`encode`]: the executable code, and its proofs.
//! - [`lemmas`]: facts proven about the spec itself.
//! - [`independent`]: a second transcription, from RFC 4648, proven equal
//!   to [`spec`] on canonical input.

pub mod contract;
pub mod decode;
pub mod encode;
pub mod independent;
pub mod lemmas;
pub mod spec;
