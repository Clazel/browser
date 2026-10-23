//! TLS 1.3 record layer and handshake message formats.
//!
//! Spec: RFC 8446 "The Transport Layer Security (TLS) Protocol Version
//! 1.3", August 2018 (<https://www.rfc-editor.org/rfc/rfc8446>).
//! Tier: see `[package.metadata.clazel]` in `Cargo.toml` and
//! `docs/VERIFICATION.md`.
//!
//! - [`spec`]: a step-by-step transcription of the standard.
//! - [`contract`]: what the executable functions are proven to satisfy.

pub mod contract;
pub mod spec;
