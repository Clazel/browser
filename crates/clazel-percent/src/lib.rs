//! WHATWG URL Standard §1.3, percent-encoded bytes.
//!
//! Spec: <https://url.spec.whatwg.org/#percent-encoded-bytes> (Living
//! Standard, `url.bs` at commit `845bafca22fb0c5a42c4bf384a9bdea525a2f10d`).
//! Tier: see `[package.metadata.clazel]` in `Cargo.toml` and
//! `docs/VERIFICATION.md`.
//!
//! - [`spec`]: a step-by-step transcription of the standard.
//! - [`contract`]: what the executable functions are proven to satisfy.
//! - [`independent`]: a second transcription, from RFC 3986, proven equal
//!   to [`spec`] where the two standards agree.
//!
//! Strings are sequences of scalar values as `u32`, the type
//! `clazel-encoding` decodes to and encodes from.

pub mod contract;
pub mod independent;
pub mod spec;
