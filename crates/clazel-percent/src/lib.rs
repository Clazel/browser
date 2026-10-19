//! WHATWG URL Standard §1.3, percent-encoded bytes.
//!
//! Spec: <https://url.spec.whatwg.org/#percent-encoded-bytes> (Living
//! Standard, `url.bs` at commit `845bafca22fb0c5a42c4bf384a9bdea525a2f10d`).
//! Tier: see `[package.metadata.clazel]` in `Cargo.toml` and
//! `docs/VERIFICATION.md`.
//!
//! - [`independent`]: a transcription of RFC 3986's percent-encoding,
//!   written first, before the WHATWG transcription it will be proven
//!   equal to.

pub mod independent;
