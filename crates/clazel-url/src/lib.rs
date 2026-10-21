//! WHATWG URL Standard: hosts (§3), URLs (§4: the URL record, the basic
//! URL parser and the URL serializer) and the URL API setters (§6.1).
//!
//! Spec: <https://url.spec.whatwg.org/> (Living Standard, `url.bs` at
//! commit `845bafca22fb0c5a42c4bf384a9bdea525a2f10d`).
//! Tier: see `[package.metadata.clazel]` in `Cargo.toml` and
//! `docs/VERIFICATION.md`.

pub mod api;
pub mod host;
pub mod url;
