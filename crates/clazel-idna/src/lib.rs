//! Internationalized domain names: RFC 3492 Punycode, and (to come) UTS #46
//! Unicode IDNA Compatibility Processing, which the URL Standard's domain
//! parser uses.
//!
//! Tier: see `[package.metadata.clazel]` in `Cargo.toml` and
//! `docs/VERIFICATION.md`.

pub mod punycode;
pub mod uts46;
