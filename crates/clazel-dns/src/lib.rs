//! DNS message format, formally verified with Verus.
//!
//! Spec: RFC 1035 "Domain Names - Implementation and Specification"
//! (November 1987, <https://www.rfc-editor.org/rfc/rfc1035>) §2.3, §3, §4;
//! RFC 1034 §3.6.2 and §5.3.3; RFC 3596 (AAAA); RFC 5452 §4 to §6 for
//! accepting a reply. Tier: see `[package.metadata.clazel]` in `Cargo.toml`
//! and `docs/VERIFICATION.md`.
//!
//! - [`spec`]: a transcription of the standards, as spec functions.
//! - [`contract`]: what the executable functions are proven to satisfy.
//! - [`resolv`]: the `nameserver` lines of `/etc/resolv.conf` (a grammar of
//!   our own).

pub mod answer;
pub mod contract;
pub mod decode;
pub mod encode;
pub mod examples;
pub mod lemmas;
pub mod resolv;
pub mod spec;
pub mod types;
