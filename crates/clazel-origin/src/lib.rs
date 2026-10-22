//! Origins and sites (HTML Standard §7.1.1) and the origin of a URL (URL
//! Standard §4.7).
//!
//! Tier: see `[package.metadata.clazel]` in `Cargo.toml` and
//! `docs/VERIFICATION.md`.
//!
//! - [`spec`]: the standards' algorithms, over abstract origins, hosts and
//!   URLs.
//! - [`contract`]: what the executable functions are proven to satisfy.
//! - [`examples`]: the spec evaluated on concrete origins, sites and URLs.
//! - [`exec`]: the executable origin and site types and functions.
//! - [`lemmas`]: facts proven about the spec.

pub mod contract;
pub mod examples;
pub mod exec;
pub mod lemmas;
pub mod spec;
