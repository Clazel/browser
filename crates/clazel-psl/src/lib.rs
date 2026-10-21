//! The Public Suffix List: "public suffix" and "registrable domain" (URL
//! Standard §3.2), and the cookie root.
//!
//! Tier: see `[package.metadata.clazel]` in `Cargo.toml` and
//! `docs/VERIFICATION.md`.
//!
//! - [`spec`]: the Public Suffix List algorithm and URL §3.2 over any list
//!   of rules, and the cookie root.
//! - [`table`]: the spec view of the generated tables ([`data`]).
//! - [`contract`]: what the executable functions are proven to satisfy.

pub mod contract;
pub mod data;
pub mod spec;
pub mod table;
pub mod tables;
