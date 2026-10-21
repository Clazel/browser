//! IPC wire format between the kernel and renderers: a deterministic CBOR
//! profile, frames and the message schema.
//!
//! Spec: RFC 8949 "Concise Binary Object Representation (CBOR)", December
//! 2020 (STD 94), §3 and §4.2.1 (<https://www.rfc-editor.org/rfc/rfc8949>).
//! Tier: see `[package.metadata.clazel]` in `Cargo.toml` and
//! `docs/VERIFICATION.md`.
//!
//! - [`cbor`]: the CBOR profile (phase-2.md items 2.1 and 2.2).

pub mod cbor;
