//! HTTP for the Clazel browser.
//!
//! Spec: RFC 9110 "HTTP Semantics" (June 2022),
//! <https://www.rfc-editor.org/rfc/rfc9110>. Tier: see
//! `[package.metadata.clazel]` in `Cargo.toml` and `docs/VERIFICATION.md`.
//!
//! - [`field`]: field syntax (RFC 9110 §5, §8.6): names, values, lists,
//!   tokens, whitespace, quoted strings, parameters, `Content-Length`,
//!   `Transfer-Encoding` and `Connection`.
//!
//! Message framing (RFC 9112) and the conformance tests are Phase 3 items
//! 3.2 and 3.3 and do not exist yet.

pub mod field;
