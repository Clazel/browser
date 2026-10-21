//! The deterministic CBOR profile (RFC 8949 §3 and §4.2.1).
//!
//! - [`spec`]: a step-by-step transcription of the standard. This is the
//!   part a human must check against the standard.
//! - [`contract`]: what the executable codec is proven to satisfy.
//! - [`termination`]: facts Verus needs to accept the spec's `decreases`.

pub mod contract;
pub mod examples;
pub mod lemmas;
pub mod spec;
pub mod termination;
