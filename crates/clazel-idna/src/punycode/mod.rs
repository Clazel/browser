//! RFC 3492 Punycode (<https://www.rfc-editor.org/rfc/rfc3492>): decoding
//! (§6.2) and encoding (§6.3), with the bias adaptation of §6.1 and the
//! overflow handling of §6.4.
//!
//! - [`spec`]: a step-by-step transcription of the RFC.
//! - [`termination`]: why the spec's loops terminate.
//! - [`contract`]: what the executable functions are proven to satisfy.

pub mod contract;
pub mod examples;
pub mod spec;
pub mod termination;
