//! RFC 3492 Punycode (<https://www.rfc-editor.org/rfc/rfc3492>): decoding
//! (§6.2) and encoding (§6.3), with the bias adaptation of §6.1 and the
//! overflow handling of §6.4.
//!
//! - [`spec`]: a step-by-step transcription of the RFC.
//! - [`termination`]: why the spec's loops terminate.
//! - [`contract`]: what the executable functions are proven to satisfy.
//! - [`decode`], [`encode`] and [`shared`]: the executable code, and its
//!   proofs.
//! - [`lemmas`] and [`round_trip`]: facts proven about the spec itself,
//!   including that decoding inverts encoding; [`examples`]: the
//!   RFC's samples, evaluated.

pub mod contract;
pub mod decode;
pub mod encode;
pub mod examples;
pub mod lemmas;
pub mod round_trip;
pub mod shared;
pub mod spec;
pub mod termination;
