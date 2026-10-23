//! HTTP field syntax (RFC 9110 §5 and §8.6).
//!
//! - [`spec`]: a transcription of the RFC.
//! - [`termination`]: why the spec's recursive functions terminate.
//! - [`contract`]: what the executable functions are proven to satisfy.

pub mod contract;
pub mod spec;
pub mod termination;
