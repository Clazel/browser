//! HTTP field syntax (RFC 9110 §5 and §8.6).
//!
//! - [`spec`]: a transcription of the RFC.
//! - [`termination`]: why the spec's recursive functions terminate.
//! - [`contract`]: what the executable functions are proven to satisfy.

pub mod content_length;
pub mod contract;
pub mod examples;
pub mod lemmas;
pub mod list;
pub mod params;
pub mod quoted;
pub mod section;
pub mod spec;
pub mod string;
pub mod termination;
#[cfg(test)]
mod tests;
pub mod types;
