//! Set-Cookie parsing, name prefixes and the lifetime limit (RFC 6265bis
//! §5.4 to §5.6).
//!
//! - [`spec`]: a step-by-step transcription of the algorithms.
//! - [`termination`]: why the spec's loop terminates.
//! - [`contract`]: what the executable functions are proven to satisfy.

pub mod contract;
pub mod spec;
pub mod termination;
