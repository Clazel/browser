//! MIME types (MIME Sniffing §4): the record, parsing, serializing, and the
//! §4.6 groups.
//!
//! - [`spec`]: a step-by-step transcription of the standard (with the Fetch
//!   and Infra definitions it uses).
//! - [`termination`]: why the spec's loops terminate.
//! - [`contract`]: what the executable functions are proven to satisfy.

pub mod contract;
pub mod spec;
pub mod termination;
