//! Set-Cookie parsing, name prefixes and the lifetime limit (RFC 6265bis
//! §5.4 to §5.6).
//!
//! - [`spec`]: a step-by-step transcription of the algorithms.
//! - [`termination`]: why the spec's loop terminates.
//! - [`contract`]: what the executable functions are proven to satisfy.
//! - [`exec`]: the executable algorithms, each proven against [`contract`].
//! - [`lemmas`]: facts proven about the spec itself.
//! - [`independent`]: a second transcription, from the server-side grammar
//!   of §4.1.1, and the proof that the spec reads that grammar as it does.

pub mod contract;
pub mod exec;
pub mod independent;
pub mod lemmas;
pub mod spec;
pub mod termination;
