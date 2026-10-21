//! Canonicalized host names, domain matching, default-path and path-match
//! (RFC 6265bis §5.1.2 to §5.1.4).
//!
//! - [`spec`]: a step-by-step transcription of the algorithms.
//! - [`contract`]: what the executable functions are proven to satisfy.
//! - [`exec`]: the executable algorithms, each proven against [`contract`].
//! - [`lemmas`]: facts proven about the spec itself.

pub mod contract;
pub mod exec;
pub mod lemmas;
pub mod spec;
