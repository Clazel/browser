//! Canonicalized host names, domain matching, default-path and path-match
//! (RFC 6265bis §5.1.2 to §5.1.4).
//!
//! - [`spec`]: a step-by-step transcription of the algorithms.
//! - [`contract`]: what the executable functions are proven to satisfy.
//! - [`exec`]: the executable algorithms, each proven against [`contract`].
//! - [`lemmas`]: facts proven about the spec itself.
//! - [`independent`]: a second transcription, from RFC 6265, and the proof
//!   that it agrees with the spec.

pub mod contract;
pub mod exec;
pub mod independent;
pub mod lemmas;
pub mod spec;
