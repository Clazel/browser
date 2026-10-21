//! Cookie dates (RFC 6265bis §5.1.1).
//!
//! - [`spec`]: a step-by-step transcription of the algorithm.
//! - [`contract`]: what the executable functions are proven to satisfy.
//! - [`exec`]: the executable parser, proven against [`contract`].
//! - [`lemmas`]: facts proven about the spec itself.
//! - [`examples`]: standards' examples, evaluated on the spec.

pub mod contract;
pub mod examples;
pub mod exec;
pub mod lemmas;
pub mod spec;
