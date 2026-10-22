//! The cookie storage model, the retrieval model and "same-site" requests
//! (RFC 6265bis §5.2, §5.7, §5.8).
//!
//! - [`spec`]: a step-by-step transcription of the algorithms, with the two
//!   isolation decisions (cookie root, per-root eviction) at its top.
//! - [`contract`]: what the executable functions will be proven to satisfy.
//! - [`lemmas`]: facts proven about the spec itself.
//!
//! Item 2.9 so far is the spec and the contracts: there is no `exec` yet.

pub mod contract;
pub mod independent;
pub mod isolation;
pub mod lemmas;
pub mod spec;
