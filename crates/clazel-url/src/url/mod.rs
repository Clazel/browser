//! URLs (URL §4): the URL record (§4.1), the basic URL parser (§4.4) and
//! the URL serializer (§4.5).
//!
//! - [`spec`]: a step-by-step transcription of the standard, one spec
//!   function per parser state.
//! - [`termination`]: why the parser's state machine terminates.
//! - [`contract`]: what the executable functions are proven to satisfy.

pub mod contract;
pub mod spec;
pub mod termination;
