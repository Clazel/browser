//! The URL API setters (URL §6.1), as functions on the URL record.
//!
//! - [`spec`]: a step-by-step transcription of the ten setters.
//! - [`contract`]: what the executable setters are proven to satisfy.
//! - [`setters`]: the executable setters, on the exec URL record.
//! - [`examples`]: WPT's and the standard's examples, evaluated.
//! - [`independent`]: a second transcription, from RFC 3986's component
//!   grammar, and the classes on which each setter is proven to agree.
//! - [`lemmas`]: facts proven about the setters (totality with a state
//!   override, §4.1's invariants, idempotence).

pub mod contract;
pub mod examples;
pub mod independent;
pub mod lemmas;
pub mod setters;
pub mod spec;
