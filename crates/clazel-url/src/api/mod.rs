//! The URL API setters (URL §6.1), as functions on the URL record.
//!
//! - [`spec`]: a step-by-step transcription of the ten setters.
//! - [`contract`]: what the executable setters are proven to satisfy.
//! - [`setters`]: the executable setters, on the exec URL record.

pub mod contract;
pub mod setters;
pub mod spec;
