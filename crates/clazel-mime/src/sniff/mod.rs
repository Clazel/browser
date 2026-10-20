//! MIME type sniffing (MIME Sniffing §5–§7).
//!
//! - [`spec`]: a step-by-step transcription of the standard, with its
//!   pattern tables.
//! - [`contract`]: what the executable functions will be proven to satisfy.
//!
//! Status: spec and contract only; no executable code yet.

pub mod contract;
pub mod spec;
pub mod pattern;
pub mod tables;
