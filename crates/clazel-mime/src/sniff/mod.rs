//! MIME type sniffing (MIME Sniffing §5–§7).
//!
//! - [`spec`]: a step-by-step transcription of the standard, with its
//!   pattern tables.
//! - [`contract`]: what the executable functions are proven to satisfy.
//! - [`pattern`], [`tables`], [`signatures`], [`algorithms`]: the
//!   executable code (§6 pattern matching, the tables, the MP4/WebM/MP3
//!   signatures, §5.1, §7, §7.1, §7.2), each proven against [`contract`].
//! - [`lemmas`]: facts proven about the spec itself.
//! - [`independent`]: a second transcription, from the tables' notes and
//!   the file-format specifications, and what it and the spec are proven
//!   to agree on.
//! - [`checks`]: facts about the concrete tables, established by
//!   evaluation.
//! - [`examples`]: WPT's media files, evaluated on the spec.

pub mod algorithms;
pub mod checks;
pub mod contract;
pub mod examples;
pub mod independent;
pub mod lemmas;
pub mod pattern;
pub mod signatures;
pub mod spec;
pub mod tables;
