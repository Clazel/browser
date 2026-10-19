//! MIME types (MIME Sniffing §4): the record, parsing, serializing, and the
//! §4.6 groups.
//!
//! - [`spec`]: a step-by-step transcription of the standard (with the Fetch
//!   and Infra definitions it uses).
//! - [`termination`]: why the spec's loops terminate.
//! - [`contract`]: what the executable functions are proven to satisfy.
//! - [`record`]: the executable MIME type and shared string helpers.
//! - [`parse`], [`serialize`], [`groups`]: the executable algorithms, each
//!   proven against [`contract`].
//! - [`lemmas`]: facts proven about the spec itself.

pub mod contract;
pub mod groups;
pub mod lemmas;
pub mod parse;
pub mod record;
pub mod serialize;
pub mod spec;
pub mod termination;
