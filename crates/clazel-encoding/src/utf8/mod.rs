//! UTF-8 (Encoding §8.1).
//!
//! - [`spec`]: a step-by-step transcription of the standard. This is the
//!   part a human must check against the standard.
//! - [`contract`]: what the executable decoder and encoder are proven to
//!   satisfy.
//! - [`decode`]: the executable decoder, and its proof.
//! - [`encode`]: the executable encoder, and its proof.
//! - [`lemmas`]: facts proven about the spec itself.
//! - [`independent`]: a second transcription, from the Unicode Standard,
//!   proven equal to [`spec`].

pub mod contract;
pub mod decode;
pub mod encode;
pub mod independent;
pub mod lemmas;
pub mod spec;
