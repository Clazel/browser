//! Frames: a 4-byte big-endian length and exactly one CBOR item.
//!
//! - [`spec`]: the definition.
//! - [`contract`]: what the executable code is proven to satisfy.

pub mod contract;
pub mod spec;
pub mod lemmas;
pub mod codec;
pub mod examples;
