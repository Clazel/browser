//! Multiple-precision arithmetic over little-endian `u64` limbs.
//!
//! - [`spec`]: `value`, the `nat` a limb sequence denotes.
//! - [`contract`]: what the arithmetic is proven to satisfy.

pub mod contract;
pub mod spec;
