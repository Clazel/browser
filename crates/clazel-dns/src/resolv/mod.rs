//! The `nameserver` lines of `/etc/resolv.conf`.
//!
//! - [`spec`]: the grammar (ours: no standard defines the file) as spec
//!   functions.
//! - [`termination`]: why the grammar's loop terminates.
//! - [`contract`]: what the executable parser is proven to satisfy.
//! - [`parse`]: the executable parser, and [`lemmas`], facts it needs.

pub mod contract;
pub mod examples;
pub mod lemmas;
pub mod parse;
pub mod spec;
pub mod termination;
