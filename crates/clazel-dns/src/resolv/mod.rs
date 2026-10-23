//! The `nameserver` lines of `/etc/resolv.conf`.
//!
//! - [`spec`]: the grammar (ours: no standard defines the file) as spec
//!   functions.
//! - [`termination`]: why the grammar's loop terminates.
//! - [`contract`]: what the executable parser is proven to satisfy.

pub mod contract;
pub mod spec;
pub mod termination;
