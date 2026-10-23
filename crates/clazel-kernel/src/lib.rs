//! The browser kernel (phase-2.md items 2.10 to 2.12): a pure step function
//! `step(State, Event) -> (State, Seq<Output>)` through which every byte a
//! renderer sends passes, and the isolation theorems about it.
//!
//! Tier: see `[package.metadata.clazel]` in `Cargo.toml` and
//! `docs/VERIFICATION.md`.
//!
//! - [`spec`]: state, events, outputs and `step` (item 2.10).
//! - [`invariant`]: `kernel_wf`, the reachable-state invariant, and the
//!   facts proven about it.
//! - [`domain`]: domains, observations and the intransitive purge that
//!   item 2.11's noninterference theorem is stated with.
//! - [`contract`]: what the executable `step` (item 2.12) must satisfy.

pub mod contract;
pub mod domain;
pub mod independent;
pub mod invariant;
pub mod spec;
