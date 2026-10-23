//! The cookie storage model, the retrieval model and "same-site" requests
//! (RFC 6265bis §5.2, §5.7, §5.8).
//!
//! - [`spec`]: a step-by-step transcription of the algorithms, with the two
//!   isolation decisions (cookie root, per-root eviction) at its top.
//! - [`contract`]: what the executable functions are proven to satisfy.
//! - [`exec`]: the executable algorithms, each proven against [`contract`].
//! - [`lemmas`]: facts proven about the spec itself.
//! - [`isolation`]: the isolation lemmas (a store or a retrieval for host `h`
//!   touches only cookies under `h`'s cookie root), proven from
//!   `clazel-psl`'s root lemmas, and the lemmas `mutations.json` certifies
//!   against.
//! - [`examples`]: the spec evaluated on concrete hosts, cookies and jars.
//! - [`independent`]: a second transcription, from RFC 6265 §5.3 and §5.4,
//!   and in [`independent_equivalence`] the proof that it agrees with the
//!   spec on a stated class.
//! - [`certificates`]: the file the kill certificates are added to.

pub mod certificates;
pub mod contract;
pub mod examples;
pub mod exec;
pub mod independent;
pub mod independent_equivalence;
pub mod isolation;
pub mod lemmas;
pub mod spec;
