//! The file `mutations.json`'s kill certificates for the storage and
//! retrieval spec are added to when they are checked (`xtask/src/mutate.rs`).
//! It holds nothing itself: a certificate has to live in a module whose own
//! proofs (and the `compute_only` examples of `examples.rs`) a mutant does
//! not break, because Verus evaluates every `compute_only` assertion of the
//! module it is asked about before it looks at the certificate.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;
