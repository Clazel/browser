//! Termination of the recursive loop in [`super::spec`]. Verus needs this
//! fact to accept the spec's `decreases` clause (it names a `via` function
//! in `spec.rs`, which only calls this); it says nothing else about the spec.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// A token that decodes at `pos` takes at least one byte and ends within
/// the input, so the position advances and the loop's measure
/// `b.len() - pos` decreases.
pub proof fn lemma_decode_token_progress(b: Seq<u8>, pos: nat)
    ensures
        match decode_token(b, pos) {
            Some((_, len)) => len >= 1 && pos + len <= b.len(),
            None => true,
        },
{
}

} // verus!
