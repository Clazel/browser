//! Termination of the recursive loops in [`super::spec`]. Verus needs these
//! facts to accept the spec's `decreases` clauses (each names a `via`
//! function in `spec.rs`, which only calls these); they say nothing else
//! about the spec.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// A collected token never runs past the end of the input.
pub proof fn lemma_collect_not_equal_len(input: Seq<u32>, delimiter: u32, position: nat)
    ensures
        position <= input.len() ==> position + collect_not_equal(input, delimiter, position).len() <= input.len(),
    decreases input.len() - position
{
    if position < input.len() && input[position as int] != delimiter {
        lemma_collect_not_equal_len(input, delimiter, position + 1);
    }
}

} // verus!
