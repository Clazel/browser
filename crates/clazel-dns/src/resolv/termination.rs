//! Termination of the recursive loop in [`super::spec`]. Verus needs this
//! fact to accept the spec's `decreases` clause (it names a `via` function
//! in `spec.rs`, which only calls this); it says nothing else about the spec.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// A line ends at or after where it starts, and within the file, so the
/// loop's position `line_end + 1` is past `pos` and the measure
/// `s.len() - pos` decreases.
pub proof fn lemma_line_end_progress(s: Seq<u8>, i: nat)
    ensures
        i <= line_end(s, i),
        i <= s.len() ==> line_end(s, i) <= s.len(),
    decreases s.len() - i,
{
    if i < s.len() && s[i as int] != 10 {
        lemma_line_end_progress(s, i + 1);
    }
}

} // verus!
