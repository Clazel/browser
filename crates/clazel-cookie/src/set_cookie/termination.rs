//! Termination of the recursive loops in [`super::spec`]. Verus needs these
//! facts to accept the spec's `decreases` clause (it names a `via`
//! function in `spec.rs`, which only calls these); they say nothing else
//! about the spec.

#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// A search for an octet never moves backwards (when it starts within the
/// string), and never moves past the end.
pub proof fn lemma_find_octet_bounds(s: Seq<u8>, c: u8, from: nat)
    ensures
        from <= s.len() ==> from <= crate::ascii::find_octet(s, c, from) <= s.len(),
        crate::ascii::find_octet(s, c, from) <= if from <= s.len() { s.len() } else { from },
    decreases s.len() - from
{
    if from < s.len() && s[from as int] != c {
        lemma_find_octet_bounds(s, c, from + 1);
    }
}

} // verus!
