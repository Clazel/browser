//! Termination of the recursive loops in [`super::spec`]. Verus needs these
//! facts to accept the spec's `decreases` clauses (each names a `via`
//! function in `spec.rs`, which only calls these); they say nothing else about the spec.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Collecting never moves the position backwards, nor past the end.
pub proof fn lemma_collect_loop_position(condition: Condition, input: Seq<u32>, position: nat, result: Seq<u32>)
    ensures
        collect_loop(condition, input, position, result).1 >= position,
        position <= input.len() ==> collect_loop(condition, input, position, result).1 <= input.len(),
    decreases input.len() - position
{
    if position < input.len() && meets(condition, input[position as int]) {
        lemma_collect_loop_position(condition, input, position + 1, result.push(input[position as int]));
    }
}

/// The quoted-string loop never moves the position backwards, nor past
/// the end.
pub proof fn lemma_quoted_string_loop_position(input: Seq<u32>, position: nat, value: Seq<u32>)
    ensures
        quoted_string_loop(input, position, value).1 >= position,
        position <= input.len() ==> quoted_string_loop(input, position, value).1 <= input.len(),
    decreases input.len() - position
{
    lemma_collect_loop_position(Condition::NotQuotationMarkOrReverseSolidus, input, position, seq![]);
    let (collected, p) = collect(Condition::NotQuotationMarkOrReverseSolidus, input, position);
    if p < input.len() && input[p as int] == 0x5C && p + 1 < input.len() {
        lemma_quoted_string_loop_position(input, p + 2, (value + collected).push(input[(p + 1) as int]));
    }
}

} // verus!
