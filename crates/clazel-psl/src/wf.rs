//! Well-formedness of a Public Suffix List, as the independent
//! transcription ([`super::independent`]) needs it, and the proof that the
//! generated tables meet it.
//!
//! The standard leaves some choices open (it does not say which of two
//! matching exception rules prevails, and says nothing of a rule with no
//! labels or an exception rule with one). [`super::spec`] fixes a choice
//! for each, so that every function is total; the independent transcription
//! does not. They agree exactly on lists where those choices never arise,
//! which is [`rules_wf`]. The generator (`xtask/src/psl.rs`) rejects any
//! list that is not well formed; [`super::wf_table`] proves it again, inside
//! Verus, for the tables it generated, so no proof rests on the generator's
//! check.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// A list in which the standard's open choices never arise:
/// - every rule has at least one label;
/// - an exception rule has at least two labels ("removing the leftmost
///   label" leaves one) and no `*` label;
/// - no exception rule is a label suffix of another exception rule, so that
///   no domain has two matching exception rules.
pub open spec fn rules_wf(rules: Seq<Rule>) -> bool {
    &&& forall|i: int| 0 <= i < rules.len() ==> (#[trigger] rules[i]).labels.len() >= 1
    &&& forall|i: int|
        0 <= i < rules.len() && (#[trigger] rules[i]).exception ==> rules[i].labels.len() >= 2 && forall|x: int|
            0 <= x < rules[i].labels.len() ==> (#[trigger] rules[i].labels[x]) != star_label()
    &&& forall|i: int, j: int|
        0 <= i < rules.len() && 0 <= j < rules.len() && i != j && (#[trigger] rules[i]).exception && (#[trigger] rules[j]).exception
            ==> !(rules[i].labels.len() <= rules[j].labels.len() && rules[i].labels
            == rules[j].labels.skip((rules[j].labels.len() - rules[i].labels.len()) as int))
}

} // verus!
