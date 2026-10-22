//! The statement that the two transcriptions of the Public Suffix List
//! algorithm agree: [`super::spec`] (URL §3.2 and the algorithm) and
//! [`super::independent`] (the "Formal algorithm" alone). The proof is in
//! [`super::equivalence_proof`].
//!
//! The classes on which they are proven equal:
//! - the rule list is well formed ([`super::wf::rules_wf`]), which the
//!   generated list is (`super::wf_table`);
//! - the domain has no empty label once a trailing dot is set aside (outside
//!   that the standard says the algorithm is undefined, and both return
//!   null, so there they agree trivially).
//!
//! For public suffix and registrable domain the two agree on the result
//! string, including a trailing dot.

#[allow(unused_imports)]
use super::independent::*;
#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// A rule of [`super::spec`] as the independent transcription writes it.
pub open spec fn ind_rule(rule: Rule) -> (Seq<Seq<u32>>, bool) {
    (rule.labels, rule.exception)
}

/// A list of rules as the independent transcription writes it.
pub open spec fn ind_rules(rules: Seq<Rule>) -> Seq<(Seq<Seq<u32>>, bool)> {
    Seq::new(rules.len(), |i: int| ind_rule(rules[i]))
}

/// The two public suffixes agree.
pub open spec fn public_suffix_equivalence(rules: Seq<Rule>, domain: Seq<u32>) -> bool {
    ind_public_suffix(ind_rules(rules), domain) == public_suffix_of_domain(rules, domain)
}

/// The two registrable domains agree.
pub open spec fn registrable_domain_equivalence(rules: Seq<Rule>, domain: Seq<u32>) -> bool {
    ind_registrable_domain(ind_rules(rules), domain) == registrable_domain_of_domain(rules, domain)
}

} // verus!
