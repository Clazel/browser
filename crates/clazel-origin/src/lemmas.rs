//! Facts proven about the spec: same origin is an equivalence on tuple
//! origins, and same origin implies same site and schemelessly same site.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Same origin is reflexive on tuple origins.
pub proof fn lemma_same_origin_reflexive(a: Origin)
    requires
        a is Tuple,
    ensures
        same_origin(a, a),
{
}

/// Same origin is symmetric.
pub proof fn lemma_same_origin_symmetric(a: Origin, b: Origin)
    requires
        same_origin(a, b),
    ensures
        same_origin(b, a),
{
}

/// Same origin is transitive.
pub proof fn lemma_same_origin_transitive(a: Origin, b: Origin, c: Origin)
    requires
        same_origin(a, b),
        same_origin(b, c),
    ensures
        same_origin(a, c),
{
}

/// Same origin implies same site, for every Public Suffix List.
pub proof fn lemma_same_origin_implies_same_site(rules: Seq<clazel_psl::spec::Rule>, a: Origin, b: Origin)
    requires
        same_origin(a, b),
    ensures
        same_site(rules, a, b),
{
}

/// Same origin implies schemelessly same site.
pub proof fn lemma_same_origin_implies_schemelessly_same_site(rules: Seq<clazel_psl::spec::Rule>, a: Origin, b: Origin)
    requires
        same_origin(a, b),
    ensures
        schemelessly_same_site(rules, a, b),
{
    match (a, b) {
        (Origin::Tuple { host: host_a, .. }, Origin::Tuple { host: host_b, .. }) => {
            assert(host_a == host_b);
        },
        _ => {},
    }
}

} // verus!
