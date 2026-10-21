//! Facts proven about the spec. The first group is what the executable
//! functions rely on (the prevailing rule matches; a suffix equals the
//! domain only when it has all its labels); the others are evidence that
//! the spec says what the standard means.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The rule that prevails among the first `n` matches the domain.
pub proof fn lemma_prevailing_matches(rules: Seq<Rule>, d: Seq<Seq<u32>>, n: nat)
    requires
        n <= rules.len(),
    ensures
        match prevailing_from(rules, d, n) {
            Some(p) => p < n && rule_matches(rules[p as int], d),
            None => true,
        },
    decreases n,
{
    if n > 0 {
        lemma_prevailing_matches(rules, d, (n - 1) as nat);
    }
}

/// The public suffix has at least one label, and at most the domain's.
pub proof fn lemma_suffix_label_count_bounds(rules: Seq<Rule>, d: Seq<Seq<u32>>)
    requires
        d.len() >= 1,
    ensures
        1 <= suffix_label_count(rules, d) <= d.len(),
{
    lemma_prevailing_matches(rules, d, rules.len());
}

/// A domain is its labels joined, with its trailing dot: the labels are a
/// non-empty list without ".".
pub proof fn lemma_domain_labels_join(domain: Seq<u32>)
    ensures
        domain_labels(domain).len() >= 1,
        forall|k: int| 0 <= k < domain_labels(domain).len() ==> clazel_url::host::lemmas::free_of(#[trigger] domain_labels(domain)[k], 0x2E),
        labels_string(domain_labels(domain), has_trailing_dot(domain)) == domain,
{
    super::join::lemma_split_join_round_trip(strip_trailing_dot(domain));
    if has_trailing_dot(domain) {
        assert(domain =~= strip_trailing_dot(domain) + seq![0x2Eu32]);
    }
}

/// A suffix of a domain with `k` of its labels is the domain itself
/// exactly when `k` is all of them.
pub proof fn lemma_label_suffix_is_domain(domain: Seq<u32>, k: nat)
    requires
        1 <= k <= domain_labels(domain).len(),
    ensures
        (label_suffix(domain_labels(domain), has_trailing_dot(domain), k) == domain) <==> (k == domain_labels(domain).len()),
{
    let d = domain_labels(domain);
    let td = has_trailing_dot(domain);
    lemma_domain_labels_join(domain);
    let tail = if td {
        seq![0x2Eu32]
    } else {
        seq![]
    };
    let a = d.skip(d.len() - k);
    if k == d.len() {
        assert(a =~= d);
    } else {
        if label_suffix(d, td, k) == domain {
            let x = clazel_url::host::lemmas::split_join(a, 0x2E);
            let y = clazel_url::host::lemmas::split_join(d, 0x2E);
            assert(x + tail == y + tail);
            assert(x.len() == y.len());
            assert forall|i: int| 0 <= i < x.len() implies x[i] == y[i] by {
                assert((x + tail)[i] == (y + tail)[i]);
            }
            assert(x =~= y);
            assert forall|j: int| 0 <= j < a.len() implies clazel_url::host::lemmas::free_of(#[trigger] a[j], 0x2E) by {
                assert(a[j] == d[d.len() - k + j]);
            }
            super::join::lemma_join_injective(a, d);
            assert(a.len() == d.len());
        }
    }
}

} // verus!
