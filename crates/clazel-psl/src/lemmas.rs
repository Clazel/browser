//! Facts proven about the spec. The first group is what the executable
//! functions rely on (the prevailing rule matches; a suffix equals the
//! domain only when it has all its labels); the others are evidence that
//! the spec says what the standard means.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// [`rule_matches_from`] is "for every pair" of the rule's labels from the
/// `k`-th from the right.
pub proof fn lemma_rule_matches_from_forall(rule: Rule, d: Seq<Seq<u32>>, k: nat)
    requires
        rule.labels.len() <= d.len(),
    ensures
        rule_matches_from(rule, d, k) <==> forall|j: int|
            k <= j < rule.labels.len() ==> label_matches(#[trigger] rule.labels[rule.labels.len() - 1 - j], d[d.len() - 1 - j]),
    decreases rule.labels.len() - k,
{
    if k < rule.labels.len() {
        lemma_rule_matches_from_forall(rule, d, k + 1);
        if rule_matches_from(rule, d, k) {
            assert forall|j: int| k <= j < rule.labels.len() implies label_matches(#[trigger] rule.labels[rule.labels.len() - 1 - j], d[d.len() - 1 - j]) by {
                if j > k {
                    assert(k + 1 <= j);
                }
            }
        }
    }
}

/// "A domain is said to match a rule" exactly as the standard words it: the
/// domain has as many or more labels, and for every pair, counting from the
/// right, the labels are identical or the rule's is "*".
pub proof fn lemma_rule_matches_forall(rule: Rule, d: Seq<Seq<u32>>)
    ensures
        rule_matches(rule, d) <==> (rule.labels.len() <= d.len() && forall|k: int|
            0 <= k < rule.labels.len() ==> label_matches(#[trigger] rule.labels[rule.labels.len() - 1 - k], d[d.len() - 1 - k])),
{
    if rule.labels.len() <= d.len() {
        lemma_rule_matches_from_forall(rule, d, 0);
    }
}

/// [`has_empty_label_from`] is "some label from the `k`-th on is empty".
pub proof fn lemma_has_empty_label_from_exists(labels: Seq<Seq<u32>>, k: nat)
    ensures
        has_empty_label_from(labels, k) <==> exists|j: int| k <= j < labels.len() && (#[trigger] labels[j]).len() == 0,
    decreases labels.len() - k,
{
    if k < labels.len() {
        lemma_has_empty_label_from_exists(labels, k + 1);
        if labels[k as int].len() != 0 && has_empty_label_from(labels, k) {
            let j = choose|j: int| k + 1 <= j < labels.len() && (#[trigger] labels[j]).len() == 0;
            assert(k <= j);
        }
    }
}

/// An empty label somewhere in `labels`.
pub proof fn lemma_has_empty_label_exists(labels: Seq<Seq<u32>>)
    ensures
        has_empty_label(labels) <==> exists|k: int| 0 <= k < labels.len() && (#[trigger] labels[k]).len() == 0,
{
    lemma_has_empty_label_from_exists(labels, 0);
}

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
