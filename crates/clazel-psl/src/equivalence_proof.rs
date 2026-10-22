//! Proof that [`super::spec`] and [`super::independent`] agree
//! ([`super::equivalence`] states what). The route: the independent
//! helpers (split, join, match, the recursions over the rule list) are
//! shown to be the spec's, and for a well-formed list
//! ([`super::wf::rules_wf`]) the relation `ind_prevails` has exactly one
//! answer for the number of labels, the one `suffix_label_count` computes.

use super::equivalence::*;
use super::independent::*;
use super::lemmas::*;
use super::spec::*;
use super::wf::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// `ind_join` is the project's `split_join`, on a non-empty list.
pub proof fn lemma_ind_join(l: Seq<Seq<u32>>)
    requires
        l.len() >= 1,
    ensures
        ind_join(l) == clazel_url::host::lemmas::split_join(l, 0x2E),
    decreases l.len(),
{
    if l.len() == 1 {
        assert(l.drop_first() =~= Seq::<Seq<u32>>::empty());
        assert(clazel_url::host::lemmas::split_join(l, 0x2E) =~= l[0]);
    } else {
        let a = l.drop_last();
        lemma_ind_join(a);
        super::join::lemma_split_join_push(a, l.last());
        assert(a.push(l.last()) =~= l);
        assert(ind_join(l) =~= ind_join(a).push(0x2Eu32) + l.last());
        assert(ind_join(l) =~= clazel_url::host::lemmas::split_join(a, 0x2E) + seq![0x2Eu32] + l.last());
    }
}

/// `ind_split` gives a non-empty list of dot-free labels that joins back.
pub proof fn lemma_ind_split_props(s: Seq<u32>)
    ensures
        ind_split(s).len() >= 1,
        forall|k: int| 0 <= k < ind_split(s).len() ==> clazel_url::host::lemmas::free_of(#[trigger] ind_split(s)[k], 0x2E),
        ind_join(ind_split(s)) == s,
    decreases s.len(),
{
    if s.len() == 0 {
        assert(ind_split(s) =~= seq![Seq::<u32>::empty()]);
        assert(ind_join(ind_split(s)) =~= s);
    } else {
        let r = ind_split(s.drop_last());
        lemma_ind_split_props(s.drop_last());
        let c = s[s.len() - 1];
        if c == 0x2Eu32 {
            let res = r.push(Seq::<u32>::empty());
            assert(res.len() >= 2);
            assert(res.drop_last() =~= r);
            assert(ind_join(res) =~= ind_join(r).push(0x2Eu32) + Seq::<u32>::empty());
            assert(ind_join(res) =~= s);
            assert forall|k: int| 0 <= k < res.len() implies clazel_url::host::lemmas::free_of(#[trigger] res[k], 0x2E) by {
                if k < r.len() {
                    assert(res[k] == r[k]);
                }
            }
        } else {
            let res = r.drop_last().push(r.last().push(c));
            assert(res.len() == r.len());
            assert(r[r.len() - 1] == r.last());
            assert forall|k: int| 0 <= k < res.len() implies clazel_url::host::lemmas::free_of(#[trigger] res[k], 0x2E) by {
                if k < res.len() - 1 {
                    assert(res[k] == r[k]);
                } else {
                    assert(res[k] =~= r.last().push(c));
                    assert(clazel_url::host::lemmas::free_of(r.last(), 0x2E));
                    assert forall|x: int| 0 <= x < res[k].len() implies res[k][x] != 0x2Eu32 by {
                        if x < r.last().len() {
                            assert(res[k][x] == r.last()[x]);
                        }
                    }
                }
            }
            if r.len() == 1 {
                assert(res =~= seq![r[0].push(c)]);
                assert(ind_join(res) =~= r[0].push(c));
                assert(ind_join(r) =~= r[0]);
                assert(s =~= s.drop_last().push(c));
            } else {
                assert(res.drop_last() =~= r.drop_last());
                assert(ind_join(res) =~= ind_join(r.drop_last()).push(0x2Eu32) + r.last().push(c));
                assert(ind_join(r) =~= ind_join(r.drop_last()).push(0x2Eu32) + r.last());
                assert(s =~= s.drop_last().push(c));
                assert(ind_join(res) =~= ind_join(r).push(c));
            }
        }
    }
}

/// `ind_split` is Infra's "strictly split" on ".".
pub proof fn lemma_ind_split_is_strictly_split(s: Seq<u32>)
    ensures
        ind_split(s) == clazel_url::host::spec::strictly_split(s, 0x2E),
{
    lemma_ind_split_props(s);
    lemma_ind_join(ind_split(s));
    clazel_url::host::lemmas::lemma_strictly_split_join(ind_split(s), 0x2E);
}

/// The independent transcription splits the domain as the spec does.
pub proof fn lemma_labels_agree(domain: Seq<u32>)
    ensures
        ind_split(ind_body(domain)) == domain_labels(domain),
        ind_has_trailing_dot(domain) == has_trailing_dot(domain),
        ind_no_empty_label(domain_labels(domain)) <==> !has_empty_label(domain_labels(domain)),
{
    assert(ind_body(domain) == strip_trailing_dot(domain));
    lemma_ind_split_is_strictly_split(ind_body(domain));
    lemma_has_empty_label_exists(domain_labels(domain));
}

/// `ind_match_from` is the quantifier form, for `k` at most the rule's labels.
pub proof fn lemma_ind_match_from(rule: Seq<Seq<u32>>, dom: Seq<Seq<u32>>, k: nat)
    requires
        k <= rule.len() <= dom.len(),
    ensures
        ind_match_from(rule, dom, k) <==> forall|x: int|
            0 <= x < k ==> (#[trigger] rule[x] == ind_star() || rule[x] == dom[dom.len() - rule.len() + x]),
    decreases k,
{
    if k > 0 {
        lemma_ind_match_from(rule, dom, (k - 1) as nat);
        if ind_match_from(rule, dom, k) {
            assert forall|x: int| 0 <= x < k implies (#[trigger] rule[x] == ind_star() || rule[x] == dom[dom.len() - rule.len() + x]) by {
                if x < k - 1 {
                    assert(0 <= x < (k - 1) as int);
                }
            }
        }
    }
}

/// Matching is the same in both transcriptions.
pub proof fn lemma_matches_agree(rule: Rule, d: Seq<Seq<u32>>)
    ensures
        ind_matches(rule.labels, d) == rule_matches(rule, d),
{
    lemma_rule_matches_forall(rule, d);
    if rule.labels.len() <= d.len() {
        lemma_ind_match_from(rule.labels, d, rule.labels.len());
        if rule_matches(rule, d) {
            assert forall|x: int| 0 <= x < rule.labels.len() implies (#[trigger] rule.labels[x] == ind_star() || rule.labels[x] == d[d.len() - rule.labels.len() + x]) by {
                let k = rule.labels.len() - 1 - x;
                assert(0 <= k < rule.labels.len());
                assert(label_matches(rule.labels[rule.labels.len() - 1 - k], d[d.len() - 1 - k]));
            }
        }
        if ind_matches(rule.labels, d) {
            assert forall|k: int| 0 <= k < rule.labels.len() implies label_matches(#[trigger] rule.labels[rule.labels.len() - 1 - k], d[d.len() - 1 - k]) by {
                let x = rule.labels.len() - 1 - k;
                assert(rule.labels[x] == ind_star() || rule.labels[x] == d[d.len() - rule.labels.len() + x]);
            }
        }
    }
}

/// The recursions over the rule list are the quantifiers.
pub proof fn lemma_ind_recursions(rules: Seq<Rule>, d: Seq<Seq<u32>>, rl: Seq<Seq<u32>>, ex: bool, k: nat)
    requires
        k <= rules.len(),
    ensures
        ind_any_match(ind_rules(rules), d, k) <==> exists|i: int| 0 <= i < k && rule_matches(#[trigger] rules[i], d),
        ind_any_exception_match(ind_rules(rules), d, k) <==> exists|i: int| 0 <= i < k && (#[trigger] rules[i]).exception && rule_matches(rules[i], d),
        ind_in_list(ind_rules(rules), rl, ex, k) <==> exists|i: int| 0 <= i < k && (#[trigger] rules[i]).labels == rl && rules[i].exception == ex,
        ind_none_longer(ind_rules(rules), d, rl, k) <==> forall|i: int|
            0 <= i < k && rule_matches(#[trigger] rules[i], d) ==> rules[i].labels.len() <= rl.len(),
    decreases k,
{
    if k > 0 {
        lemma_ind_recursions(rules, d, rl, ex, (k - 1) as nat);
        let ir = ind_rules(rules);
        let i = (k - 1) as int;
        assert(ir[i] == ind_rule(rules[i]));
        lemma_matches_agree(rules[i], d);
        if ind_any_match(ir, d, k) {
            if !rule_matches(rules[i], d) {
                assert(exists|j: int| 0 <= j < k - 1 && rule_matches(#[trigger] rules[j], d));
            }
        }
        if ind_any_exception_match(ir, d, k) && !(rules[i].exception && rule_matches(rules[i], d)) {
            assert(exists|j: int| 0 <= j < k - 1 && (#[trigger] rules[j]).exception && rule_matches(rules[j], d));
        }
    }
}

/// The spec's one-pass choice, as the properties the independent relation
/// needs.
pub proof fn lemma_prevailing_props(rules: Seq<Rule>, d: Seq<Seq<u32>>, n: nat)
    requires
        n <= rules.len(),
    ensures
        (prevailing_from(rules, d, n) is Some) <==> exists|i: int| 0 <= i < n && rule_matches(#[trigger] rules[i], d),
        match prevailing_from(rules, d, n) {
            Some(p) => {
                &&& p < n
                &&& rule_matches(rules[p as int], d)
                &&& (exists|i: int| 0 <= i < n && (#[trigger] rules[i]).exception && rule_matches(rules[i], d)) ==> rules[p as int].exception
                &&& (!exists|i: int| 0 <= i < n && (#[trigger] rules[i]).exception && rule_matches(rules[i], d)) ==> (forall|i: int|
                    0 <= i < n && rule_matches(#[trigger] rules[i], d) ==> rules[i].labels.len() <= rules[p as int].labels.len())
            },
            None => true,
        },
    decreases n,
{
    if n > 0 {
        lemma_prevailing_props(rules, d, (n - 1) as nat);
        let last = (n - 1) as int;
        let best = prevailing_from(rules, d, (n - 1) as nat);
        let r = rules[last];
        if rule_matches(r, d) && (best is None || beats(r, rules[best->Some_0 as int])) {
            if r.exception {
                assert(rules[last].exception && rule_matches(rules[last], d));
            }
            if best is Some {
                let b = best->Some_0 as int;
                if !r.exception {
                    // beats(r, b) with r not an exception: b is not one either,
                    // so no earlier rule is a matching exception.
                    assert(!rules[b].exception);
                    assert(!exists|i: int| 0 <= i < n - 1 && (#[trigger] rules[i]).exception && rule_matches(rules[i], d));
                }
            }
        } else {
            if rule_matches(r, d) {
                // best is Some and r does not beat it.
                let b = best->Some_0 as int;
                if r.exception && rule_matches(r, d) {
                    assert(rules[b].exception);
                }
                if !exists|i: int| 0 <= i < n && (#[trigger] rules[i]).exception && rule_matches(rules[i], d) {
                    assert(!exists|i: int| 0 <= i < n - 1 && (#[trigger] rules[i]).exception && rule_matches(rules[i], d));
                    assert(!rules[b].exception);
                    assert(!r.exception);
                }
            }
            if (exists|i: int| 0 <= i < n && (#[trigger] rules[i]).exception && rule_matches(rules[i], d)) && !(r.exception && rule_matches(r, d)) {
                assert(exists|i: int| 0 <= i < n - 1 && (#[trigger] rules[i]).exception && rule_matches(rules[i], d));
            }
        }
    }
}

/// In a well-formed list, two matching exception rules are the same rule.
pub proof fn lemma_one_exception(rules: Seq<Rule>, d: Seq<Seq<u32>>, i: int, j: int)
    requires
        rules_wf(rules),
        0 <= i < rules.len(),
        0 <= j < rules.len(),
        rules[i].exception,
        rules[j].exception,
        rule_matches(rules[i], d),
        rule_matches(rules[j], d),
    ensures
        i == j,
{
    if i != j {
        lemma_rule_matches_forall(rules[i], d);
        lemma_rule_matches_forall(rules[j], d);
        let a = rules[i].labels;
        let b = rules[j].labels;
        if a.len() <= b.len() {
            assert forall|x: int| 0 <= x < a.len() implies a[x] == b.skip((b.len() - a.len()) as int)[x] by {
                let k = a.len() - 1 - x;
                assert(label_matches(a[a.len() - 1 - k], d[d.len() - 1 - k]));
                assert(a[x] != star_label());
                let k2 = b.len() - 1 - (b.len() - a.len() + x);
                assert(0 <= k2 < b.len());
                assert(label_matches(b[b.len() - 1 - k2], d[d.len() - 1 - k2]));
                assert(b[b.len() - a.len() + x] != star_label());
            }
            assert(a =~= b.skip((b.len() - a.len()) as int));
            assert(false);
        } else {
            assert forall|x: int| 0 <= x < b.len() implies b[x] == a.skip((a.len() - b.len()) as int)[x] by {
                let k = b.len() - 1 - x;
                assert(label_matches(b[b.len() - 1 - k], d[d.len() - 1 - k]));
                assert(b[x] != star_label());
                let k2 = a.len() - 1 - (a.len() - b.len() + x);
                assert(0 <= k2 < a.len());
                assert(label_matches(a[a.len() - 1 - k2], d[d.len() - 1 - k2]));
                assert(a[a.len() - b.len() + x] != star_label());
            }
            assert(b =~= a.skip((a.len() - b.len()) as int));
            assert(false);
        }
    }
}

/// For a well-formed list the relation has exactly the spec's answer.
pub proof fn lemma_count_agrees(rules: Seq<Rule>, d: Seq<Seq<u32>>)
    requires
        rules_wf(rules),
    ensures
        ind_suffix_labels(ind_rules(rules), d, suffix_label_count(rules, d)),
        forall|n: nat| ind_suffix_labels(ind_rules(rules), d, n) ==> n == suffix_label_count(rules, d),
{
    let ir = ind_rules(rules);
    let len = rules.len();
    let n0 = suffix_label_count(rules, d);
    lemma_prevailing_props(rules, d, len);
    lemma_ind_recursions(rules, d, seq![ind_star()], false, len);
    match prevailing_from(rules, d, len) {
        None => {
            let star = seq![ind_star()];
            assert(!ind_any_match(ir, d, len));
            assert(prevailing_rule(rules, d).labels == star);
            assert(n0 == 1);
            assert(ind_prevails(ir, d, star, false));
            assert(star.len() == 1);
            assert(ind_suffix_labels(ir, d, n0));
            assert forall|n: nat| ind_suffix_labels(ir, d, n) implies n == n0 by {
                let (rl, ex) = choose|rl: Seq<Seq<u32>>, ex: bool|
                    #![trigger ind_prevails(ir, d, rl, ex)]
                    ind_prevails(ir, d, rl, ex) && n == (if ex && rl.len() > 0 { (rl.len() - 1) as nat } else { rl.len() });
                assert(rl == star && !ex);
            }
        },
        Some(p) => {
            let rp = rules[p as int];
            assert(rules[p as int] == prevailing_rule(rules, d));
            assert(rp.labels.len() >= 1);
            assert(ind_any_match(ir, d, len));
            lemma_ind_recursions(rules, d, rp.labels, rp.exception, len);
            assert(ir[p as int] == ind_rule(rp));
            lemma_matches_agree(rp, d);
            assert(ind_prevails(ir, d, rp.labels, rp.exception));
            assert(n0 == (if rp.exception && rp.labels.len() > 0 { (rp.labels.len() - 1) as nat } else { rp.labels.len() }));
            assert(ind_suffix_labels(ir, d, n0));
            assert forall|n: nat| ind_suffix_labels(ir, d, n) implies n == n0 by {
                let (rl, ex) = choose|rl: Seq<Seq<u32>>, ex: bool|
                    #![trigger ind_prevails(ir, d, rl, ex)]
                    ind_prevails(ir, d, rl, ex) && n == (if ex && rl.len() > 0 { (rl.len() - 1) as nat } else { rl.len() });
                lemma_ind_recursions(rules, d, rl, ex, len);
                let q = choose|q: int| 0 <= q < len && (#[trigger] rules[q]).labels == rl && rules[q].exception == ex;
                lemma_matches_agree(rules[q], d);
                assert(ind_matches(rl, d));
                assert(rule_matches(rules[q], d));
                if exists|i: int| 0 <= i < len && (#[trigger] rules[i]).exception && rule_matches(rules[i], d) {
                    assert(ex);
                    lemma_one_exception(rules, d, q, p as int);
                } else {
                    assert(!ex);
                    assert(ind_none_longer(ir, d, rl, len));
                    assert(rules[p as int].labels.len() <= rl.len());
                    assert(rl.len() <= rp.labels.len());
                    assert(!rp.exception);
                }
            }
        },
    }
}

/// The two public suffixes agree on a well-formed list.
pub proof fn lemma_public_suffix_equivalence(rules: Seq<Rule>, domain: Seq<u32>)
    requires
        rules_wf(rules),
    ensures
        public_suffix_equivalence(rules, domain),
{
    lemma_labels_agree(domain);
    lemma_domain_labels_join(domain);
    let d = domain_labels(domain);
    let td = has_trailing_dot(domain);
    lemma_has_empty_label_exists(d);
    if !has_empty_label(d) {
        lemma_count_agrees(rules, d);
        let n0 = suffix_label_count(rules, d);
        assert(ind_suffix_labels(ind_rules(rules), d, n0));
        assert(ind_public_suffix_len(ind_rules(rules), d) == n0);
        lemma_suffix_label_count_bounds(rules, d);
        let sub = d.skip((d.len() - n0) as int);
        lemma_ind_join(sub);
        assert(ind_join(sub) == clazel_url::host::lemmas::split_join(sub, 0x2E));
        if td {
            assert(ind_join(sub).push(0x2Eu32) =~= ind_join(sub) + seq![0x2Eu32]);
        } else {
            assert(ind_join(sub) =~= ind_join(sub) + Seq::<u32>::empty());
        }
    }
}

/// The two registrable domains agree on a well-formed list.
pub proof fn lemma_registrable_domain_equivalence(rules: Seq<Rule>, domain: Seq<u32>)
    requires
        rules_wf(rules),
    ensures
        registrable_domain_equivalence(rules, domain),
{
    lemma_labels_agree(domain);
    lemma_domain_labels_join(domain);
    let d = domain_labels(domain);
    let td = has_trailing_dot(domain);
    lemma_has_empty_label_exists(d);
    if !has_empty_label(d) {
        lemma_count_agrees(rules, d);
        let n0 = suffix_label_count(rules, d);
        assert(ind_public_suffix_len(ind_rules(rules), d) == n0);
        lemma_suffix_label_count_bounds(rules, d);
        lemma_label_suffix_is_domain(domain, n0);
        if n0 < d.len() {
            let sub = d.skip((d.len() - n0 - 1) as int);
            lemma_ind_join(sub);
            if td {
                assert(ind_join(sub).push(0x2Eu32) =~= ind_join(sub) + seq![0x2Eu32]);
            } else {
                assert(ind_join(sub) =~= ind_join(sub) + Seq::<u32>::empty());
            }
        }
    }
}

/// The independent transcription agrees with the spec on the generated
/// list, for public suffixes and registrable domains alike, for every
/// domain.
pub proof fn lemma_table_equivalence(domain: Seq<u32>)
    ensures
        public_suffix_equivalence(super::table::psl_rules(), domain),
        registrable_domain_equivalence(super::table::psl_rules(), domain),
{
    super::wf_table::lemma_table_wf();
    lemma_public_suffix_equivalence(super::table::psl_rules(), domain);
    lemma_registrable_domain_equivalence(super::table::psl_rules(), domain);
}

} // verus!
