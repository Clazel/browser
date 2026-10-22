//! An independent transcription of the Public Suffix List's "Formal
//! algorithm", written from the Public Suffix List wiki page "Format"
//! (<https://github.com/publicsuffix/list/wiki/Format>) alone, without
//! reference to the project's other transcription. Nothing is imported from
//! sibling modules; strings are `Seq<u32>` code points.
//!
//! Source structure. The page's "Definitions" say that a rule starting with
//! `!` is an exception rule (the algorithm treats it as the rule without
//! the `!`), that domains and rules are split into labels at dots, that
//! "empty labels are not permitted", and that a domain matches a rule when
//! it has at least as many labels and, comparing labels from the right, each
//! pair is identical or the rule's label is `*`. The "Algorithm" is a
//! numbered list, quoted at each use below.
//!
//! Modelling choices:
//! - A rule is `(labels, is_exception)`; the `!` is not part of the labels;
//!   the wildcard label is the one-label string `*`.
//! - The standard leaves ties open (two matching rules with the same number
//!   of labels, or two matching exception rules), so the prevailing rule is
//!   a RELATION ([`ind_prevails`]), not a function. The public suffix length
//!   is then `choose`n among the lengths the relation allows; it is only
//!   meaningful when that length is unique.
//! - Recursions over the rule list and over a rule's labels replace
//!   quantifiers, so the definitions can be evaluated on concrete inputs.
//! - The domain is lower-case ASCII/punycode already (the page presumes it).
//! - A trailing dot is set aside before splitting and re-added to the result.
//!   A domain with an empty label after that is outside the algorithm
//!   (`None`), since "empty labels are not permitted".
//! - The default rule of step 2 is `*` and is not an exception rule.

#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The one-label wildcard `*`.
pub open spec fn ind_star() -> Seq<u32> {
    seq![0x2Au32]
}

/// Splits a string into labels at each '.': the dots are not part of the
/// labels. A string with no '.' is one label; the empty string is one empty
/// label; "a." is the labels "a" and "".
pub open spec fn ind_split(s: Seq<u32>) -> Seq<Seq<u32>>
    decreases s.len(),
{
    if s.len() == 0 {
        seq![Seq::<u32>::empty()]
    } else if s[s.len() - 1] == 0x2Eu32 {
        ind_split(s.drop_last()).push(Seq::<u32>::empty())
    } else {
        let rest = ind_split(s.drop_last());
        rest.drop_last().push(rest.last().push(s[s.len() - 1]))
    }
}

/// Joins labels with '.' (no labels: the empty string).
pub open spec fn ind_join(labels: Seq<Seq<u32>>) -> Seq<u32>
    decreases labels.len(),
{
    if labels.len() == 0 {
        Seq::<u32>::empty()
    } else if labels.len() == 1 {
        labels[0]
    } else {
        ind_join(labels.drop_last()).push(0x2Eu32) + labels.last()
    }
}

/// Compares the first `k` labels of `rule` (from the right) with the
/// corresponding labels of `dom`, right-aligned.
pub open spec fn ind_match_from(rule: Seq<Seq<u32>>, dom: Seq<Seq<u32>>, k: nat) -> bool
    decreases k,
{
    if k == 0 {
        true
    } else if k > rule.len() || rule.len() > dom.len() {
        false
    } else {
        let r = rule[k - 1];
        let d = dom[dom.len() - rule.len() + k - 1];
        (r == ind_star() || r == d) && ind_match_from(rule, dom, (k - 1) as nat)
    }
}

/// Definitions: "A domain is said to match a rule if and only if all of the
/// following conditions are met: when the domain and rule are split into
/// corresponding labels, that the domain contains as many or more labels
/// than the rule, and beginning with the right-most labels of both the
/// domain and the rule, and continuing for all labels in the rule, one of
/// the following is true: the label from the domain is an exact match of the
/// label from the rule; or the label from the rule is `*`."
///
/// Quantifier form: `rule.len() <= dom.len() && forall|i| 0 <= i <
/// rule.len() ==> rule[i] == ind_star() || rule[i] == dom[dom.len() -
/// rule.len() + i]`.
pub open spec fn ind_matches(rule_labels: Seq<Seq<u32>>, domain_labels: Seq<Seq<u32>>) -> bool {
    rule_labels.len() <= domain_labels.len()
        && ind_match_from(rule_labels, domain_labels, rule_labels.len())
}

/// Some rule among the first `k` matches the domain.
pub open spec fn ind_any_match(
    rules: Seq<(Seq<Seq<u32>>, bool)>,
    dom: Seq<Seq<u32>>,
    k: nat,
) -> bool
    decreases k,
{
    if k == 0 || k > rules.len() {
        false
    } else {
        ind_matches(rules[k - 1].0, dom) || ind_any_match(rules, dom, (k - 1) as nat)
    }
}

/// Some exception rule among the first `k` matches the domain.
pub open spec fn ind_any_exception_match(
    rules: Seq<(Seq<Seq<u32>>, bool)>,
    dom: Seq<Seq<u32>>,
    k: nat,
) -> bool
    decreases k,
{
    if k == 0 || k > rules.len() {
        false
    } else {
        (rules[k - 1].1 && ind_matches(rules[k - 1].0, dom))
            || ind_any_exception_match(rules, dom, (k - 1) as nat)
    }
}

/// `(rl, ex)` is one of the first `k` rules.
pub open spec fn ind_in_list(
    rules: Seq<(Seq<Seq<u32>>, bool)>,
    rl: Seq<Seq<u32>>,
    ex: bool,
    k: nat,
) -> bool
    decreases k,
{
    if k == 0 || k > rules.len() {
        false
    } else {
        rules[k - 1] == (rl, ex) || ind_in_list(rules, rl, ex, (k - 1) as nat)
    }
}

/// None of the first `k` rules that match the domain has more labels than `rl`.
pub open spec fn ind_none_longer(
    rules: Seq<(Seq<Seq<u32>>, bool)>,
    dom: Seq<Seq<u32>>,
    rl: Seq<Seq<u32>>,
    k: nat,
) -> bool
    decreases k,
{
    if k == 0 || k > rules.len() {
        true
    } else {
        (!ind_matches(rules[k - 1].0, dom) || rules[k - 1].0.len() <= rl.len())
            && ind_none_longer(rules, dom, rl, (k - 1) as nat)
    }
}

/// The Algorithm, steps 1 to 4, as a relation: `(rule_labels, is_exception)`
/// is allowed to be the prevailing rule.
/// 1. "Match domain against all rules and take note of the matching ones."
/// 2. "If no rules match, the prevailing rule is "*"."
/// 3. "If more than one rule matches, the prevailing rule is the one which
///    is an exception rule."
/// 4. "If there is no matching exception rule, the prevailing rule is the
///    one with the most labels."
/// Ties are left open, so every tied rule is allowed.
pub open spec fn ind_prevails(
    rules: Seq<(Seq<Seq<u32>>, bool)>,
    domain_labels: Seq<Seq<u32>>,
    rule_labels: Seq<Seq<u32>>,
    is_exception: bool,
) -> bool {
    if !ind_any_match(rules, domain_labels, rules.len()) {
        // 2.
        rule_labels == seq![ind_star()] && !is_exception
    } else {
        ind_in_list(rules, rule_labels, is_exception, rules.len())
            && ind_matches(rule_labels, domain_labels)
            // 3.
            && (ind_any_exception_match(rules, domain_labels, rules.len()) ==> is_exception)
            // 4.
            && (!ind_any_exception_match(rules, domain_labels, rules.len())
                ==> ind_none_longer(rules, domain_labels, rule_labels, rules.len()))
    }
}

/// Steps 5 and 6: some prevailing rule gives a public suffix of exactly `n`
/// labels.
/// 5. "If the prevailing rule is an exception rule, modify it by removing the
///    leftmost label."
/// 6. "The public suffix is the set of labels from the domain which match
///    the labels of the prevailing rule, using the matching algorithm
///    above."
pub open spec fn ind_suffix_labels(
    rules: Seq<(Seq<Seq<u32>>, bool)>,
    domain_labels: Seq<Seq<u32>>,
    n: nat,
) -> bool {
    exists|rl: Seq<Seq<u32>>, ex: bool|
        #![trigger ind_prevails(rules, domain_labels, rl, ex)]
        ind_prevails(rules, domain_labels, rl, ex)
            && n == (if ex && rl.len() > 0 { (rl.len() - 1) as nat } else { rl.len() })
}

/// The number of labels of the public suffix. Only meaningful when the `n`
/// satisfying [`ind_suffix_labels`] is unique (ties between equally good
/// rules may otherwise leave several).
pub open spec fn ind_public_suffix_len(
    rules: Seq<(Seq<Seq<u32>>, bool)>,
    domain_labels: Seq<Seq<u32>>,
) -> nat {
    choose|n: nat| ind_suffix_labels(rules, domain_labels, n)
}

/// The domain with one trailing dot set aside.
pub open spec fn ind_body(domain: Seq<u32>) -> Seq<u32> {
    if domain.len() > 0 && domain[domain.len() - 1] == 0x2Eu32 {
        domain.drop_last()
    } else {
        domain
    }
}

/// The domain included a trailing dot.
pub open spec fn ind_has_trailing_dot(domain: Seq<u32>) -> bool {
    domain.len() > 0 && domain[domain.len() - 1] == 0x2Eu32
}

/// "Empty labels are not permitted": no label is empty.
pub open spec fn ind_no_empty_label(labels: Seq<Seq<u32>>) -> bool {
    forall|i: int| 0 <= i < labels.len() ==> (#[trigger] labels[i]).len() > 0
}

/// Step 6 on a domain string: the matching labels joined by '.', "If the
/// domain had a trailing dot, add one to the suffix" (Note 3: `example.com`
/// gives `com`, `example.com.` gives `com.`). `None` for a domain with an
/// empty label (after setting a trailing dot aside).
pub open spec fn ind_public_suffix(
    rules: Seq<(Seq<Seq<u32>>, bool)>,
    domain: Seq<u32>,
) -> Option<Seq<u32>> {
    let labels = ind_split(ind_body(domain));
    if !ind_no_empty_label(labels) {
        None
    } else {
        let n = ind_public_suffix_len(rules, labels);
        let suffix = ind_join(labels.skip(labels.len() - n));
        Some(if ind_has_trailing_dot(domain) { suffix.push(0x2Eu32) } else { suffix })
    }
}

/// Step 7: "The registered or registrable domain is the public suffix plus
/// one additional label." `None` when the domain has no label beyond its
/// public suffix, or when [`ind_public_suffix`] is `None`.
pub open spec fn ind_registrable_domain(
    rules: Seq<(Seq<Seq<u32>>, bool)>,
    domain: Seq<u32>,
) -> Option<Seq<u32>> {
    let labels = ind_split(ind_body(domain));
    if !ind_no_empty_label(labels) {
        None
    } else {
        let n = ind_public_suffix_len(rules, labels);
        if labels.len() <= n {
            None
        } else {
            let reg = ind_join(labels.skip(labels.len() - n - 1));
            Some(if ind_has_trailing_dot(domain) { reg.push(0x2Eu32) } else { reg })
        }
    }
}

// ---------------------------------------------------------------------
// Sanity examples (not part of the transcription).

/// Rules `com`, `uk`, `co.uk`, `*.ck`, `!www.ck`.
pub open spec fn ex_rules() -> Seq<(Seq<Seq<u32>>, bool)> {
    seq![
        (seq![seq![0x63u32, 0x6Fu32, 0x6Du32]], false),
        (seq![seq![0x75u32, 0x6Bu32]], false),
        (seq![seq![0x63u32, 0x6Fu32], seq![0x75u32, 0x6Bu32]], false),
        (seq![seq![0x2Au32], seq![0x63u32, 0x6Bu32]], false),
        (seq![seq![0x77u32, 0x77u32, 0x77u32], seq![0x63u32, 0x6Bu32]], true),
    ]
}

proof fn reveal_fuel() {
    reveal_with_fuel(ind_match_from, 4);
    reveal_with_fuel(ind_any_match, 7);
    reveal_with_fuel(ind_any_exception_match, 7);
    reveal_with_fuel(ind_in_list, 7);
    reveal_with_fuel(ind_none_longer, 7);
}

proof fn example_split_join() {
    let s = seq![0x61u32, 0x2Eu32, 0x62u32, 0x63u32];
    reveal_with_fuel(ind_split, 6);
    reveal_with_fuel(ind_join, 4);
    assert(ind_split(seq![0x61u32]) =~= seq![seq![0x61u32]]);
    assert(ind_split(seq![0x61u32, 0x2Eu32]) =~= seq![seq![0x61u32], Seq::<u32>::empty()]);
    assert(ind_split(seq![0x61u32, 0x2Eu32, 0x62u32]) =~= seq![seq![0x61u32], seq![0x62u32]]);
    let r3 = ind_split(seq![0x61u32, 0x2Eu32, 0x62u32]);
    assert(r3.drop_last() =~= seq![seq![0x61u32]]);
    assert(r3.last() =~= seq![0x62u32]);
    assert(r3.last().push(0x63u32) =~= seq![0x62u32, 0x63u32]);
    assert(s.drop_last() =~= seq![0x61u32, 0x2Eu32, 0x62u32]);
    assert(ind_split(s) =~= seq![seq![0x61u32], seq![0x62u32, 0x63u32]]);
    assert(ind_join(ind_split(s)) =~= s);
    assert(ind_split(Seq::<u32>::empty()) =~= seq![Seq::<u32>::empty()]);
}

proof fn example_matches() {
    reveal_with_fuel(ind_match_from, 4); reveal_with_fuel(ind_any_match, 7); reveal_with_fuel(ind_any_exception_match, 7); reveal_with_fuel(ind_in_list, 7); reveal_with_fuel(ind_none_longer, 7);
    let co_uk = seq![seq![0x63u32, 0x6Fu32], seq![0x75u32, 0x6Bu32]];
    let abcouk = seq![seq![0x61u32], seq![0x62u32], seq![0x63u32, 0x6Fu32], seq![0x75u32, 0x6Bu32]];
    assert(ind_matches(co_uk, abcouk));
    assert(!ind_matches(abcouk, co_uk));
    let star_ck = seq![seq![0x2Au32], seq![0x63u32, 0x6Bu32]];
    let www_ck = seq![seq![0x77u32, 0x77u32, 0x77u32], seq![0x63u32, 0x6Bu32]];
    assert(ind_matches(star_ck, www_ck));
    assert(!ind_matches(co_uk, www_ck));
}

/// example.com: prevailing rule `com`, suffix 1 label.
proof fn example_com() {
    reveal_with_fuel(ind_match_from, 4); reveal_with_fuel(ind_any_match, 7); reveal_with_fuel(ind_any_exception_match, 7); reveal_with_fuel(ind_in_list, 7); reveal_with_fuel(ind_none_longer, 7);
    let d = seq![seq![0x65u32, 0x78u32], seq![0x63u32, 0x6Fu32, 0x6Du32]];
    let com = seq![seq![0x63u32, 0x6Fu32, 0x6Du32]];
    assert(ind_prevails(ex_rules(), d, com, false));
    assert(ind_suffix_labels(ex_rules(), d, 1));
}

/// a.b.co.uk: `co.uk` prevails over `uk`; suffix 2 labels.
proof fn example_co_uk() {
    reveal_with_fuel(ind_match_from, 4); reveal_with_fuel(ind_any_match, 7); reveal_with_fuel(ind_any_exception_match, 7); reveal_with_fuel(ind_in_list, 7); reveal_with_fuel(ind_none_longer, 7);
    let d = seq![seq![0x61u32], seq![0x62u32], seq![0x63u32, 0x6Fu32], seq![0x75u32, 0x6Bu32]];
    let co_uk = seq![seq![0x63u32, 0x6Fu32], seq![0x75u32, 0x6Bu32]];
    let uk = seq![seq![0x75u32, 0x6Bu32]];
    assert(ind_prevails(ex_rules(), d, co_uk, false));
    assert(!ind_prevails(ex_rules(), d, uk, false));
    assert(ind_suffix_labels(ex_rules(), d, 2));
}

/// www.ck: the exception rule `!www.ck` prevails; its leftmost label is
/// removed, leaving 1 label (`ck`).
proof fn example_www_ck() {
    reveal_with_fuel(ind_match_from, 4); reveal_with_fuel(ind_any_match, 7); reveal_with_fuel(ind_any_exception_match, 7); reveal_with_fuel(ind_in_list, 7); reveal_with_fuel(ind_none_longer, 7);
    let d = seq![seq![0x77u32, 0x77u32, 0x77u32], seq![0x63u32, 0x6Bu32]];
    let star_ck = seq![seq![0x2Au32], seq![0x63u32, 0x6Bu32]];
    assert(ind_prevails(ex_rules(), d, d, true));
    assert(!ind_prevails(ex_rules(), d, star_ck, false));
    assert(ind_suffix_labels(ex_rules(), d, 1));
}

/// a.b.ck: `*.ck` prevails; suffix 2 labels.
proof fn example_a_b_ck() {
    reveal_with_fuel(ind_match_from, 4); reveal_with_fuel(ind_any_match, 7); reveal_with_fuel(ind_any_exception_match, 7); reveal_with_fuel(ind_in_list, 7); reveal_with_fuel(ind_none_longer, 7);
    let d = seq![seq![0x61u32], seq![0x62u32], seq![0x63u32, 0x6Bu32]];
    let star_ck = seq![seq![0x2Au32], seq![0x63u32, 0x6Bu32]];
    assert(ind_prevails(ex_rules(), d, star_ck, false));
    assert(ind_suffix_labels(ex_rules(), d, 2));
}

/// zz.unknown: no rule matches; the default rule `*` gives 1 label.
proof fn example_unknown() {
    reveal_with_fuel(ind_match_from, 4); reveal_with_fuel(ind_any_match, 7); reveal_with_fuel(ind_any_exception_match, 7); reveal_with_fuel(ind_in_list, 7); reveal_with_fuel(ind_none_longer, 7);
    let d = seq![seq![0x7Au32, 0x7Au32], seq![0x75u32, 0x6Eu32]];
    assert(ind_prevails(ex_rules(), d, seq![ind_star()], false));
    assert(ind_suffix_labels(ex_rules(), d, 1));
}

} // verus!
