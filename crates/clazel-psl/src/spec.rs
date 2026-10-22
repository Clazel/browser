//! Executable-style specification of the Public Suffix List algorithm and
//! of what the URL Standard builds on it: "public suffix" and "registrable
//! domain" of a host (§3.2), and the **cookie root** (our definition, below).
//! Nothing here runs; it defines what "correct" means. Every definition
//! cites its source, and each `// N.` comment is the step number in the
//! cited algorithm.
//!
//! Sources (each pinned; a review is against exactly this text):
//! - URL Standard, Living Standard, `url.bs` at commit
//!   `845bafca22fb0c5a42c4bf384a9bdea525a2f10d` (19 October 2026),
//!   <https://url.spec.whatwg.org/#host-miscellaneous>: §3.2 "obtain the
//!   public suffix of a host" and "obtain the registrable domain of a
//!   host", and the example table that follows them.
//! - Public Suffix List, "Format", sections "Entry Specification" and
//!   "Formal algorithm" (the repository's wiki page
//!   <https://github.com/publicsuffix/list/wiki/Format>, which the URL
//!   Standard's "obtain the public suffix" and "obtain the registrable
//!   domain" link to in step 3), as fetched on 21 October 2026
//!   (SHA-256 of the page's Markdown
//!   `78ed430cacb1ca738ea741c736edaec0c5bb8d5c2eb3ab9cf46cd6b9818e404e`).
//!   Its "Algorithm" bullets are quoted as `A1` to `A7`, in order:
//!   A1 "Match domain against all rules and take note of the matching
//!   ones.", A2 "If no rules match, the prevailing rule is "*".", A3 "If
//!   more than one rule matches, the prevailing rule is the one which is an
//!   exception rule.", A4 "If there is no matching exception rule, the
//!   prevailing rule is the one with the most labels.", A5 "If the
//!   prevailing rule is a exception rule, modify it by removing the
//!   leftmost label.", A6 "The public suffix is the set of labels from the
//!   domain which match the labels of the prevailing rule, using the
//!   matching algorithm above. A trailing dot shall be added if the domain
//!   included one.", A7 "The registered or registrable domain is the public
//!   suffix plus one additional label."
//! - Infra Standard, commit `459b7829230ad256a690dabd315db974469af8e7`:
//!   §4.7 "strictly split" (from `clazel-url`'s spec), which is how the URL
//!   Standard splits a domain into its labels (§3.1 "domain labels").
//!
//! The rules themselves are the Public Suffix List, a data file: every
//! function here takes them as `rules: Seq<Rule>`, and what is proven holds
//! for every list. [`super::table::psl_rules`] is the list the generated
//! tables hold (`public_suffix_list.dat` at a pinned commit).
//!
//! Modelling choices (each one is a deliberate, reviewable deviation in
//! form, never in meaning, except where it says it fills a gap):
//! - A string is a `Seq<u32>` of code points, a rule a [`Rule`]: its labels
//!   (left to right, `*` being the one-label string `*`) and whether it is an
//!   exception rule. The list's `!` is not part of the labels. The tables
//!   hold each label of the Unicode list as an A-label, because hosts are
//!   canonical ASCII (the standard says to canonicalize "lower-case,
//!   Punycode ... prior to being compared").
//! - A domain is split into labels by Infra "strictly split" on U+002E
//!   (URL §3.1: "The domain labels of a domain are the result of strictly
//!   splitting domain on U+002E (.)"), after A6's trailing dot is set
//!   aside: the labels of `example.com.` are those of `example.com`, and
//!   the result gets the dot back (Note 3: "looking up `example.com` should
//!   yield `com` while looking up `example.com.` should yield `com.`").
//! - **Empty labels.** The Definitions say "Empty labels are not
//!   permitted", and the list's own tests say that `.com` and
//!   `.example.com` have no registrable domain. The algorithm is not defined
//!   on a domain with an empty label (after A6's trailing dot is set aside:
//!   a leading dot, `a..b`, `.`, and the empty string), and URL §3.2 lets
//!   "obtain the public suffix" return null, so it returns null for these.
//!   They are valid URL hosts (`http://a..b/`), which is why the case is
//!   specified and not assumed away.
//! - "The prevailing rule" is chosen by [`prevailing_from`], one pass over
//!   the rules in list order that keeps the best so far, where an exception
//!   rule beats a non-exception rule (A3), a rule with more labels beats a
//!   rule with fewer among non-exceptions (A4), and the earlier rule wins
//!   otherwise. A3 does not say which exception rule prevails if two match
//!   (and A4 does not say which of two equally long rules): the earlier one.
//!   The generator rejects a list in which two exception rules could match
//!   the same domain, so for the real list the choice never matters, and
//!   two non-exception rules of equal length that both match remove the same
//!   number of labels, so there it cannot matter either.
//! - A5 and A6 are folded into one count: the public suffix has
//!   [`suffix_label_count`] labels, the prevailing rule's, less one if it is
//!   an exception rule. That is at least one: an exception rule with one
//!   label (which the list has none of, and the generator rejects) would
//!   "remove the leftmost label" and leave no label, which has no meaning,
//!   so it keeps one.
//! - URL §3.2 asks for a host that "is a domain"; any other host (an IP
//!   address, an opaque host, the empty host) has no public suffix and no
//!   registrable domain (step 1: "return null").
//! - The standard's Assert steps ("`publicSuffix` is an ASCII string that
//!   ends with `trailingDot`") are lemmas (`lemmas.rs`), not preconditions:
//!   every function here is total.
//! - **The cookie root is ours.** No standard names it; it is defined here
//!   for `clazel-cookie` and `clazel-kernel` (Phase 2 items 2.9, 2.11) and
//!   stated exactly as the plan does: the shortest suffix of the domain, in
//!   labels, that is not a public suffix, or the domain itself when every
//!   suffix is one; for an IP address, the address. (A "suffix, in labels"
//!   keeps the trailing dot, like the public suffix, so that `com.` is a
//!   public suffix and `example.com.` has the root `example.com.`.) A suffix
//!   "is a public suffix" when obtaining its public suffix returns it. An
//!   opaque host and the empty host are their own roots. Why this and not
//!   the registrable domain is the isolation boundary: `lemmas.rs`
//!   (`lemma_root_of_suffix`) proves the property the cookie crate needs,
//!   and 2.9 explains it.

#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// A rule of the list: "A rule may begin with a "!" (exclamation mark). If
/// it does, it is labelled as a "exception rule" and then treated as if the
/// exclamation mark is not present." The labels are the rule split into
/// labels with the separator ".", left to right.
pub struct Rule {
    /// The rule's labels, from left to right.
    pub labels: Seq<Seq<u32>>,
    /// Whether the rule began with "!".
    pub exception: bool,
}

/// The wildcard label: "The wildcard character * (asterisk, specifically
/// U+002A) matches any valid sequence of characters in a hostname part."
pub open spec fn star_label() -> Seq<u32> {
    seq![0x2Au32]
}

/// "...for every pair, either they are identical, or that the label from
/// the rule is "*"."
pub open spec fn label_matches(rule_label: Seq<u32>, domain_label: Seq<u32>) -> bool {
    rule_label == domain_label || rule_label == star_label()
}

/// The labels of `rule` from the `k`-th from the right, up to the leftmost,
/// match the corresponding labels of the domain: "Beginning with the
/// right-most labels of both the domain and the rule, and continuing for all
/// labels in the rule, one finds that for every pair, either they are
/// identical, or that the label from the rule is "*"." (Recursive, so that
/// Verus can evaluate it on a concrete rule; `lemma_rule_matches_forall`
/// proves it is that "for every pair" statement.)
pub open spec fn rule_matches_from(rule: Rule, d: Seq<Seq<u32>>, k: nat) -> bool
    decreases rule.labels.len() - k,
{
    if k >= rule.labels.len() {
        true
    } else {
        label_matches(rule.labels[rule.labels.len() - 1 - k], d[d.len() - 1 - k]) && rule_matches_from(rule, d, k + 1)
    }
}

/// "A domain is said to match a rule if and only if all of the following
/// conditions are met: When the domain and rule are split into
/// corresponding labels, that the domain contains as many or more labels
/// than the rule. Beginning with the right-most labels of both the domain
/// and the rule, and continuing for all labels in the rule, one finds that
/// for every pair, either they are identical, or that the label from the
/// rule is "*"." `d` is the domain's labels.
pub open spec fn rule_matches(rule: Rule, d: Seq<Seq<u32>>) -> bool {
    &&& rule.labels.len() <= d.len()
    &&& rule_matches_from(rule, d, 0)
}

/// `a` beats `b` as the prevailing rule: A3 "the prevailing rule is the one
/// which is an exception rule", A4 "If there is no matching exception rule,
/// the prevailing rule is the one with the most labels". Neither beats an
/// earlier rule of the same kind and length (see the modelling choices).
pub open spec fn beats(a: Rule, b: Rule) -> bool {
    (a.exception && !b.exception) || (!a.exception && !b.exception && a.labels.len() > b.labels.len())
}

/// A1, A3 and A4 over the first `n` rules: the index of the rule that
/// prevails among the matching ones, if any rule among them matches.
pub open spec fn prevailing_from(rules: Seq<Rule>, d: Seq<Seq<u32>>, n: nat) -> Option<nat>
    decreases n,
{
    if n == 0 {
        None
    } else {
        let best = prevailing_from(rules, d, (n - 1) as nat);
        let rule = rules[(n - 1) as int];
        // A1 "take note of the matching ones"
        if rule_matches(rule, d) && (best is None || beats(rule, rules[best->Some_0 as int])) {
            Some((n - 1) as nat)
        } else {
            best
        }
    }
}

/// The prevailing rule: A2 "If no rules match, the prevailing rule is "*"."
/// and otherwise A3 and A4.
pub open spec fn prevailing_rule(rules: Seq<Rule>, d: Seq<Seq<u32>>) -> Rule {
    match prevailing_from(rules, d, rules.len()) {
        // A2.
        None => Rule { labels: seq![star_label()], exception: false },
        Some(i) => rules[i as int],
    }
}

/// How many labels the public suffix has, for the domain with labels `d`:
/// A5 "If the prevailing rule is a exception rule, modify it by removing
/// the leftmost label." and A6 "The public suffix is the set of labels from
/// the domain which match the labels of the prevailing rule" (at least one:
/// see the modelling choices).
pub open spec fn suffix_label_count(rules: Seq<Rule>, d: Seq<Seq<u32>>) -> nat {
    let rule = prevailing_rule(rules, d);
    if rule.exception && rule.labels.len() > 1 {
        (rule.labels.len() - 1) as nat
    } else if rule.labels.len() > 0 {
        rule.labels.len()
    } else {
        1
    }
}

/// URL §3.2 step 2: "Let trailingDot be "." if host ends with "."".
pub open spec fn has_trailing_dot(domain: Seq<u32>) -> bool {
    domain.len() > 0 && domain.last() == 0x2Eu32
}

/// `domain` without the trailing dot, if it has one (A6 and Note 3).
pub open spec fn strip_trailing_dot(domain: Seq<u32>) -> Seq<u32> {
    if has_trailing_dot(domain) {
        domain.drop_last()
    } else {
        domain
    }
}

/// URL §3.1: "The domain labels of a domain domain are the result of
/// strictly splitting domain on U+002E (.)", with the trailing dot set
/// aside.
pub open spec fn domain_labels(domain: Seq<u32>) -> Seq<Seq<u32>> {
    clazel_url::host::spec::strictly_split(strip_trailing_dot(domain), 0x2E)
}

/// Some label of `labels` from the `k`-th on is empty. (Recursive, so that
/// Verus can evaluate it; `lemma_has_empty_label_exists` proves it is the
/// existential statement.)
pub open spec fn has_empty_label_from(labels: Seq<Seq<u32>>, k: nat) -> bool
    decreases labels.len() - k,
{
    if k >= labels.len() {
        false
    } else {
        labels[k as int].len() == 0 || has_empty_label_from(labels, k + 1)
    }
}

/// "Empty labels are not permitted."
pub open spec fn has_empty_label(labels: Seq<Seq<u32>>) -> bool {
    has_empty_label_from(labels, 0)
}

/// `labels` joined with ".", and "A trailing dot shall be added if the
/// domain included one."
pub open spec fn labels_string(labels: Seq<Seq<u32>>, trailing_dot: bool) -> Seq<u32> {
    clazel_url::host::lemmas::split_join(labels, 0x2E) + (if trailing_dot {
        seq![0x2Eu32]
    } else {
        seq![]
    })
}

/// The last `k` labels of `labels`, as a string.
pub open spec fn label_suffix(labels: Seq<Seq<u32>>, trailing_dot: bool, k: nat) -> Seq<u32> {
    labels_string(labels.skip(labels.len() - k), trailing_dot)
}

/// URL §3.2 "obtain the public suffix of a host" for a host that is a
/// domain (step 1), over the rules `rules`: steps 2 to 5, with the Public
/// Suffix List algorithm (A1 to A6) as step 3.
pub open spec fn public_suffix_of_domain(rules: Seq<Rule>, domain: Seq<u32>) -> Option<Seq<u32>> {
    // 2. "Let trailingDot be "." if host ends with "."; otherwise the empty
    //    string."
    let trailing_dot = has_trailing_dot(domain);
    let d = domain_labels(domain);
    if has_empty_label(d) {
        // The algorithm is not defined here (see the modelling choices).
        None
    } else {
        // 3. "Let publicSuffix be the public suffix determined by running
        //    the Public Suffix List algorithm with host as domain."
        // 4. "Assert: publicSuffix is an ASCII string that ends with
        //    trailingDot." (lemma_public_suffix_ends_with)
        // 5. "Return publicSuffix."
        Some(label_suffix(d, trailing_dot, suffix_label_count(rules, d)))
    }
}

/// URL §3.2 "obtain the registrable domain of a host" for a host that is a
/// domain, over the rules `rules`.
pub open spec fn registrable_domain_of_domain(rules: Seq<Rule>, domain: Seq<u32>) -> Option<Seq<u32>> {
    match public_suffix_of_domain(rules, domain) {
        // 1. "If host's public suffix is null [...], then return null."
        None => None,
        Some(public_suffix) => if public_suffix == domain {
            // 1. "[...] or host's public suffix equals host, then return
            //    null."
            None
        } else {
            // 2. "Let trailingDot be "." if host ends with "."; otherwise
            //    the empty string."
            let trailing_dot = has_trailing_dot(domain);
            let d = domain_labels(domain);
            // 3. "Let registrableDomain be the registrable domain
            //    determined by running the Public Suffix List algorithm
            //    with host as domain." (A7: "the public suffix plus one
            //    additional label")
            // 4. "Assert: registrableDomain is an ASCII string that ends
            //    with trailingDot." (lemma_registrable_domain_ends_with)
            // 5. "Return registrableDomain."
            Some(label_suffix(d, trailing_dot, suffix_label_count(rules, d) + 1))
        },
    }
}

/// URL §3.2 "obtain the public suffix of a host".
pub open spec fn public_suffix(rules: Seq<Rule>, host: clazel_url::host::spec::Host) -> Option<Seq<u32>> {
    match host {
        clazel_url::host::spec::Host::Domain(domain) => public_suffix_of_domain(rules, domain),
        // 1. "If host is not a domain, then return null."
        _ => None,
    }
}

/// URL §3.2 "obtain the registrable domain of a host".
pub open spec fn registrable_domain(rules: Seq<Rule>, host: clazel_url::host::spec::Host) -> Option<Seq<u32>> {
    match host {
        clazel_url::host::spec::Host::Domain(domain) => registrable_domain_of_domain(rules, domain),
        // A host that is not a domain has a null public suffix (§3.2
        // "obtain the public suffix", step 1), so step 1 here returns null.
        _ => None,
    }
}

/// A suffix of a domain is "a public suffix" when obtaining its public
/// suffix returns it.
pub open spec fn is_public_suffix(rules: Seq<Rule>, domain: Seq<u32>) -> bool {
    public_suffix_of_domain(rules, domain) == Some(domain)
}

/// The cookie root of a domain, searching the suffixes with `k` labels or
/// more, shortest first: the first that is not a public suffix, or the
/// domain itself once every shorter one is.
pub open spec fn cookie_root_from(rules: Seq<Rule>, domain: Seq<u32>, k: nat) -> Seq<u32>
    decreases domain_labels(domain).len() - k,
{
    let d = domain_labels(domain);
    let trailing_dot = has_trailing_dot(domain);
    if k >= d.len() {
        domain
    } else if !is_public_suffix(rules, label_suffix(d, trailing_dot, k)) {
        label_suffix(d, trailing_dot, k)
    } else {
        cookie_root_from(rules, domain, k + 1)
    }
}

/// The cookie root of a domain: "the shortest suffix of it (in labels) that
/// is not a public suffix, or the domain itself when every suffix is a
/// public suffix".
pub open spec fn cookie_root_of_domain(rules: Seq<Rule>, domain: Seq<u32>) -> Seq<u32> {
    cookie_root_from(rules, domain, 1)
}

/// The cookie root of a host: of a domain, as above; "for an IP address,
/// the address"; an opaque host and the empty host are their own.
pub open spec fn cookie_root(rules: Seq<Rule>, host: clazel_url::host::spec::Host) -> clazel_url::host::spec::Host {
    match host {
        clazel_url::host::spec::Host::Domain(domain) => clazel_url::host::spec::Host::Domain(cookie_root_of_domain(rules, domain)),
        _ => host,
    }
}

} // verus!
