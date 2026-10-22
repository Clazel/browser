//! Examples evaluated on the spec: Verus computes the spec on concrete
//! domains and a small list of rules, so a transcription error shows up here
//! as a failed proof. The list `rules()` has one rule of each kind the
//! algorithm distinguishes: `com`, `uk` and `co.uk` (plain rules of one and
//! two labels), `*.ck` (wildcard) and `!www.ck` (exception to it), which are
//! the examples of the Public Suffix List's "Format" page. They also serve
//! as the certificates of `mutations.json`.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// "a".
pub open spec fn l_a() -> Seq<u32> {
    seq![0x61u32]
}

/// "b".
pub open spec fn l_b() -> Seq<u32> {
    seq![0x62u32]
}

/// "com".
pub open spec fn l_com() -> Seq<u32> {
    seq![0x63u32, 0x6F, 0x6D]
}

/// "co".
pub open spec fn l_co() -> Seq<u32> {
    seq![0x63u32, 0x6F]
}

/// "uk".
pub open spec fn l_uk() -> Seq<u32> {
    seq![0x75u32, 0x6B]
}

/// "ck".
pub open spec fn l_ck() -> Seq<u32> {
    seq![0x63u32, 0x6B]
}

/// "www".
pub open spec fn l_www() -> Seq<u32> {
    seq![0x77u32, 0x77, 0x77]
}

/// "zz": a label no rule mentions.
pub open spec fn l_zz() -> Seq<u32> {
    seq![0x7Au32, 0x7A]
}

/// The domain with these labels, without a trailing dot.
pub open spec fn dom(labels: Seq<Seq<u32>>) -> Seq<u32> {
    labels_string(labels, false)
}

/// The domain with these labels and a trailing dot.
pub open spec fn dom_dot(labels: Seq<Seq<u32>>) -> Seq<u32> {
    labels_string(labels, true)
}

/// `com`, `uk`, `co.uk`, `*.ck`, `!www.ck`.
pub open spec fn rules() -> Seq<Rule> {
    seq![
        Rule { labels: seq![l_com()], exception: false },
        Rule { labels: seq![l_uk()], exception: false },
        Rule { labels: seq![l_co(), l_uk()], exception: false },
        Rule { labels: seq![star_label(), l_ck()], exception: false },
        Rule { labels: seq![l_www(), l_ck()], exception: true },
    ]
}

/// `co.uk` before `uk`: the same rules in the other order.
pub open spec fn rules_reversed() -> Seq<Rule> {
    seq![
        Rule { labels: seq![l_co(), l_uk()], exception: false },
        Rule { labels: seq![l_uk()], exception: false },
    ]
}

/// `*.ck` before `!www.ck`: the exception comes last.
pub open spec fn rules_wildcard_first() -> Seq<Rule> {
    seq![
        Rule { labels: seq![star_label(), l_ck()], exception: false },
        Rule { labels: seq![l_www(), l_ck()], exception: true },
    ]
}

/// `!com`: an exception rule with one label, which the real list has none
/// of (see the modelling choices).
pub open spec fn rules_single_label_exception() -> Seq<Rule> {
    seq![Rule { labels: seq![l_com()], exception: true }]
}

// ---------------------------------------------------------------------
// The public suffix.
// ---------------------------------------------------------------------

/// A plain one-label rule: `a.com` has the public suffix `com`.
pub proof fn example_public_suffix_plain()
    ensures
        public_suffix_of_domain(rules(), dom(seq![l_a(), l_com()])) == Some(dom(seq![l_com()])),
{
    assert(public_suffix_of_domain(rules(), dom(seq![l_a(), l_com()])) == Some(dom(seq![l_com()]))) by (compute_only);
}

/// The longest matching rule prevails (A4): `co.uk` beats `uk` for `a.co.uk`,
/// whichever comes first in the list.
pub proof fn example_public_suffix_longest_rule()
    ensures
        public_suffix_of_domain(rules(), dom(seq![l_a(), l_co(), l_uk()])) == Some(dom(seq![l_co(), l_uk()])),
        public_suffix_of_domain(rules_reversed(), dom(seq![l_a(), l_co(), l_uk()])) == Some(dom(seq![l_co(), l_uk()])),
{
    assert(public_suffix_of_domain(rules(), dom(seq![l_a(), l_co(), l_uk()])) == Some(dom(seq![l_co(), l_uk()]))) by (compute_only);
    assert(public_suffix_of_domain(rules_reversed(), dom(seq![l_a(), l_co(), l_uk()])) == Some(dom(seq![l_co(), l_uk()]))) by (compute_only);
}

/// A longer rule is not chosen when it does not match: `b.uk` has the public
/// suffix `uk`, not `co.uk`, which does not match it.
pub proof fn example_public_suffix_short_rule()
    ensures
        public_suffix_of_domain(rules(), dom(seq![l_b(), l_uk()])) == Some(dom(seq![l_uk()])),
        public_suffix_of_domain(rules_reversed(), dom(seq![l_b(), l_uk()])) == Some(dom(seq![l_uk()])),
{
    assert(public_suffix_of_domain(rules(), dom(seq![l_b(), l_uk()])) == Some(dom(seq![l_uk()]))) by (compute_only);
    assert(public_suffix_of_domain(rules_reversed(), dom(seq![l_b(), l_uk()])) == Some(dom(seq![l_uk()]))) by (compute_only);
}

/// A wildcard rule matches any label: `*.ck` gives `b.a.ck` the public
/// suffix `a.ck`.
pub proof fn example_public_suffix_wildcard()
    ensures
        public_suffix_of_domain(rules(), dom(seq![l_b(), l_a(), l_ck()])) == Some(dom(seq![l_a(), l_ck()])),
{
    assert(public_suffix_of_domain(rules(), dom(seq![l_b(), l_a(), l_ck()])) == Some(dom(seq![l_a(), l_ck()]))) by (compute_only);
}

/// An exception rule prevails (A3) and loses its leftmost label (A5): `!www.ck`
/// gives `www.ck` and `a.www.ck` the public suffix `ck`, although `*.ck` also
/// matches and has the same number of labels, whichever comes first.
pub proof fn example_public_suffix_exception()
    ensures
        public_suffix_of_domain(rules(), dom(seq![l_www(), l_ck()])) == Some(dom(seq![l_ck()])),
        public_suffix_of_domain(rules(), dom(seq![l_a(), l_www(), l_ck()])) == Some(dom(seq![l_ck()])),
        public_suffix_of_domain(rules_wildcard_first(), dom(seq![l_www(), l_ck()])) == Some(dom(seq![l_ck()])),
{
    assert(public_suffix_of_domain(rules(), dom(seq![l_www(), l_ck()])) == Some(dom(seq![l_ck()]))) by (compute_only);
    assert(public_suffix_of_domain(rules(), dom(seq![l_a(), l_www(), l_ck()])) == Some(dom(seq![l_ck()]))) by (compute_only);
    assert(public_suffix_of_domain(rules_wildcard_first(), dom(seq![l_www(), l_ck()])) == Some(dom(seq![l_ck()]))) by (compute_only);
}

/// If no rule matches, the prevailing rule is "*" (A2): the public suffix of
/// `a.b.zz` is `zz`, and of `zz` itself.
pub proof fn example_public_suffix_default_rule()
    ensures
        public_suffix_of_domain(rules(), dom(seq![l_a(), l_b(), l_zz()])) == Some(dom(seq![l_zz()])),
        public_suffix_of_domain(rules(), dom(seq![l_zz()])) == Some(dom(seq![l_zz()])),
        public_suffix_of_domain(seq![], dom(seq![l_a(), l_b(), l_zz()])) == Some(dom(seq![l_zz()])),
{
    assert(public_suffix_of_domain(rules(), dom(seq![l_a(), l_b(), l_zz()])) == Some(dom(seq![l_zz()]))) by (compute_only);
    assert(public_suffix_of_domain(rules(), dom(seq![l_zz()])) == Some(dom(seq![l_zz()]))) by (compute_only);
    assert(public_suffix_of_domain(seq![], dom(seq![l_a(), l_b(), l_zz()])) == Some(dom(seq![l_zz()]))) by (compute_only);
}

/// "A trailing dot shall be added if the domain included one" (A6, Note 3):
/// the public suffix of `a.com.` is `com.`.
pub proof fn example_public_suffix_trailing_dot()
    ensures
        public_suffix_of_domain(rules(), dom_dot(seq![l_a(), l_com()])) == Some(dom_dot(seq![l_com()])),
{
    assert(public_suffix_of_domain(rules(), dom_dot(seq![l_a(), l_com()])) == Some(dom_dot(seq![l_com()]))) by (compute_only);
}

/// "Empty labels are not permitted": `a..com`, `.com` and the empty string
/// have no public suffix.
pub proof fn example_public_suffix_empty_label()
    ensures
        public_suffix_of_domain(rules(), dom(seq![l_a(), seq![], l_com()])) is None,
        public_suffix_of_domain(rules(), dom(seq![seq![], l_com()])) is None,
        public_suffix_of_domain(rules(), seq![]) is None,
{
    assert(public_suffix_of_domain(rules(), dom(seq![l_a(), seq![], l_com()])) is None) by (compute_only);
    assert(public_suffix_of_domain(rules(), dom(seq![seq![], l_com()])) is None) by (compute_only);
    assert(public_suffix_of_domain(rules(), seq![]) is None) by (compute_only);
}

// ---------------------------------------------------------------------
// The registrable domain.
// ---------------------------------------------------------------------

/// "The public suffix plus one additional label" (A7).
pub proof fn example_registrable_domain()
    ensures
        registrable_domain_of_domain(rules(), dom(seq![l_a(), l_com()])) == Some(dom(seq![l_a(), l_com()])),
        registrable_domain_of_domain(rules(), dom(seq![l_b(), l_a(), l_co(), l_uk()])) == Some(dom(seq![l_a(), l_co(), l_uk()])),
        registrable_domain_of_domain(rules(), dom(seq![l_a(), l_www(), l_ck()])) == Some(dom(seq![l_www(), l_ck()])),
        registrable_domain_of_domain(rules(), dom_dot(seq![l_b(), l_a(), l_com()])) == Some(dom_dot(seq![l_a(), l_com()])),
{
    assert(registrable_domain_of_domain(rules(), dom(seq![l_a(), l_com()])) == Some(dom(seq![l_a(), l_com()]))) by (compute_only);
    assert(registrable_domain_of_domain(rules(), dom(seq![l_b(), l_a(), l_co(), l_uk()])) == Some(dom(seq![l_a(), l_co(), l_uk()]))) by (compute_only);
    assert(registrable_domain_of_domain(rules(), dom(seq![l_a(), l_www(), l_ck()])) == Some(dom(seq![l_www(), l_ck()]))) by (compute_only);
    assert(registrable_domain_of_domain(rules(), dom_dot(seq![l_b(), l_a(), l_com()])) == Some(dom_dot(seq![l_a(), l_com()]))) by (compute_only);
}

/// A public suffix has no registrable domain: not `com`, not `co.uk`, not
/// `a.ck` (a wildcard match), not the empty-label domains.
pub proof fn example_registrable_domain_of_suffix()
    ensures
        registrable_domain_of_domain(rules(), dom(seq![l_com()])) is None,
        registrable_domain_of_domain(rules(), dom(seq![l_co(), l_uk()])) is None,
        registrable_domain_of_domain(rules(), dom(seq![l_a(), l_ck()])) is None,
        registrable_domain_of_domain(rules(), dom(seq![l_zz()])) is None,
        registrable_domain_of_domain(rules(), dom(seq![seq![], l_com()])) is None,
{
    assert(registrable_domain_of_domain(rules(), dom(seq![l_com()])) is None) by (compute_only);
    assert(registrable_domain_of_domain(rules(), dom(seq![l_co(), l_uk()])) is None) by (compute_only);
    assert(registrable_domain_of_domain(rules(), dom(seq![l_a(), l_ck()])) is None) by (compute_only);
    assert(registrable_domain_of_domain(rules(), dom(seq![l_zz()])) is None) by (compute_only);
    assert(registrable_domain_of_domain(rules(), dom(seq![seq![], l_com()])) is None) by (compute_only);
}

/// Only a domain has a public suffix or a registrable domain.
pub proof fn example_not_a_domain()
    ensures
        public_suffix(rules(), clazel_url::host::spec::Host::Ipv4(1)) is None,
        registrable_domain(rules(), clazel_url::host::spec::Host::Ipv4(1)) is None,
        public_suffix(rules(), clazel_url::host::spec::Host::Opaque(dom(seq![l_a(), l_com()]))) is None,
        registrable_domain(rules(), clazel_url::host::spec::Host::Empty) is None,
        public_suffix(rules(), clazel_url::host::spec::Host::Domain(dom(seq![l_a(), l_com()]))) == Some(dom(seq![l_com()])),
        registrable_domain(rules(), clazel_url::host::spec::Host::Domain(dom(seq![l_a(), l_com()]))) == Some(dom(seq![l_a(), l_com()])),
{
    assert(public_suffix(rules(), clazel_url::host::spec::Host::Ipv4(1)) is None) by (compute_only);
    assert(registrable_domain(rules(), clazel_url::host::spec::Host::Ipv4(1)) is None) by (compute_only);
    assert(public_suffix(rules(), clazel_url::host::spec::Host::Opaque(dom(seq![l_a(), l_com()]))) is None) by (compute_only);
    assert(registrable_domain(rules(), clazel_url::host::spec::Host::Empty) is None) by (compute_only);
    assert(public_suffix(rules(), clazel_url::host::spec::Host::Domain(dom(seq![l_a(), l_com()]))) == Some(dom(seq![l_com()]))) by (compute_only);
    assert(registrable_domain(rules(), clazel_url::host::spec::Host::Domain(dom(seq![l_a(), l_com()]))) == Some(dom(seq![l_a(), l_com()]))) by (compute_only);
}

/// The last `k` labels of a domain.
pub proof fn example_label_suffix()
    ensures
        label_suffix(seq![l_a(), l_b(), l_com()], false, 2) == dom(seq![l_b(), l_com()]),
        label_suffix(seq![l_a(), l_b(), l_com()], true, 1) == dom_dot(seq![l_com()]),
        // The last two labels and the first two differ (for the proofs that
        // use them).
        dom(seq![l_b(), l_com()]) != dom(seq![l_a(), l_b()]),
{
    assert(label_suffix(seq![l_a(), l_b(), l_com()], false, 2) == dom(seq![l_b(), l_com()])) by (compute_only);
    assert(label_suffix(seq![l_a(), l_b(), l_com()], true, 1) == dom_dot(seq![l_com()])) by (compute_only);
    assert(dom(seq![l_b(), l_com()]) != dom(seq![l_a(), l_b()])) by (compute_only);
}

/// The labels of a domain, with and without a trailing dot.
pub proof fn example_domain_labels()
    ensures
        domain_labels(dom(seq![l_a(), l_com()])) == seq![l_a(), l_com()],
        domain_labels(dom_dot(seq![l_a(), l_com()])) == seq![l_a(), l_com()],
        has_trailing_dot(dom_dot(seq![l_a(), l_com()])),
        !has_trailing_dot(dom(seq![l_a(), l_com()])),
{
    assert(domain_labels(dom(seq![l_a(), l_com()])) == seq![l_a(), l_com()]) by (compute_only);
    assert(domain_labels(dom_dot(seq![l_a(), l_com()])) == seq![l_a(), l_com()]) by (compute_only);
    assert(has_trailing_dot(dom_dot(seq![l_a(), l_com()]))) by (compute_only);
    assert(!has_trailing_dot(dom(seq![l_a(), l_com()]))) by (compute_only);
}

/// An exception rule with one label would leave no label; the suffix keeps
/// one (see the modelling choices), so the label count is at least one.
pub proof fn example_single_label_exception()
    ensures
        suffix_label_count(rules_single_label_exception(), seq![l_com()]) == 1,
{
    assert(suffix_label_count(rules_single_label_exception(), seq![l_com()]) == 1nat) by (compute_only);
}

// ---------------------------------------------------------------------
// The cookie root.
// ---------------------------------------------------------------------

/// The cookie root of a registrable domain and of a name below it is the
/// registrable domain.
pub proof fn example_cookie_root_registrable()
    ensures
        cookie_root_of_domain(rules(), dom(seq![l_a(), l_com()])) == dom(seq![l_a(), l_com()]),
        cookie_root_of_domain(rules(), dom(seq![l_www(), l_a(), l_com()])) == dom(seq![l_a(), l_com()]),
        cookie_root_of_domain(rules(), dom(seq![l_b(), l_a(), l_co(), l_uk()])) == dom(seq![l_a(), l_co(), l_uk()]),
{
    assert(cookie_root_of_domain(rules(), dom(seq![l_a(), l_com()])) == dom(seq![l_a(), l_com()])) by (compute_only);
    assert(cookie_root_of_domain(rules(), dom(seq![l_www(), l_a(), l_com()])) == dom(seq![l_a(), l_com()])) by (compute_only);
    assert(cookie_root_of_domain(rules(), dom(seq![l_b(), l_a(), l_co(), l_uk()])) == dom(seq![l_a(), l_co(), l_uk()])) by (compute_only);
}

/// A domain every suffix of which is a public suffix is its own cookie root:
/// `com`, `uk`, `co.uk`.
pub proof fn example_cookie_root_public_suffix()
    ensures
        cookie_root_of_domain(rules(), dom(seq![l_com()])) == dom(seq![l_com()]),
        cookie_root_of_domain(rules(), dom(seq![l_co(), l_uk()])) == dom(seq![l_co(), l_uk()]),
        cookie_root_of_domain(rules(), dom(seq![l_zz()])) == dom(seq![l_zz()]),
{
    assert(cookie_root_of_domain(rules(), dom(seq![l_com()])) == dom(seq![l_com()])) by (compute_only);
    assert(cookie_root_of_domain(rules(), dom(seq![l_co(), l_uk()])) == dom(seq![l_co(), l_uk()])) by (compute_only);
    assert(cookie_root_of_domain(rules(), dom(seq![l_zz()])) == dom(seq![l_zz()])) by (compute_only);
}

/// Two sibling hosts below a public suffix have different cookie roots, so
/// they cannot share a cookie: `a.co.uk` and `b.co.uk`.
pub proof fn example_cookie_root_siblings()
    ensures
        cookie_root_of_domain(rules(), dom(seq![l_a(), l_co(), l_uk()])) == dom(seq![l_a(), l_co(), l_uk()]),
        cookie_root_of_domain(rules(), dom(seq![l_b(), l_co(), l_uk()])) == dom(seq![l_b(), l_co(), l_uk()]),
        cookie_root_of_domain(rules(), dom(seq![l_a(), l_uk()])) == dom(seq![l_a(), l_uk()]),
{
    assert(cookie_root_of_domain(rules(), dom(seq![l_a(), l_co(), l_uk()])) == dom(seq![l_a(), l_co(), l_uk()])) by (compute_only);
    assert(cookie_root_of_domain(rules(), dom(seq![l_b(), l_co(), l_uk()])) == dom(seq![l_b(), l_co(), l_uk()])) by (compute_only);
    assert(cookie_root_of_domain(rules(), dom(seq![l_a(), l_uk()])) == dom(seq![l_a(), l_uk()])) by (compute_only);
}

/// A wildcard public suffix: `*.ck` makes `a.ck` a public suffix, so the
/// cookie root of `b.a.ck` is `b.a.ck`; an exception makes `www.ck` an
/// ordinary domain, so its cookie root is itself, and that of `b.www.ck` is
/// `www.ck`.
pub proof fn example_cookie_root_wildcard_and_exception()
    ensures
        cookie_root_of_domain(rules(), dom(seq![l_a(), l_ck()])) == dom(seq![l_a(), l_ck()]),
        cookie_root_of_domain(rules(), dom(seq![l_b(), l_a(), l_ck()])) == dom(seq![l_b(), l_a(), l_ck()]),
        cookie_root_of_domain(rules(), dom(seq![l_www(), l_ck()])) == dom(seq![l_www(), l_ck()]),
        cookie_root_of_domain(rules(), dom(seq![l_b(), l_www(), l_ck()])) == dom(seq![l_www(), l_ck()]),
{
    assert(cookie_root_of_domain(rules(), dom(seq![l_a(), l_ck()])) == dom(seq![l_a(), l_ck()])) by (compute_only);
    assert(cookie_root_of_domain(rules(), dom(seq![l_b(), l_a(), l_ck()])) == dom(seq![l_b(), l_a(), l_ck()])) by (compute_only);
    assert(cookie_root_of_domain(rules(), dom(seq![l_www(), l_ck()])) == dom(seq![l_www(), l_ck()])) by (compute_only);
    assert(cookie_root_of_domain(rules(), dom(seq![l_b(), l_www(), l_ck()])) == dom(seq![l_www(), l_ck()])) by (compute_only);
}

/// The cookie root keeps a trailing dot, and the default rule alone makes
/// the last label a public suffix.
pub proof fn example_cookie_root_trailing_dot_and_default()
    ensures
        cookie_root_of_domain(rules(), dom_dot(seq![l_b(), l_a(), l_com()])) == dom_dot(seq![l_a(), l_com()]),
        cookie_root_of_domain(seq![], dom(seq![l_a(), l_b(), l_zz()])) == dom(seq![l_b(), l_zz()]),
{
    assert(cookie_root_of_domain(rules(), dom_dot(seq![l_b(), l_a(), l_com()])) == dom_dot(seq![l_a(), l_com()])) by (compute_only);
    assert(cookie_root_of_domain(seq![], dom(seq![l_a(), l_b(), l_zz()])) == dom(seq![l_b(), l_zz()])) by (compute_only);
}

/// Which suffixes are public suffixes.
pub proof fn example_is_public_suffix()
    ensures
        is_public_suffix(rules(), dom(seq![l_co(), l_uk()])),
        is_public_suffix(rules(), dom(seq![l_a(), l_ck()])),
        !is_public_suffix(rules(), dom(seq![l_a(), l_co(), l_uk()])),
        !is_public_suffix(rules(), dom(seq![l_www(), l_ck()])),
        !is_public_suffix(rules(), dom(seq![l_a(), l_com()])),
{
    assert(is_public_suffix(rules(), dom(seq![l_co(), l_uk()]))) by (compute_only);
    assert(is_public_suffix(rules(), dom(seq![l_a(), l_ck()]))) by (compute_only);
    assert(!is_public_suffix(rules(), dom(seq![l_a(), l_co(), l_uk()]))) by (compute_only);
    assert(!is_public_suffix(rules(), dom(seq![l_www(), l_ck()]))) by (compute_only);
    assert(!is_public_suffix(rules(), dom(seq![l_a(), l_com()]))) by (compute_only);
}

/// A host that is not a domain is its own cookie root, an IP address
/// included: two different addresses never share a root.
pub proof fn example_cookie_root_not_a_domain()
    ensures
        cookie_root(rules(), clazel_url::host::spec::Host::Ipv4(1)) == clazel_url::host::spec::Host::Ipv4(1),
        cookie_root(rules(), clazel_url::host::spec::Host::Ipv4(2)) == clazel_url::host::spec::Host::Ipv4(2),
        cookie_root(rules(), clazel_url::host::spec::Host::Opaque(dom(seq![l_a(), l_com()]))) == clazel_url::host::spec::Host::Opaque(dom(seq![l_a(), l_com()])),
        cookie_root(rules(), clazel_url::host::spec::Host::Empty) == clazel_url::host::spec::Host::Empty,
        cookie_root(rules(), clazel_url::host::spec::Host::Domain(dom(seq![l_www(), l_a(), l_com()]))) == clazel_url::host::spec::Host::Domain(dom(seq![l_a(), l_com()])),
{
    assert(cookie_root(rules(), clazel_url::host::spec::Host::Ipv4(1)) == clazel_url::host::spec::Host::Ipv4(1)) by (compute_only);
    assert(cookie_root(rules(), clazel_url::host::spec::Host::Ipv4(2)) == clazel_url::host::spec::Host::Ipv4(2)) by (compute_only);
    assert(cookie_root(rules(), clazel_url::host::spec::Host::Opaque(dom(seq![l_a(), l_com()]))) == clazel_url::host::spec::Host::Opaque(dom(seq![l_a(), l_com()]))) by (compute_only);
    assert(cookie_root(rules(), clazel_url::host::spec::Host::Empty) == clazel_url::host::spec::Host::Empty) by (compute_only);
    assert(cookie_root(rules(), clazel_url::host::spec::Host::Domain(dom(seq![l_www(), l_a(), l_com()]))) == clazel_url::host::spec::Host::Domain(dom(seq![l_a(), l_com()]))) by (compute_only);
}

} // verus!
