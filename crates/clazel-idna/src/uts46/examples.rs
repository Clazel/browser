//! Examples evaluated on the spec: WPT rows, and inputs chosen to
//! exercise each step of UTS #46 processing and the domain parser. Each is
//! a theorem about the spec, proven by evaluation; the mutation tests use
//! them as kill certificates. Kept apart from the other lemmas so that a
//! mutant that breaks one of them does not stop Verus before it checks a
//! certificate.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The first rows of WPT's IdnaTestV2.json (domain parser ToASCII, not
/// strict).
pub proof fn lemma_idna_test_v2_examples() {
    reveal(super::data::IDNA_MAPPING_0);
    reveal(super::data::IDNA_MAPPING_1);
    reveal(super::data::IDNA_MAPPING_2);
    reveal(super::data::IDNA_MAPPING_3);
    reveal(super::data::IDNA_MAPPING_4);
    reveal(super::data::IDNA_MAPPING_5);
    reveal(super::data::IDNA_MAPPING_6);
    reveal(super::data::IDNA_MAPPING_7);
    reveal(super::data::IDNA_MAPPING_8);
    reveal(super::data::IDNA_MAPPING_9);
    reveal(super::data::IDNA_MAPPING_10);
    reveal(super::data::IDNA_MAPPING_11);
    reveal(super::data::IDNA_MAPPING_DATA_0);
    reveal(super::data::IDNA_MAPPING_DATA_1);
    reveal(super::data::IDNA_MAPPING_DATA_2);
    reveal(super::data::DECOMPOSITION_0);
    reveal(super::data::DECOMPOSITION_1);
    reveal(super::data::DECOMPOSITION_DATA_0);
    reveal(super::data::COMPOSITION_0);
    reveal(super::data::COMBINING_CLASS_0);
    reveal(super::data::MARK_0);
    reveal(super::data::BIDI_CLASS_0);
    reveal(super::data::JOINING_TYPE_0);
    assert(domain_parser_to_ascii(seq![0x66u32, 0x61u32, 0x73u32, 0x73u32, 0x2Eu32, 0x64u32, 0x65u32], false) == Some(seq![0x66u32, 0x61u32, 0x73u32, 0x73u32, 0x2Eu32, 0x64u32, 0x65u32])) by (compute_only);
    assert(domain_parser_to_ascii(seq![0x66u32, 0x61u32, 0xDFu32, 0x2Eu32, 0x64u32, 0x65u32], false) == Some(seq![0x78u32, 0x6Eu32, 0x2Du32, 0x2Du32, 0x66u32, 0x61u32, 0x2Du32, 0x68u32, 0x69u32, 0x61u32, 0x2Eu32, 0x64u32, 0x65u32])) by (compute_only);
    assert(domain_parser_to_ascii(seq![0x46u32, 0x61u32, 0xDFu32, 0x2Eu32, 0x64u32, 0x65u32], false) == Some(seq![0x78u32, 0x6Eu32, 0x2Du32, 0x2Du32, 0x66u32, 0x61u32, 0x2Du32, 0x68u32, 0x69u32, 0x61u32, 0x2Eu32, 0x64u32, 0x65u32])) by (compute_only);
    assert(domain_parser_to_ascii(seq![0x78u32, 0x6Eu32, 0x2Du32, 0x2Du32, 0x66u32, 0x61u32, 0x2Du32, 0x68u32, 0x69u32, 0x61u32, 0x2Eu32, 0x64u32, 0x65u32], false) == Some(seq![0x78u32, 0x6Eu32, 0x2Du32, 0x2Du32, 0x66u32, 0x61u32, 0x2Du32, 0x68u32, 0x69u32, 0x61u32, 0x2Eu32, 0x64u32, 0x65u32])) by (compute_only);
    assert(domain_parser_to_ascii(seq![0xE0u32, 0x2Eu32, 0x5D0u32, 0x308u32], false) == Some(seq![0x78u32, 0x6Eu32, 0x2Du32, 0x2Du32, 0x30u32, 0x63u32, 0x61u32, 0x2Eu32, 0x78u32, 0x6Eu32, 0x2Du32, 0x2Du32, 0x73u32, 0x73u32, 0x61u32, 0x37u32, 0x33u32, 0x6Cu32])) by (compute_only);
    assert(domain_parser_to_ascii(seq![0x61u32, 0x300u32, 0x2Eu32, 0x5D0u32, 0x308u32], false) == Some(seq![0x78u32, 0x6Eu32, 0x2Du32, 0x2Du32, 0x30u32, 0x63u32, 0x61u32, 0x2Eu32, 0x78u32, 0x6Eu32, 0x2Du32, 0x2Du32, 0x73u32, 0x73u32, 0x61u32, 0x37u32, 0x33u32, 0x6Cu32])) by (compute_only);
}

/// domain parser ToASCII("a\xadb", beStrict false) is "ab".
pub proof fn example_ignored()
    ensures
        domain_parser_to_ascii(seq![0x61u32, 0xADu32, 0x62u32], false) == Some(seq![0x61u32, 0x62u32]),
{
    reveal(super::data::IDNA_MAPPING_0);
    reveal(super::data::IDNA_MAPPING_1);
    reveal(super::data::IDNA_MAPPING_2);
    reveal(super::data::IDNA_MAPPING_3);
    reveal(super::data::IDNA_MAPPING_4);
    reveal(super::data::IDNA_MAPPING_5);
    reveal(super::data::IDNA_MAPPING_6);
    reveal(super::data::IDNA_MAPPING_7);
    reveal(super::data::IDNA_MAPPING_8);
    reveal(super::data::IDNA_MAPPING_9);
    reveal(super::data::IDNA_MAPPING_10);
    reveal(super::data::IDNA_MAPPING_11);
    reveal(super::data::IDNA_MAPPING_DATA_0);
    reveal(super::data::IDNA_MAPPING_DATA_1);
    reveal(super::data::IDNA_MAPPING_DATA_2);
    reveal(super::data::DECOMPOSITION_0);
    reveal(super::data::DECOMPOSITION_1);
    reveal(super::data::DECOMPOSITION_DATA_0);
    reveal(super::data::COMPOSITION_0);
    reveal(super::data::COMBINING_CLASS_0);
    reveal(super::data::MARK_0);
    reveal(super::data::BIDI_CLASS_0);
    reveal(super::data::JOINING_TYPE_0);
    assert(domain_parser_to_ascii(seq![0x61u32, 0xADu32, 0x62u32], false) == Some(seq![0x61u32, 0x62u32])) by (compute_only);
}

/// domain parser ToASCII("A", beStrict false) is "a".
pub proof fn example_mapped()
    ensures
        domain_parser_to_ascii(seq![0x41u32], false) == Some(seq![0x61u32]),
{
    reveal(super::data::IDNA_MAPPING_0);
    reveal(super::data::IDNA_MAPPING_1);
    reveal(super::data::IDNA_MAPPING_2);
    reveal(super::data::IDNA_MAPPING_3);
    reveal(super::data::IDNA_MAPPING_4);
    reveal(super::data::IDNA_MAPPING_5);
    reveal(super::data::IDNA_MAPPING_6);
    reveal(super::data::IDNA_MAPPING_7);
    reveal(super::data::IDNA_MAPPING_8);
    reveal(super::data::IDNA_MAPPING_9);
    reveal(super::data::IDNA_MAPPING_10);
    reveal(super::data::IDNA_MAPPING_11);
    reveal(super::data::IDNA_MAPPING_DATA_0);
    reveal(super::data::IDNA_MAPPING_DATA_1);
    reveal(super::data::IDNA_MAPPING_DATA_2);
    reveal(super::data::DECOMPOSITION_0);
    reveal(super::data::DECOMPOSITION_1);
    reveal(super::data::DECOMPOSITION_DATA_0);
    reveal(super::data::COMPOSITION_0);
    reveal(super::data::COMBINING_CLASS_0);
    reveal(super::data::MARK_0);
    reveal(super::data::BIDI_CLASS_0);
    reveal(super::data::JOINING_TYPE_0);
    assert(domain_parser_to_ascii(seq![0x41u32], false) == Some(seq![0x61u32])) by (compute_only);
}

/// domain parser ToASCII("fa\xdf", beStrict false) is "xn--fa-hia".
pub proof fn example_deviation()
    ensures
        domain_parser_to_ascii(seq![0x66u32, 0x61u32, 0xDFu32], false) == Some(seq![0x78u32, 0x6Eu32, 0x2Du32, 0x2Du32, 0x66u32, 0x61u32, 0x2Du32, 0x68u32, 0x69u32, 0x61u32]),
{
    reveal(super::data::IDNA_MAPPING_0);
    reveal(super::data::IDNA_MAPPING_1);
    reveal(super::data::IDNA_MAPPING_2);
    reveal(super::data::IDNA_MAPPING_3);
    reveal(super::data::IDNA_MAPPING_4);
    reveal(super::data::IDNA_MAPPING_5);
    reveal(super::data::IDNA_MAPPING_6);
    reveal(super::data::IDNA_MAPPING_7);
    reveal(super::data::IDNA_MAPPING_8);
    reveal(super::data::IDNA_MAPPING_9);
    reveal(super::data::IDNA_MAPPING_10);
    reveal(super::data::IDNA_MAPPING_11);
    reveal(super::data::IDNA_MAPPING_DATA_0);
    reveal(super::data::IDNA_MAPPING_DATA_1);
    reveal(super::data::IDNA_MAPPING_DATA_2);
    reveal(super::data::DECOMPOSITION_0);
    reveal(super::data::DECOMPOSITION_1);
    reveal(super::data::DECOMPOSITION_DATA_0);
    reveal(super::data::COMPOSITION_0);
    reveal(super::data::COMBINING_CLASS_0);
    reveal(super::data::MARK_0);
    reveal(super::data::BIDI_CLASS_0);
    reveal(super::data::JOINING_TYPE_0);
    assert(domain_parser_to_ascii(seq![0x66u32, 0x61u32, 0xDFu32], false) == Some(seq![0x78u32, 0x6Eu32, 0x2Du32, 0x2Du32, 0x66u32, 0x61u32, 0x2Du32, 0x68u32, 0x69u32, 0x61u32])) by (compute_only);
}

/// domain parser ToASCII("a\u0300", beStrict false) is "xn--0ca".
pub proof fn example_normalize()
    ensures
        domain_parser_to_ascii(seq![0x61u32, 0x300u32], false) == Some(seq![0x78u32, 0x6Eu32, 0x2Du32, 0x2Du32, 0x30u32, 0x63u32, 0x61u32]),
{
    reveal(super::data::IDNA_MAPPING_0);
    reveal(super::data::IDNA_MAPPING_1);
    reveal(super::data::IDNA_MAPPING_2);
    reveal(super::data::IDNA_MAPPING_3);
    reveal(super::data::IDNA_MAPPING_4);
    reveal(super::data::IDNA_MAPPING_5);
    reveal(super::data::IDNA_MAPPING_6);
    reveal(super::data::IDNA_MAPPING_7);
    reveal(super::data::IDNA_MAPPING_8);
    reveal(super::data::IDNA_MAPPING_9);
    reveal(super::data::IDNA_MAPPING_10);
    reveal(super::data::IDNA_MAPPING_11);
    reveal(super::data::IDNA_MAPPING_DATA_0);
    reveal(super::data::IDNA_MAPPING_DATA_1);
    reveal(super::data::IDNA_MAPPING_DATA_2);
    reveal(super::data::DECOMPOSITION_0);
    reveal(super::data::DECOMPOSITION_1);
    reveal(super::data::DECOMPOSITION_DATA_0);
    reveal(super::data::COMPOSITION_0);
    reveal(super::data::COMBINING_CLASS_0);
    reveal(super::data::MARK_0);
    reveal(super::data::BIDI_CLASS_0);
    reveal(super::data::JOINING_TYPE_0);
    assert(domain_parser_to_ascii(seq![0x61u32, 0x300u32], false) == Some(seq![0x78u32, 0x6Eu32, 0x2Du32, 0x2Du32, 0x30u32, 0x63u32, 0x61u32])) by (compute_only);
}

/// domain parser ToASCII("xn--a", beStrict false) is failure.
pub proof fn example_xn_prefix()
    ensures
        domain_parser_to_ascii(seq![0x78u32, 0x6Eu32, 0x2Du32, 0x2Du32, 0x61u32], false) is None,
{
    reveal(super::data::IDNA_MAPPING_0);
    reveal(super::data::IDNA_MAPPING_1);
    reveal(super::data::IDNA_MAPPING_2);
    reveal(super::data::IDNA_MAPPING_3);
    reveal(super::data::IDNA_MAPPING_4);
    reveal(super::data::IDNA_MAPPING_5);
    reveal(super::data::IDNA_MAPPING_6);
    reveal(super::data::IDNA_MAPPING_7);
    reveal(super::data::IDNA_MAPPING_8);
    reveal(super::data::IDNA_MAPPING_9);
    reveal(super::data::IDNA_MAPPING_10);
    reveal(super::data::IDNA_MAPPING_11);
    reveal(super::data::IDNA_MAPPING_DATA_0);
    reveal(super::data::IDNA_MAPPING_DATA_1);
    reveal(super::data::IDNA_MAPPING_DATA_2);
    reveal(super::data::DECOMPOSITION_0);
    reveal(super::data::DECOMPOSITION_1);
    reveal(super::data::DECOMPOSITION_DATA_0);
    reveal(super::data::COMPOSITION_0);
    reveal(super::data::COMBINING_CLASS_0);
    reveal(super::data::MARK_0);
    reveal(super::data::BIDI_CLASS_0);
    reveal(super::data::JOINING_TYPE_0);
    assert(domain_parser_to_ascii(seq![0x78u32, 0x6Eu32, 0x2Du32, 0x2Du32, 0x61u32], false) is None) by (compute_only);
}

/// domain parser ToASCII("xn--\xe9", beStrict false) is failure.
pub proof fn example_xn_non_ascii()
    ensures
        domain_parser_to_ascii(seq![0x78u32, 0x6Eu32, 0x2Du32, 0x2Du32, 0xE9u32], false) is None,
{
    reveal(super::data::IDNA_MAPPING_0);
    reveal(super::data::IDNA_MAPPING_1);
    reveal(super::data::IDNA_MAPPING_2);
    reveal(super::data::IDNA_MAPPING_3);
    reveal(super::data::IDNA_MAPPING_4);
    reveal(super::data::IDNA_MAPPING_5);
    reveal(super::data::IDNA_MAPPING_6);
    reveal(super::data::IDNA_MAPPING_7);
    reveal(super::data::IDNA_MAPPING_8);
    reveal(super::data::IDNA_MAPPING_9);
    reveal(super::data::IDNA_MAPPING_10);
    reveal(super::data::IDNA_MAPPING_11);
    reveal(super::data::IDNA_MAPPING_DATA_0);
    reveal(super::data::IDNA_MAPPING_DATA_1);
    reveal(super::data::IDNA_MAPPING_DATA_2);
    reveal(super::data::DECOMPOSITION_0);
    reveal(super::data::DECOMPOSITION_1);
    reveal(super::data::DECOMPOSITION_DATA_0);
    reveal(super::data::COMPOSITION_0);
    reveal(super::data::COMBINING_CLASS_0);
    reveal(super::data::MARK_0);
    reveal(super::data::BIDI_CLASS_0);
    reveal(super::data::JOINING_TYPE_0);
    assert(domain_parser_to_ascii(seq![0x78u32, 0x6Eu32, 0x2Du32, 0x2Du32, 0xE9u32], false) is None) by (compute_only);
}

/// domain parser ToASCII("xn--abc-", beStrict false) is failure.
pub proof fn example_ascii_decoded()
    ensures
        domain_parser_to_ascii(seq![0x78u32, 0x6Eu32, 0x2Du32, 0x2Du32, 0x61u32, 0x62u32, 0x63u32, 0x2Du32], false) is None,
{
    reveal(super::data::IDNA_MAPPING_0);
    reveal(super::data::IDNA_MAPPING_1);
    reveal(super::data::IDNA_MAPPING_2);
    reveal(super::data::IDNA_MAPPING_3);
    reveal(super::data::IDNA_MAPPING_4);
    reveal(super::data::IDNA_MAPPING_5);
    reveal(super::data::IDNA_MAPPING_6);
    reveal(super::data::IDNA_MAPPING_7);
    reveal(super::data::IDNA_MAPPING_8);
    reveal(super::data::IDNA_MAPPING_9);
    reveal(super::data::IDNA_MAPPING_10);
    reveal(super::data::IDNA_MAPPING_11);
    reveal(super::data::IDNA_MAPPING_DATA_0);
    reveal(super::data::IDNA_MAPPING_DATA_1);
    reveal(super::data::IDNA_MAPPING_DATA_2);
    reveal(super::data::DECOMPOSITION_0);
    reveal(super::data::DECOMPOSITION_1);
    reveal(super::data::DECOMPOSITION_DATA_0);
    reveal(super::data::COMPOSITION_0);
    reveal(super::data::COMBINING_CLASS_0);
    reveal(super::data::MARK_0);
    reveal(super::data::BIDI_CLASS_0);
    reveal(super::data::JOINING_TYPE_0);
    assert(domain_parser_to_ascii(seq![0x78u32, 0x6Eu32, 0x2Du32, 0x2Du32, 0x61u32, 0x62u32, 0x63u32, 0x2Du32], false) is None) by (compute_only);
}

/// domain parser ToASCII("xn--fa-hia", beStrict false) is "xn--fa-hia".
pub proof fn example_xn_rest()
    ensures
        domain_parser_to_ascii(seq![0x78u32, 0x6Eu32, 0x2Du32, 0x2Du32, 0x66u32, 0x61u32, 0x2Du32, 0x68u32, 0x69u32, 0x61u32], false) == Some(seq![0x78u32, 0x6Eu32, 0x2Du32, 0x2Du32, 0x66u32, 0x61u32, 0x2Du32, 0x68u32, 0x69u32, 0x61u32]),
{
    reveal(super::data::IDNA_MAPPING_0);
    reveal(super::data::IDNA_MAPPING_1);
    reveal(super::data::IDNA_MAPPING_2);
    reveal(super::data::IDNA_MAPPING_3);
    reveal(super::data::IDNA_MAPPING_4);
    reveal(super::data::IDNA_MAPPING_5);
    reveal(super::data::IDNA_MAPPING_6);
    reveal(super::data::IDNA_MAPPING_7);
    reveal(super::data::IDNA_MAPPING_8);
    reveal(super::data::IDNA_MAPPING_9);
    reveal(super::data::IDNA_MAPPING_10);
    reveal(super::data::IDNA_MAPPING_11);
    reveal(super::data::IDNA_MAPPING_DATA_0);
    reveal(super::data::IDNA_MAPPING_DATA_1);
    reveal(super::data::IDNA_MAPPING_DATA_2);
    reveal(super::data::DECOMPOSITION_0);
    reveal(super::data::DECOMPOSITION_1);
    reveal(super::data::DECOMPOSITION_DATA_0);
    reveal(super::data::COMPOSITION_0);
    reveal(super::data::COMBINING_CLASS_0);
    reveal(super::data::MARK_0);
    reveal(super::data::BIDI_CLASS_0);
    reveal(super::data::JOINING_TYPE_0);
    assert(domain_parser_to_ascii(seq![0x78u32, 0x6Eu32, 0x2Du32, 0x2Du32, 0x66u32, 0x61u32, 0x2Du32, 0x68u32, 0x69u32, 0x61u32], false) == Some(seq![0x78u32, 0x6Eu32, 0x2Du32, 0x2Du32, 0x66u32, 0x61u32, 0x2Du32, 0x68u32, 0x69u32, 0x61u32])) by (compute_only);
}

/// domain parser ToASCII("a.\u0661", beStrict false) is failure.
pub proof fn example_bidi_domain_an()
    ensures
        domain_parser_to_ascii(seq![0x61u32, 0x2Eu32, 0x661u32], false) is None,
{
    reveal(super::data::IDNA_MAPPING_0);
    reveal(super::data::IDNA_MAPPING_1);
    reveal(super::data::IDNA_MAPPING_2);
    reveal(super::data::IDNA_MAPPING_3);
    reveal(super::data::IDNA_MAPPING_4);
    reveal(super::data::IDNA_MAPPING_5);
    reveal(super::data::IDNA_MAPPING_6);
    reveal(super::data::IDNA_MAPPING_7);
    reveal(super::data::IDNA_MAPPING_8);
    reveal(super::data::IDNA_MAPPING_9);
    reveal(super::data::IDNA_MAPPING_10);
    reveal(super::data::IDNA_MAPPING_11);
    reveal(super::data::IDNA_MAPPING_DATA_0);
    reveal(super::data::IDNA_MAPPING_DATA_1);
    reveal(super::data::IDNA_MAPPING_DATA_2);
    reveal(super::data::DECOMPOSITION_0);
    reveal(super::data::DECOMPOSITION_1);
    reveal(super::data::DECOMPOSITION_DATA_0);
    reveal(super::data::COMPOSITION_0);
    reveal(super::data::COMBINING_CLASS_0);
    reveal(super::data::MARK_0);
    reveal(super::data::BIDI_CLASS_0);
    reveal(super::data::JOINING_TYPE_0);
    assert(domain_parser_to_ascii(seq![0x61u32, 0x2Eu32, 0x661u32], false) is None) by (compute_only);
}

/// domain parser ToASCII("\u05d0+\u05d1", beStrict false) is "xn--+-zhce".
pub proof fn example_rtl_es()
    ensures
        domain_parser_to_ascii(seq![0x5D0u32, 0x2Bu32, 0x5D1u32], false) == Some(seq![0x78u32, 0x6Eu32, 0x2Du32, 0x2Du32, 0x2Bu32, 0x2Du32, 0x7Au32, 0x68u32, 0x63u32, 0x65u32]),
{
    reveal(super::data::IDNA_MAPPING_0);
    reveal(super::data::IDNA_MAPPING_1);
    reveal(super::data::IDNA_MAPPING_2);
    reveal(super::data::IDNA_MAPPING_3);
    reveal(super::data::IDNA_MAPPING_4);
    reveal(super::data::IDNA_MAPPING_5);
    reveal(super::data::IDNA_MAPPING_6);
    reveal(super::data::IDNA_MAPPING_7);
    reveal(super::data::IDNA_MAPPING_8);
    reveal(super::data::IDNA_MAPPING_9);
    reveal(super::data::IDNA_MAPPING_10);
    reveal(super::data::IDNA_MAPPING_11);
    reveal(super::data::IDNA_MAPPING_DATA_0);
    reveal(super::data::IDNA_MAPPING_DATA_1);
    reveal(super::data::IDNA_MAPPING_DATA_2);
    reveal(super::data::DECOMPOSITION_0);
    reveal(super::data::DECOMPOSITION_1);
    reveal(super::data::DECOMPOSITION_DATA_0);
    reveal(super::data::COMPOSITION_0);
    reveal(super::data::COMBINING_CLASS_0);
    reveal(super::data::MARK_0);
    reveal(super::data::BIDI_CLASS_0);
    reveal(super::data::JOINING_TYPE_0);
    assert(domain_parser_to_ascii(seq![0x5D0u32, 0x2Bu32, 0x5D1u32], false) == Some(seq![0x78u32, 0x6Eu32, 0x2Du32, 0x2Du32, 0x2Bu32, 0x2Du32, 0x7Au32, 0x68u32, 0x63u32, 0x65u32])) by (compute_only);
}

/// domain parser ToASCII("a\u0308\u0301.\u05d0", beStrict false) is "xn--4ca69h.xn--4db".
pub proof fn example_ltr_nsm()
    ensures
        domain_parser_to_ascii(seq![0x61u32, 0x308u32, 0x301u32, 0x2Eu32, 0x5D0u32], false) == Some(seq![0x78u32, 0x6Eu32, 0x2Du32, 0x2Du32, 0x34u32, 0x63u32, 0x61u32, 0x36u32, 0x39u32, 0x68u32, 0x2Eu32, 0x78u32, 0x6Eu32, 0x2Du32, 0x2Du32, 0x34u32, 0x64u32, 0x62u32]),
{
    reveal(super::data::IDNA_MAPPING_0);
    reveal(super::data::IDNA_MAPPING_1);
    reveal(super::data::IDNA_MAPPING_2);
    reveal(super::data::IDNA_MAPPING_3);
    reveal(super::data::IDNA_MAPPING_4);
    reveal(super::data::IDNA_MAPPING_5);
    reveal(super::data::IDNA_MAPPING_6);
    reveal(super::data::IDNA_MAPPING_7);
    reveal(super::data::IDNA_MAPPING_8);
    reveal(super::data::IDNA_MAPPING_9);
    reveal(super::data::IDNA_MAPPING_10);
    reveal(super::data::IDNA_MAPPING_11);
    reveal(super::data::IDNA_MAPPING_DATA_0);
    reveal(super::data::IDNA_MAPPING_DATA_1);
    reveal(super::data::IDNA_MAPPING_DATA_2);
    reveal(super::data::DECOMPOSITION_0);
    reveal(super::data::DECOMPOSITION_1);
    reveal(super::data::DECOMPOSITION_DATA_0);
    reveal(super::data::COMPOSITION_0);
    reveal(super::data::COMBINING_CLASS_0);
    reveal(super::data::MARK_0);
    reveal(super::data::BIDI_CLASS_0);
    reveal(super::data::JOINING_TYPE_0);
    assert(domain_parser_to_ascii(seq![0x61u32, 0x308u32, 0x301u32, 0x2Eu32, 0x5D0u32], false) == Some(seq![0x78u32, 0x6Eu32, 0x2Du32, 0x2Du32, 0x34u32, 0x63u32, 0x61u32, 0x36u32, 0x39u32, 0x68u32, 0x2Eu32, 0x78u32, 0x6Eu32, 0x2Du32, 0x2Du32, 0x34u32, 0x64u32, 0x62u32])) by (compute_only);
}

/// domain parser ToASCII("\u05d01", beStrict false) is "xn--1-zhc".
pub proof fn example_rtl_ends_en()
    ensures
        domain_parser_to_ascii(seq![0x5D0u32, 0x31u32], false) == Some(seq![0x78u32, 0x6Eu32, 0x2Du32, 0x2Du32, 0x31u32, 0x2Du32, 0x7Au32, 0x68u32, 0x63u32]),
{
    reveal(super::data::IDNA_MAPPING_0);
    reveal(super::data::IDNA_MAPPING_1);
    reveal(super::data::IDNA_MAPPING_2);
    reveal(super::data::IDNA_MAPPING_3);
    reveal(super::data::IDNA_MAPPING_4);
    reveal(super::data::IDNA_MAPPING_5);
    reveal(super::data::IDNA_MAPPING_6);
    reveal(super::data::IDNA_MAPPING_7);
    reveal(super::data::IDNA_MAPPING_8);
    reveal(super::data::IDNA_MAPPING_9);
    reveal(super::data::IDNA_MAPPING_10);
    reveal(super::data::IDNA_MAPPING_11);
    reveal(super::data::IDNA_MAPPING_DATA_0);
    reveal(super::data::IDNA_MAPPING_DATA_1);
    reveal(super::data::IDNA_MAPPING_DATA_2);
    reveal(super::data::DECOMPOSITION_0);
    reveal(super::data::DECOMPOSITION_1);
    reveal(super::data::DECOMPOSITION_DATA_0);
    reveal(super::data::COMPOSITION_0);
    reveal(super::data::COMBINING_CLASS_0);
    reveal(super::data::MARK_0);
    reveal(super::data::BIDI_CLASS_0);
    reveal(super::data::JOINING_TYPE_0);
    assert(domain_parser_to_ascii(seq![0x5D0u32, 0x31u32], false) == Some(seq![0x78u32, 0x6Eu32, 0x2Du32, 0x2Du32, 0x31u32, 0x2Du32, 0x7Au32, 0x68u32, 0x63u32])) by (compute_only);
}

/// domain parser ToASCII("\u05d01\u0661", beStrict false) is failure.
pub proof fn example_rtl_en_an()
    ensures
        domain_parser_to_ascii(seq![0x5D0u32, 0x31u32, 0x661u32], false) is None,
{
    reveal(super::data::IDNA_MAPPING_0);
    reveal(super::data::IDNA_MAPPING_1);
    reveal(super::data::IDNA_MAPPING_2);
    reveal(super::data::IDNA_MAPPING_3);
    reveal(super::data::IDNA_MAPPING_4);
    reveal(super::data::IDNA_MAPPING_5);
    reveal(super::data::IDNA_MAPPING_6);
    reveal(super::data::IDNA_MAPPING_7);
    reveal(super::data::IDNA_MAPPING_8);
    reveal(super::data::IDNA_MAPPING_9);
    reveal(super::data::IDNA_MAPPING_10);
    reveal(super::data::IDNA_MAPPING_11);
    reveal(super::data::IDNA_MAPPING_DATA_0);
    reveal(super::data::IDNA_MAPPING_DATA_1);
    reveal(super::data::IDNA_MAPPING_DATA_2);
    reveal(super::data::DECOMPOSITION_0);
    reveal(super::data::DECOMPOSITION_1);
    reveal(super::data::DECOMPOSITION_DATA_0);
    reveal(super::data::COMPOSITION_0);
    reveal(super::data::COMBINING_CLASS_0);
    reveal(super::data::MARK_0);
    reveal(super::data::BIDI_CLASS_0);
    reveal(super::data::JOINING_TYPE_0);
    assert(domain_parser_to_ascii(seq![0x5D0u32, 0x31u32, 0x661u32], false) is None) by (compute_only);
}

/// domain parser ToASCII("\u0628", beStrict false) is "xn--ngb".
pub proof fn example_first_al()
    ensures
        domain_parser_to_ascii(seq![0x628u32], false) == Some(seq![0x78u32, 0x6Eu32, 0x2Du32, 0x2Du32, 0x6Eu32, 0x67u32, 0x62u32]),
{
    reveal(super::data::IDNA_MAPPING_0);
    reveal(super::data::IDNA_MAPPING_1);
    reveal(super::data::IDNA_MAPPING_2);
    reveal(super::data::IDNA_MAPPING_3);
    reveal(super::data::IDNA_MAPPING_4);
    reveal(super::data::IDNA_MAPPING_5);
    reveal(super::data::IDNA_MAPPING_6);
    reveal(super::data::IDNA_MAPPING_7);
    reveal(super::data::IDNA_MAPPING_8);
    reveal(super::data::IDNA_MAPPING_9);
    reveal(super::data::IDNA_MAPPING_10);
    reveal(super::data::IDNA_MAPPING_11);
    reveal(super::data::IDNA_MAPPING_DATA_0);
    reveal(super::data::IDNA_MAPPING_DATA_1);
    reveal(super::data::IDNA_MAPPING_DATA_2);
    reveal(super::data::DECOMPOSITION_0);
    reveal(super::data::DECOMPOSITION_1);
    reveal(super::data::DECOMPOSITION_DATA_0);
    reveal(super::data::COMPOSITION_0);
    reveal(super::data::COMBINING_CLASS_0);
    reveal(super::data::MARK_0);
    reveal(super::data::BIDI_CLASS_0);
    reveal(super::data::JOINING_TYPE_0);
    assert(domain_parser_to_ascii(seq![0x628u32], false) == Some(seq![0x78u32, 0x6Eu32, 0x2Du32, 0x2Du32, 0x6Eu32, 0x67u32, 0x62u32])) by (compute_only);
}

/// domain parser ToASCII("\u0915\u094d\u200d\u0937", beStrict false) is "xn--11b2ezcw70k".
pub proof fn example_virama()
    ensures
        domain_parser_to_ascii(seq![0x915u32, 0x94Du32, 0x200Du32, 0x937u32], false) == Some(seq![0x78u32, 0x6Eu32, 0x2Du32, 0x2Du32, 0x31u32, 0x31u32, 0x62u32, 0x32u32, 0x65u32, 0x7Au32, 0x63u32, 0x77u32, 0x37u32, 0x30u32, 0x6Bu32]),
{
    reveal(super::data::IDNA_MAPPING_0);
    reveal(super::data::IDNA_MAPPING_1);
    reveal(super::data::IDNA_MAPPING_2);
    reveal(super::data::IDNA_MAPPING_3);
    reveal(super::data::IDNA_MAPPING_4);
    reveal(super::data::IDNA_MAPPING_5);
    reveal(super::data::IDNA_MAPPING_6);
    reveal(super::data::IDNA_MAPPING_7);
    reveal(super::data::IDNA_MAPPING_8);
    reveal(super::data::IDNA_MAPPING_9);
    reveal(super::data::IDNA_MAPPING_10);
    reveal(super::data::IDNA_MAPPING_11);
    reveal(super::data::IDNA_MAPPING_DATA_0);
    reveal(super::data::IDNA_MAPPING_DATA_1);
    reveal(super::data::IDNA_MAPPING_DATA_2);
    reveal(super::data::DECOMPOSITION_0);
    reveal(super::data::DECOMPOSITION_1);
    reveal(super::data::DECOMPOSITION_DATA_0);
    reveal(super::data::COMPOSITION_0);
    reveal(super::data::COMBINING_CLASS_0);
    reveal(super::data::MARK_0);
    reveal(super::data::BIDI_CLASS_0);
    reveal(super::data::JOINING_TYPE_0);
    assert(domain_parser_to_ascii(seq![0x915u32, 0x94Du32, 0x200Du32, 0x937u32], false) == Some(seq![0x78u32, 0x6Eu32, 0x2Du32, 0x2Du32, 0x31u32, 0x31u32, 0x62u32, 0x32u32, 0x65u32, 0x7Au32, 0x63u32, 0x77u32, 0x37u32, 0x30u32, 0x6Bu32])) by (compute_only);
}

/// domain parser ToASCII("\u062f\u200c\u0628", beStrict false) is failure.
pub proof fn example_joins_left()
    ensures
        domain_parser_to_ascii(seq![0x62Fu32, 0x200Cu32, 0x628u32], false) is None,
{
    reveal(super::data::IDNA_MAPPING_0);
    reveal(super::data::IDNA_MAPPING_1);
    reveal(super::data::IDNA_MAPPING_2);
    reveal(super::data::IDNA_MAPPING_3);
    reveal(super::data::IDNA_MAPPING_4);
    reveal(super::data::IDNA_MAPPING_5);
    reveal(super::data::IDNA_MAPPING_6);
    reveal(super::data::IDNA_MAPPING_7);
    reveal(super::data::IDNA_MAPPING_8);
    reveal(super::data::IDNA_MAPPING_9);
    reveal(super::data::IDNA_MAPPING_10);
    reveal(super::data::IDNA_MAPPING_11);
    reveal(super::data::IDNA_MAPPING_DATA_0);
    reveal(super::data::IDNA_MAPPING_DATA_1);
    reveal(super::data::IDNA_MAPPING_DATA_2);
    reveal(super::data::DECOMPOSITION_0);
    reveal(super::data::DECOMPOSITION_1);
    reveal(super::data::DECOMPOSITION_DATA_0);
    reveal(super::data::COMPOSITION_0);
    reveal(super::data::COMBINING_CLASS_0);
    reveal(super::data::MARK_0);
    reveal(super::data::BIDI_CLASS_0);
    reveal(super::data::JOINING_TYPE_0);
    assert(domain_parser_to_ascii(seq![0x62Fu32, 0x200Cu32, 0x628u32], false) is None) by (compute_only);
}

/// domain parser ToASCII("a\u200db", beStrict false) is failure.
pub proof fn example_zwj()
    ensures
        domain_parser_to_ascii(seq![0x61u32, 0x200Du32, 0x62u32], false) is None,
{
    reveal(super::data::IDNA_MAPPING_0);
    reveal(super::data::IDNA_MAPPING_1);
    reveal(super::data::IDNA_MAPPING_2);
    reveal(super::data::IDNA_MAPPING_3);
    reveal(super::data::IDNA_MAPPING_4);
    reveal(super::data::IDNA_MAPPING_5);
    reveal(super::data::IDNA_MAPPING_6);
    reveal(super::data::IDNA_MAPPING_7);
    reveal(super::data::IDNA_MAPPING_8);
    reveal(super::data::IDNA_MAPPING_9);
    reveal(super::data::IDNA_MAPPING_10);
    reveal(super::data::IDNA_MAPPING_11);
    reveal(super::data::IDNA_MAPPING_DATA_0);
    reveal(super::data::IDNA_MAPPING_DATA_1);
    reveal(super::data::IDNA_MAPPING_DATA_2);
    reveal(super::data::DECOMPOSITION_0);
    reveal(super::data::DECOMPOSITION_1);
    reveal(super::data::DECOMPOSITION_DATA_0);
    reveal(super::data::COMPOSITION_0);
    reveal(super::data::COMBINING_CLASS_0);
    reveal(super::data::MARK_0);
    reveal(super::data::BIDI_CLASS_0);
    reveal(super::data::JOINING_TYPE_0);
    assert(domain_parser_to_ascii(seq![0x61u32, 0x200Du32, 0x62u32], false) is None) by (compute_only);
}

/// domain parser ToASCII("xn--a-vbb", beStrict false) is failure.
pub proof fn example_nfc_check()
    ensures
        domain_parser_to_ascii(seq![0x78u32, 0x6Eu32, 0x2Du32, 0x2Du32, 0x61u32, 0x2Du32, 0x76u32, 0x62u32, 0x62u32], false) is None,
{
    reveal(super::data::IDNA_MAPPING_0);
    reveal(super::data::IDNA_MAPPING_1);
    reveal(super::data::IDNA_MAPPING_2);
    reveal(super::data::IDNA_MAPPING_3);
    reveal(super::data::IDNA_MAPPING_4);
    reveal(super::data::IDNA_MAPPING_5);
    reveal(super::data::IDNA_MAPPING_6);
    reveal(super::data::IDNA_MAPPING_7);
    reveal(super::data::IDNA_MAPPING_8);
    reveal(super::data::IDNA_MAPPING_9);
    reveal(super::data::IDNA_MAPPING_10);
    reveal(super::data::IDNA_MAPPING_11);
    reveal(super::data::IDNA_MAPPING_DATA_0);
    reveal(super::data::IDNA_MAPPING_DATA_1);
    reveal(super::data::IDNA_MAPPING_DATA_2);
    reveal(super::data::DECOMPOSITION_0);
    reveal(super::data::DECOMPOSITION_1);
    reveal(super::data::DECOMPOSITION_DATA_0);
    reveal(super::data::COMPOSITION_0);
    reveal(super::data::COMBINING_CLASS_0);
    reveal(super::data::MARK_0);
    reveal(super::data::BIDI_CLASS_0);
    reveal(super::data::JOINING_TYPE_0);
    assert(domain_parser_to_ascii(seq![0x78u32, 0x6Eu32, 0x2Du32, 0x2Du32, 0x61u32, 0x2Du32, 0x76u32, 0x62u32, 0x62u32], false) is None) by (compute_only);
}

/// domain parser ToASCII("ab--c", beStrict true) is failure.
pub proof fn example_hyphen_34()
    ensures
        domain_parser_to_ascii(seq![0x61u32, 0x62u32, 0x2Du32, 0x2Du32, 0x63u32], true) is None,
{
    reveal(super::data::IDNA_MAPPING_0);
    reveal(super::data::IDNA_MAPPING_1);
    reveal(super::data::IDNA_MAPPING_2);
    reveal(super::data::IDNA_MAPPING_3);
    reveal(super::data::IDNA_MAPPING_4);
    reveal(super::data::IDNA_MAPPING_5);
    reveal(super::data::IDNA_MAPPING_6);
    reveal(super::data::IDNA_MAPPING_7);
    reveal(super::data::IDNA_MAPPING_8);
    reveal(super::data::IDNA_MAPPING_9);
    reveal(super::data::IDNA_MAPPING_10);
    reveal(super::data::IDNA_MAPPING_11);
    reveal(super::data::IDNA_MAPPING_DATA_0);
    reveal(super::data::IDNA_MAPPING_DATA_1);
    reveal(super::data::IDNA_MAPPING_DATA_2);
    reveal(super::data::DECOMPOSITION_0);
    reveal(super::data::DECOMPOSITION_1);
    reveal(super::data::DECOMPOSITION_DATA_0);
    reveal(super::data::COMPOSITION_0);
    reveal(super::data::COMBINING_CLASS_0);
    reveal(super::data::MARK_0);
    reveal(super::data::BIDI_CLASS_0);
    reveal(super::data::JOINING_TYPE_0);
    assert(domain_parser_to_ascii(seq![0x61u32, 0x62u32, 0x2Du32, 0x2Du32, 0x63u32], true) is None) by (compute_only);
}

/// domain parser ToASCII("-a", beStrict true) is failure.
pub proof fn example_hyphen_start()
    ensures
        domain_parser_to_ascii(seq![0x2Du32, 0x61u32], true) is None,
{
    reveal(super::data::IDNA_MAPPING_0);
    reveal(super::data::IDNA_MAPPING_1);
    reveal(super::data::IDNA_MAPPING_2);
    reveal(super::data::IDNA_MAPPING_3);
    reveal(super::data::IDNA_MAPPING_4);
    reveal(super::data::IDNA_MAPPING_5);
    reveal(super::data::IDNA_MAPPING_6);
    reveal(super::data::IDNA_MAPPING_7);
    reveal(super::data::IDNA_MAPPING_8);
    reveal(super::data::IDNA_MAPPING_9);
    reveal(super::data::IDNA_MAPPING_10);
    reveal(super::data::IDNA_MAPPING_11);
    reveal(super::data::IDNA_MAPPING_DATA_0);
    reveal(super::data::IDNA_MAPPING_DATA_1);
    reveal(super::data::IDNA_MAPPING_DATA_2);
    reveal(super::data::DECOMPOSITION_0);
    reveal(super::data::DECOMPOSITION_1);
    reveal(super::data::DECOMPOSITION_DATA_0);
    reveal(super::data::COMPOSITION_0);
    reveal(super::data::COMBINING_CLASS_0);
    reveal(super::data::MARK_0);
    reveal(super::data::BIDI_CLASS_0);
    reveal(super::data::JOINING_TYPE_0);
    assert(domain_parser_to_ascii(seq![0x2Du32, 0x61u32], true) is None) by (compute_only);
}

/// domain parser ToASCII("xn--xn---3ra", beStrict false) is failure.
pub proof fn example_xn_check()
    ensures
        domain_parser_to_ascii(seq![0x78u32, 0x6Eu32, 0x2Du32, 0x2Du32, 0x78u32, 0x6Eu32, 0x2Du32, 0x2Du32, 0x2Du32, 0x33u32, 0x72u32, 0x61u32], false) is None,
{
    reveal(super::data::IDNA_MAPPING_0);
    reveal(super::data::IDNA_MAPPING_1);
    reveal(super::data::IDNA_MAPPING_2);
    reveal(super::data::IDNA_MAPPING_3);
    reveal(super::data::IDNA_MAPPING_4);
    reveal(super::data::IDNA_MAPPING_5);
    reveal(super::data::IDNA_MAPPING_6);
    reveal(super::data::IDNA_MAPPING_7);
    reveal(super::data::IDNA_MAPPING_8);
    reveal(super::data::IDNA_MAPPING_9);
    reveal(super::data::IDNA_MAPPING_10);
    reveal(super::data::IDNA_MAPPING_11);
    reveal(super::data::IDNA_MAPPING_DATA_0);
    reveal(super::data::IDNA_MAPPING_DATA_1);
    reveal(super::data::IDNA_MAPPING_DATA_2);
    reveal(super::data::DECOMPOSITION_0);
    reveal(super::data::DECOMPOSITION_1);
    reveal(super::data::DECOMPOSITION_DATA_0);
    reveal(super::data::COMPOSITION_0);
    reveal(super::data::COMBINING_CLASS_0);
    reveal(super::data::MARK_0);
    reveal(super::data::BIDI_CLASS_0);
    reveal(super::data::JOINING_TYPE_0);
    assert(domain_parser_to_ascii(seq![0x78u32, 0x6Eu32, 0x2Du32, 0x2Du32, 0x78u32, 0x6Eu32, 0x2Du32, 0x2Du32, 0x2Du32, 0x33u32, 0x72u32, 0x61u32], false) is None) by (compute_only);
}

/// domain parser ToASCII("\u0300a", beStrict false) is failure.
pub proof fn example_mark_first()
    ensures
        domain_parser_to_ascii(seq![0x300u32, 0x61u32], false) is None,
{
    reveal(super::data::IDNA_MAPPING_0);
    reveal(super::data::IDNA_MAPPING_1);
    reveal(super::data::IDNA_MAPPING_2);
    reveal(super::data::IDNA_MAPPING_3);
    reveal(super::data::IDNA_MAPPING_4);
    reveal(super::data::IDNA_MAPPING_5);
    reveal(super::data::IDNA_MAPPING_6);
    reveal(super::data::IDNA_MAPPING_7);
    reveal(super::data::IDNA_MAPPING_8);
    reveal(super::data::IDNA_MAPPING_9);
    reveal(super::data::IDNA_MAPPING_10);
    reveal(super::data::IDNA_MAPPING_11);
    reveal(super::data::IDNA_MAPPING_DATA_0);
    reveal(super::data::IDNA_MAPPING_DATA_1);
    reveal(super::data::IDNA_MAPPING_DATA_2);
    reveal(super::data::DECOMPOSITION_0);
    reveal(super::data::DECOMPOSITION_1);
    reveal(super::data::DECOMPOSITION_DATA_0);
    reveal(super::data::COMPOSITION_0);
    reveal(super::data::COMBINING_CLASS_0);
    reveal(super::data::MARK_0);
    reveal(super::data::BIDI_CLASS_0);
    reveal(super::data::JOINING_TYPE_0);
    assert(domain_parser_to_ascii(seq![0x300u32, 0x61u32], false) is None) by (compute_only);
}

/// domain parser ToASCII("a-b", beStrict true) is "a-b".
pub proof fn example_std3_hyphen()
    ensures
        domain_parser_to_ascii(seq![0x61u32, 0x2Du32, 0x62u32], true) == Some(seq![0x61u32, 0x2Du32, 0x62u32]),
{
    reveal(super::data::IDNA_MAPPING_0);
    reveal(super::data::IDNA_MAPPING_1);
    reveal(super::data::IDNA_MAPPING_2);
    reveal(super::data::IDNA_MAPPING_3);
    reveal(super::data::IDNA_MAPPING_4);
    reveal(super::data::IDNA_MAPPING_5);
    reveal(super::data::IDNA_MAPPING_6);
    reveal(super::data::IDNA_MAPPING_7);
    reveal(super::data::IDNA_MAPPING_8);
    reveal(super::data::IDNA_MAPPING_9);
    reveal(super::data::IDNA_MAPPING_10);
    reveal(super::data::IDNA_MAPPING_11);
    reveal(super::data::IDNA_MAPPING_DATA_0);
    reveal(super::data::IDNA_MAPPING_DATA_1);
    reveal(super::data::IDNA_MAPPING_DATA_2);
    reveal(super::data::DECOMPOSITION_0);
    reveal(super::data::DECOMPOSITION_1);
    reveal(super::data::DECOMPOSITION_DATA_0);
    reveal(super::data::COMPOSITION_0);
    reveal(super::data::COMBINING_CLASS_0);
    reveal(super::data::MARK_0);
    reveal(super::data::BIDI_CLASS_0);
    reveal(super::data::JOINING_TYPE_0);
    assert(domain_parser_to_ascii(seq![0x61u32, 0x2Du32, 0x62u32], true) == Some(seq![0x61u32, 0x2Du32, 0x62u32])) by (compute_only);
}

/// domain parser ToASCII("a\u0301\u0300", beStrict false) is "xn--1ca00i".
pub proof fn example_order_stable()
    ensures
        domain_parser_to_ascii(seq![0x61u32, 0x301u32, 0x300u32], false) == Some(seq![0x78u32, 0x6Eu32, 0x2Du32, 0x2Du32, 0x31u32, 0x63u32, 0x61u32, 0x30u32, 0x30u32, 0x69u32]),
{
    reveal(super::data::IDNA_MAPPING_0);
    reveal(super::data::IDNA_MAPPING_1);
    reveal(super::data::IDNA_MAPPING_2);
    reveal(super::data::IDNA_MAPPING_3);
    reveal(super::data::IDNA_MAPPING_4);
    reveal(super::data::IDNA_MAPPING_5);
    reveal(super::data::IDNA_MAPPING_6);
    reveal(super::data::IDNA_MAPPING_7);
    reveal(super::data::IDNA_MAPPING_8);
    reveal(super::data::IDNA_MAPPING_9);
    reveal(super::data::IDNA_MAPPING_10);
    reveal(super::data::IDNA_MAPPING_11);
    reveal(super::data::IDNA_MAPPING_DATA_0);
    reveal(super::data::IDNA_MAPPING_DATA_1);
    reveal(super::data::IDNA_MAPPING_DATA_2);
    reveal(super::data::DECOMPOSITION_0);
    reveal(super::data::DECOMPOSITION_1);
    reveal(super::data::DECOMPOSITION_DATA_0);
    reveal(super::data::COMPOSITION_0);
    reveal(super::data::COMBINING_CLASS_0);
    reveal(super::data::MARK_0);
    reveal(super::data::BIDI_CLASS_0);
    reveal(super::data::JOINING_TYPE_0);
    assert(domain_parser_to_ascii(seq![0x61u32, 0x301u32, 0x300u32], false) == Some(seq![0x78u32, 0x6Eu32, 0x2Du32, 0x2Du32, 0x31u32, 0x63u32, 0x61u32, 0x30u32, 0x30u32, 0x69u32])) by (compute_only);
}

/// domain parser ToASCII("a\u0352\u0301", beStrict false) is "xn--a-xbb6v".
pub proof fn example_blocked()
    ensures
        domain_parser_to_ascii(seq![0x61u32, 0x352u32, 0x301u32], false) == Some(seq![0x78u32, 0x6Eu32, 0x2Du32, 0x2Du32, 0x61u32, 0x2Du32, 0x78u32, 0x62u32, 0x62u32, 0x36u32, 0x76u32]),
{
    reveal(super::data::IDNA_MAPPING_0);
    reveal(super::data::IDNA_MAPPING_1);
    reveal(super::data::IDNA_MAPPING_2);
    reveal(super::data::IDNA_MAPPING_3);
    reveal(super::data::IDNA_MAPPING_4);
    reveal(super::data::IDNA_MAPPING_5);
    reveal(super::data::IDNA_MAPPING_6);
    reveal(super::data::IDNA_MAPPING_7);
    reveal(super::data::IDNA_MAPPING_8);
    reveal(super::data::IDNA_MAPPING_9);
    reveal(super::data::IDNA_MAPPING_10);
    reveal(super::data::IDNA_MAPPING_11);
    reveal(super::data::IDNA_MAPPING_DATA_0);
    reveal(super::data::IDNA_MAPPING_DATA_1);
    reveal(super::data::IDNA_MAPPING_DATA_2);
    reveal(super::data::DECOMPOSITION_0);
    reveal(super::data::DECOMPOSITION_1);
    reveal(super::data::DECOMPOSITION_DATA_0);
    reveal(super::data::COMPOSITION_0);
    reveal(super::data::COMBINING_CLASS_0);
    reveal(super::data::MARK_0);
    reveal(super::data::BIDI_CLASS_0);
    reveal(super::data::JOINING_TYPE_0);
    assert(domain_parser_to_ascii(seq![0x61u32, 0x352u32, 0x301u32], false) == Some(seq![0x78u32, 0x6Eu32, 0x2Du32, 0x2Du32, 0x61u32, 0x2Du32, 0x78u32, 0x62u32, 0x62u32, 0x36u32, 0x76u32])) by (compute_only);
}

/// domain parser ToASCII("\uac00\u11a7", beStrict false) is "xn--qud9310f".
pub proof fn example_hangul_t()
    ensures
        domain_parser_to_ascii(seq![0xAC00u32, 0x11A7u32], false) == Some(seq![0x78u32, 0x6Eu32, 0x2Du32, 0x2Du32, 0x71u32, 0x75u32, 0x64u32, 0x39u32, 0x33u32, 0x31u32, 0x30u32, 0x66u32]),
{
    reveal(super::data::IDNA_MAPPING_0);
    reveal(super::data::IDNA_MAPPING_1);
    reveal(super::data::IDNA_MAPPING_2);
    reveal(super::data::IDNA_MAPPING_3);
    reveal(super::data::IDNA_MAPPING_4);
    reveal(super::data::IDNA_MAPPING_5);
    reveal(super::data::IDNA_MAPPING_6);
    reveal(super::data::IDNA_MAPPING_7);
    reveal(super::data::IDNA_MAPPING_8);
    reveal(super::data::IDNA_MAPPING_9);
    reveal(super::data::IDNA_MAPPING_10);
    reveal(super::data::IDNA_MAPPING_11);
    reveal(super::data::IDNA_MAPPING_DATA_0);
    reveal(super::data::IDNA_MAPPING_DATA_1);
    reveal(super::data::IDNA_MAPPING_DATA_2);
    reveal(super::data::DECOMPOSITION_0);
    reveal(super::data::DECOMPOSITION_1);
    reveal(super::data::DECOMPOSITION_DATA_0);
    reveal(super::data::COMPOSITION_0);
    reveal(super::data::COMBINING_CLASS_0);
    reveal(super::data::MARK_0);
    reveal(super::data::BIDI_CLASS_0);
    reveal(super::data::JOINING_TYPE_0);
    assert(domain_parser_to_ascii(seq![0xAC00u32, 0x11A7u32], false) == Some(seq![0x78u32, 0x6Eu32, 0x2Du32, 0x2Du32, 0x71u32, 0x75u32, 0x64u32, 0x39u32, 0x33u32, 0x31u32, 0x30u32, 0x66u32])) by (compute_only);
}

/// domain parser ToASCII("\xfc", beStrict false) is "xn--tda".
pub proof fn example_prefix()
    ensures
        domain_parser_to_ascii(seq![0xFCu32], false) == Some(seq![0x78u32, 0x6Eu32, 0x2Du32, 0x2Du32, 0x74u32, 0x64u32, 0x61u32]),
{
    reveal(super::data::IDNA_MAPPING_0);
    reveal(super::data::IDNA_MAPPING_1);
    reveal(super::data::IDNA_MAPPING_2);
    reveal(super::data::IDNA_MAPPING_3);
    reveal(super::data::IDNA_MAPPING_4);
    reveal(super::data::IDNA_MAPPING_5);
    reveal(super::data::IDNA_MAPPING_6);
    reveal(super::data::IDNA_MAPPING_7);
    reveal(super::data::IDNA_MAPPING_8);
    reveal(super::data::IDNA_MAPPING_9);
    reveal(super::data::IDNA_MAPPING_10);
    reveal(super::data::IDNA_MAPPING_11);
    reveal(super::data::IDNA_MAPPING_DATA_0);
    reveal(super::data::IDNA_MAPPING_DATA_1);
    reveal(super::data::IDNA_MAPPING_DATA_2);
    reveal(super::data::DECOMPOSITION_0);
    reveal(super::data::DECOMPOSITION_1);
    reveal(super::data::DECOMPOSITION_DATA_0);
    reveal(super::data::COMPOSITION_0);
    reveal(super::data::COMBINING_CLASS_0);
    reveal(super::data::MARK_0);
    reveal(super::data::BIDI_CLASS_0);
    reveal(super::data::JOINING_TYPE_0);
    assert(domain_parser_to_ascii(seq![0xFCu32], false) == Some(seq![0x78u32, 0x6Eu32, 0x2Du32, 0x2Du32, 0x74u32, 0x64u32, 0x61u32])) by (compute_only);
}



/// domain parser("A", beStrict false) is "a".
pub proof fn example_lowercase()
    ensures
        domain_parser(seq![0x41u32], false) == Some(seq![0x61u32]),
{
    reveal(super::data::IDNA_MAPPING_0);
    reveal(super::data::IDNA_MAPPING_1);
    reveal(super::data::IDNA_MAPPING_2);
    reveal(super::data::IDNA_MAPPING_3);
    reveal(super::data::IDNA_MAPPING_4);
    reveal(super::data::IDNA_MAPPING_5);
    reveal(super::data::IDNA_MAPPING_6);
    reveal(super::data::IDNA_MAPPING_7);
    reveal(super::data::IDNA_MAPPING_8);
    reveal(super::data::IDNA_MAPPING_9);
    reveal(super::data::IDNA_MAPPING_10);
    reveal(super::data::IDNA_MAPPING_11);
    reveal(super::data::IDNA_MAPPING_DATA_0);
    reveal(super::data::IDNA_MAPPING_DATA_1);
    reveal(super::data::IDNA_MAPPING_DATA_2);
    reveal(super::data::DECOMPOSITION_0);
    reveal(super::data::DECOMPOSITION_1);
    reveal(super::data::DECOMPOSITION_DATA_0);
    reveal(super::data::COMPOSITION_0);
    reveal(super::data::COMBINING_CLASS_0);
    reveal(super::data::MARK_0);
    reveal(super::data::BIDI_CLASS_0);
    reveal(super::data::JOINING_TYPE_0);
    assert(domain_parser(seq![0x41u32], false) == Some(seq![0x61u32])) by (compute_only);
}

/// domain parser("a%b", beStrict false) is failure.
pub proof fn example_percent()
    ensures
        domain_parser(seq![0x61u32, 0x25u32, 0x62u32], false) is None,
{
    reveal(super::data::IDNA_MAPPING_0);
    reveal(super::data::IDNA_MAPPING_1);
    reveal(super::data::IDNA_MAPPING_2);
    reveal(super::data::IDNA_MAPPING_3);
    reveal(super::data::IDNA_MAPPING_4);
    reveal(super::data::IDNA_MAPPING_5);
    reveal(super::data::IDNA_MAPPING_6);
    reveal(super::data::IDNA_MAPPING_7);
    reveal(super::data::IDNA_MAPPING_8);
    reveal(super::data::IDNA_MAPPING_9);
    reveal(super::data::IDNA_MAPPING_10);
    reveal(super::data::IDNA_MAPPING_11);
    reveal(super::data::IDNA_MAPPING_DATA_0);
    reveal(super::data::IDNA_MAPPING_DATA_1);
    reveal(super::data::IDNA_MAPPING_DATA_2);
    reveal(super::data::DECOMPOSITION_0);
    reveal(super::data::DECOMPOSITION_1);
    reveal(super::data::DECOMPOSITION_DATA_0);
    reveal(super::data::COMPOSITION_0);
    reveal(super::data::COMBINING_CLASS_0);
    reveal(super::data::MARK_0);
    reveal(super::data::BIDI_CLASS_0);
    reveal(super::data::JOINING_TYPE_0);
    assert(domain_parser(seq![0x61u32, 0x25u32, 0x62u32], false) is None) by (compute_only);
}

/// domain parser("\xad", beStrict false) is failure.
pub proof fn example_empty()
    ensures
        domain_parser(seq![0xADu32], false) is None,
{
    reveal(super::data::IDNA_MAPPING_0);
    reveal(super::data::IDNA_MAPPING_1);
    reveal(super::data::IDNA_MAPPING_2);
    reveal(super::data::IDNA_MAPPING_3);
    reveal(super::data::IDNA_MAPPING_4);
    reveal(super::data::IDNA_MAPPING_5);
    reveal(super::data::IDNA_MAPPING_6);
    reveal(super::data::IDNA_MAPPING_7);
    reveal(super::data::IDNA_MAPPING_8);
    reveal(super::data::IDNA_MAPPING_9);
    reveal(super::data::IDNA_MAPPING_10);
    reveal(super::data::IDNA_MAPPING_11);
    reveal(super::data::IDNA_MAPPING_DATA_0);
    reveal(super::data::IDNA_MAPPING_DATA_1);
    reveal(super::data::IDNA_MAPPING_DATA_2);
    reveal(super::data::DECOMPOSITION_0);
    reveal(super::data::DECOMPOSITION_1);
    reveal(super::data::DECOMPOSITION_DATA_0);
    reveal(super::data::COMPOSITION_0);
    reveal(super::data::COMBINING_CLASS_0);
    reveal(super::data::MARK_0);
    reveal(super::data::BIDI_CLASS_0);
    reveal(super::data::JOINING_TYPE_0);
    assert(domain_parser(seq![0xADu32], false) is None) by (compute_only);
}

/// domain parser ToASCII("a\u05d0", beStrict false) is failure.
pub proof fn example_url_bidi()
    ensures
        domain_parser_to_ascii(seq![0x61u32, 0x5D0u32], false) is None,
{
    reveal(super::data::IDNA_MAPPING_0);
    reveal(super::data::IDNA_MAPPING_1);
    reveal(super::data::IDNA_MAPPING_2);
    reveal(super::data::IDNA_MAPPING_3);
    reveal(super::data::IDNA_MAPPING_4);
    reveal(super::data::IDNA_MAPPING_5);
    reveal(super::data::IDNA_MAPPING_6);
    reveal(super::data::IDNA_MAPPING_7);
    reveal(super::data::IDNA_MAPPING_8);
    reveal(super::data::IDNA_MAPPING_9);
    reveal(super::data::IDNA_MAPPING_10);
    reveal(super::data::IDNA_MAPPING_11);
    reveal(super::data::IDNA_MAPPING_DATA_0);
    reveal(super::data::IDNA_MAPPING_DATA_1);
    reveal(super::data::IDNA_MAPPING_DATA_2);
    reveal(super::data::DECOMPOSITION_0);
    reveal(super::data::DECOMPOSITION_1);
    reveal(super::data::DECOMPOSITION_DATA_0);
    reveal(super::data::COMPOSITION_0);
    reveal(super::data::COMBINING_CLASS_0);
    reveal(super::data::MARK_0);
    reveal(super::data::BIDI_CLASS_0);
    reveal(super::data::JOINING_TYPE_0);
    assert(domain_parser_to_ascii(seq![0x61u32, 0x5D0u32], false) is None) by (compute_only);
}

/// VerifyDnsLength: a 64-character label is too long.
pub proof fn example_dns_63()
    ensures
        !dns_length_ok(seq![seq![0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32]]),
{
    assert(!dns_length_ok(seq![seq![0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32]])) by (compute_only);
}

/// VerifyDnsLength: labels of 63, 63, 63 and 62 characters make a
/// 254-character domain, which is too long.
pub proof fn example_dns_253()
    ensures
        !dns_length_ok(seq![seq![0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32], seq![0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32], seq![0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32], seq![0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32]]),
{
    assert(!dns_length_ok(seq![seq![0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32], seq![0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32], seq![0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32], seq![0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32, 0x61u32]])) by (compute_only);
}

/// domain parser ToASCII("xn---", beStrict false) is failure: "-" is not
/// valid Punycode (a leading delimiter with nothing before it is read as
/// a digit, and has no digit-value).
pub proof fn example_bad_punycode()
    ensures
        domain_parser_to_ascii(seq![0x78u32, 0x6Eu32, 0x2Du32, 0x2Du32, 0x2Du32], false) is None,
{
    reveal(super::data::IDNA_MAPPING_0);
    reveal(super::data::IDNA_MAPPING_1);
    reveal(super::data::IDNA_MAPPING_2);
    reveal(super::data::IDNA_MAPPING_3);
    reveal(super::data::IDNA_MAPPING_4);
    reveal(super::data::IDNA_MAPPING_5);
    reveal(super::data::IDNA_MAPPING_6);
    reveal(super::data::IDNA_MAPPING_7);
    reveal(super::data::IDNA_MAPPING_8);
    reveal(super::data::IDNA_MAPPING_9);
    reveal(super::data::IDNA_MAPPING_10);
    reveal(super::data::IDNA_MAPPING_11);
    reveal(super::data::IDNA_MAPPING_DATA_0);
    reveal(super::data::IDNA_MAPPING_DATA_1);
    reveal(super::data::IDNA_MAPPING_DATA_2);
    reveal(super::data::DECOMPOSITION_0);
    reveal(super::data::DECOMPOSITION_1);
    reveal(super::data::DECOMPOSITION_DATA_0);
    reveal(super::data::COMPOSITION_0);
    reveal(super::data::COMBINING_CLASS_0);
    reveal(super::data::MARK_0);
    reveal(super::data::BIDI_CLASS_0);
    reveal(super::data::JOINING_TYPE_0);
    assert(domain_parser_to_ascii(seq![0x78u32, 0x6Eu32, 0x2Du32, 0x2Du32, 0x2Du32], false) is None) by (compute_only);
}

} // verus!
