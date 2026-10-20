//! Examples from WPT `url/resources/IdnaTestV2.json` and UTS #46, evaluated
//! on the spec. Kept apart from the lemmas so that a mutant that breaks
//! one of them does not stop Verus before it checks a kill certificate.

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

} // verus!
