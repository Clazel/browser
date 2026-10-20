//! The standard's own examples, evaluated on the spec. Kept apart from
//! [`super::lemmas`] so that a mutant that breaks one of them does not stop
//! Verus before it checks a kill certificate there.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// RFC 4648 §10's test vectors, evaluated on the spec: "f" is "Zg==",
/// "fo" is "Zm8=", "foo" is "Zm9v", "foobar" is "Zm9vYmFy", and decode
/// takes each back. Also Infra's own note on step 9: "YQ" and "YR" both
/// return `a`.
pub proof fn lemma_examples() {
    assert(forgiving_base64_encode(seq![0x66u8]) == seq![0x5Au32, 0x67, 0x3D, 0x3D]) by (compute_only);
    assert(forgiving_base64_encode(seq![0x66u8, 0x6F]) == seq![0x5Au32, 0x6D, 0x38, 0x3D]) by (compute_only);
    assert(forgiving_base64_encode(seq![0x66u8, 0x6F, 0x6F]) == seq![0x5Au32, 0x6D, 0x39, 0x76]) by (compute_only);
    assert(forgiving_base64_encode(seq![0x66u8, 0x6F, 0x6F, 0x62, 0x61, 0x72])
        == seq![0x5Au32, 0x6D, 0x39, 0x76, 0x59, 0x6D, 0x46, 0x79]) by (compute_only);
    assert(forgiving_base64_decode(seq![0x5Au32, 0x67, 0x3D, 0x3D]) == Some(seq![0x66u8])) by (compute_only);
    assert(forgiving_base64_decode(seq![0x5Au32, 0x6D, 0x38, 0x3D]) == Some(seq![0x66u8, 0x6F])) by (compute_only);
    assert(forgiving_base64_decode(seq![0x5Au32, 0x6D, 0x39, 0x76, 0x59, 0x6D, 0x46, 0x79])
        == Some(seq![0x66u8, 0x6F, 0x6F, 0x62, 0x61, 0x72])) by (compute_only);
    assert(forgiving_base64_decode(seq![0x59u32, 0x51]) == Some(seq![0x61u8])) by (compute_only);
    assert(forgiving_base64_decode(seq![0x59u32, 0x52]) == Some(seq![0x61u8])) by (compute_only);
}

} // verus!
