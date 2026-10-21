//! Concrete frames, evaluated on the spec. Kept apart from
//! [`super::lemmas`] so that a mutant that breaks one of them does not stop
//! Verus before it checks a kill certificate there.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The limit is exactly 1 MiB: a header announcing 1048576 is accepted, one
/// announcing one more is not, and a header is exactly 4 bytes.
pub proof fn lemma_example_limit()
    ensures
        payload_length(seq![0x00u8, 0x10, 0x00, 0x00]) == Some(1048576nat),
        payload_length(seq![0x00u8, 0x10, 0x00, 0x01]) is None,
        payload_length(seq![0x00u8, 0x00, 0x00]) is None,
{
    assert(payload_length(seq![0x00u8, 0x10, 0x00, 0x00]) == Some(1048576nat)) by (compute_only);
    assert(payload_length(seq![0x00u8, 0x10, 0x00, 0x01]) is None) by (compute_only);
    assert(payload_length(seq![0x00u8, 0x00, 0x00]) is None) by (compute_only);
}

/// A frame of 3 bytes is `00 00 00 03` and the bytes.
pub proof fn lemma_example_frame()
    ensures
        decode_frame(seq![0x00u8, 0x00, 0x00, 0x03, 0x0A, 0x0B, 0x0C]) == Some(seq![0x0Au8, 0x0B, 0x0C]),
        encode_frame(seq![0x0Au8, 0x0B, 0x0C]) == seq![0x00u8, 0x00, 0x00, 0x03, 0x0A, 0x0B, 0x0C],
{
    assert(decode_frame(seq![0x00u8, 0x00, 0x00, 0x03, 0x0A, 0x0B, 0x0C]) == Some(seq![0x0Au8, 0x0B, 0x0C])) by (compute_only);
    assert(encode_frame(seq![0x0Au8, 0x0B, 0x0C]) == seq![0x00u8, 0x00, 0x00, 0x03, 0x0A, 0x0B, 0x0C]) by (compute_only);
}

/// Bytes after the frame, a short payload and a short header are rejected.
pub proof fn lemma_reject_frame_length()
    ensures
        decode_frame(seq![0x00u8, 0x00, 0x00, 0x00, 0x01]) is None,
        decode_frame(seq![0x00u8, 0x00, 0x00, 0x02, 0x01]) is None,
        decode_frame(seq![0x00u8, 0x00, 0x00]) is None,
{
    assert(decode_frame(seq![0x00u8, 0x00, 0x00, 0x00, 0x01]) is None) by (compute_only);
    assert(decode_frame(seq![0x00u8, 0x00, 0x00, 0x02, 0x01]) is None) by (compute_only);
    assert(decode_frame(seq![0x00u8, 0x00, 0x00]) is None) by (compute_only);
}

} // verus!
