//! Facts proven about the frame spec: framing is invertible and canonical,
//! and no frame is over the limit.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Decoding the frame of a payload within the limit gives the payload back.
pub proof fn lemma_decode_encode_frame(payload: Seq<u8>)
    ensures
        payload_ok(payload) ==> decode_frame(encode_frame(payload)) == Some(payload),
{
    if payload_ok(payload) {
        crate::cbor::lemmas::lemma_pow256_8();
        crate::cbor::lemmas::lemma_be_bytes_len(payload.len(), 4);
        crate::cbor::lemmas::lemma_be_value_of_be_bytes(payload.len(), 4);
        let f = encode_frame(payload);
        assert(f.subrange(0, 4) =~= be_bytes(payload.len(), 4));
        assert(f.subrange(4, f.len() as int) =~= payload);
    }
}

/// Encode inverts decode: a frame is exactly the framing of its payload, so
/// no two byte strings are the same frame, and its payload is within the
/// limit.
pub proof fn lemma_encode_decode_frame(frame: Seq<u8>)
    ensures
        match decode_frame(frame) {
            Some(payload) => payload_ok(payload) && encode_frame(payload) =~= frame,
            None => true,
        },
{
    if let Some(payload) = decode_frame(frame) {
        let h = frame.subrange(0, 4);
        crate::cbor::lemmas::lemma_be_bytes_of_be_value(h);
        assert(payload.len() == be_value(h));
        assert(frame =~= h + payload);
        assert(encode_frame(payload) =~= be_bytes(be_value(h), 4) + payload);
    }
}

/// A header announces at most the limit, and exactly the length a frame
/// with it must have (so the transport never reads beyond `MAX_FRAME`).
pub proof fn lemma_payload_length_bounded(header: Seq<u8>)
    ensures
        match payload_length(header) {
            Some(n) => n <= MAX_FRAME as nat && header.len() == 4,
            None => true,
        },
{
}

} // verus!
