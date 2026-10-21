//! The executable frame functions, proven to meet [`super::contract`].

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use crate::cbor::spec::be_bytes;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The payload length a 4-byte header announces, if it is at most
/// [`MAX_FRAME`]. The transport calls this on the first 4 bytes it reads,
/// before reading the payload.
pub fn payload_length(header: &[u8]) -> (output: Option<usize>)
    ensures
        super::contract::payload_length_ensures(
            header@,
            match output {
                Some(n) => Some(n as nat),
                None => None,
            },
        ),
{
    if header.len() != 4 {
        return None;
    }
    let value = crate::cbor::decode::read_be(header, 0, 4);
    assert(header@.subrange(0, 4) =~= header@);
    if value <= MAX_FRAME as u64 {
        // value <= MAX_FRAME, so this is exact.
        Some(value as usize)
    } else {
        None
    }
}

/// Split exactly one frame into its payload.
pub fn decode_frame(frame: &[u8]) -> (output: Option<Vec<u8>>)
    ensures
        super::contract::decode_frame_ensures(
            frame@,
            match output {
                Some(v) => Some(v@),
                None => None,
            },
        ),
{
    if frame.len() < 4 {
        return None;
    }
    let header = vstd::slice::slice_subrange(frame, 0, 4);
    let len = payload_length(header)?;
    // frame.len() >= 4, so this does not saturate.
    if frame.len().saturating_sub(4) == len {
        Some(vstd::slice::slice_to_vec(vstd::slice::slice_subrange(frame, 4, frame.len())))
    } else {
        None
    }
}

/// The frame holding `payload`; `None` if the payload is over the limit.
pub fn encode_frame(payload: &[u8]) -> (output: Option<Vec<u8>>)
    ensures
        super::contract::encode_frame_ensures(
            payload@,
            match output {
                Some(v) => Some(v@),
                None => None,
            },
        ),
{
    if payload.len() > MAX_FRAME {
        return None;
    }
    proof {
        crate::cbor::lemmas::lemma_pow256_8();
    }
    let mut out: Vec<u8> = Vec::new();
    assert((payload.len() as u64 as nat) < crate::cbor::lemmas::pow256(4nat));
    crate::cbor::encode::push_be(&mut out, payload.len() as u64, 4);
    out.extend_from_slice(payload);
    assert(out@ =~= super::spec::encode_frame(payload@)) by {
        assert(payload.len() as u64 as nat == payload@.len());
        assert(Seq::<u8>::empty() + (be_bytes(payload@.len(), 4) + payload@) =~= be_bytes(payload@.len(), 4) + payload@);
    }
    Some(out)
}

} // verus!
