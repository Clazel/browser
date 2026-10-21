//! Contracts the executable frame functions must be proven to meet.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Contract for `payload_length(&[u8]) -> Option<usize>`.
pub open spec fn payload_length_ensures(header: Seq<u8>, output: Option<nat>) -> bool {
    output == payload_length(header)
}

/// Contract for `decode_frame(&[u8]) -> Option<Vec<u8>>`.
pub open spec fn decode_frame_ensures(frame: Seq<u8>, output: Option<Seq<u8>>) -> bool {
    output == decode_frame(frame)
}

/// Contract for `encode_frame(&[u8]) -> Option<Vec<u8>>`: `None` exactly
/// when the payload is over the limit.
pub open spec fn encode_frame_ensures(payload: Seq<u8>, output: Option<Seq<u8>>) -> bool {
    output == if payload_ok(payload) {
        Some(encode_frame(payload))
    } else {
        None
    }
}

} // verus!
