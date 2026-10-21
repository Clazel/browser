//! Executable-style specification of IPC frames (phase-2.md item 2.3). The
//! schema is ours, not a standard's, so there is nothing to transcribe: this
//! file is the definition, and `lemmas.rs` proves its properties.
//!
//! A frame is a 4-byte big-endian length, at most [`MAX_FRAME`], followed by
//! exactly that many bytes, which are exactly one CBOR item of the profile
//! (`crate::cbor`). A byte string that is not exactly one frame is not a
//! frame: the transport reads the 4 header bytes, asks [`payload_length`]
//! how many more to read (refusing a frame above the limit before reading
//! it), then hands the whole frame to the decoder.
//!
//! Modelling choices:
//! - The length is `be_value` of the 4 header bytes (`crate::cbor::spec`,
//!   "an unsigned integer in network byte order"), written by `be_bytes`.
//! - "Failure" is `None`.

#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// [`crate::cbor::spec::be_value`].
pub open spec fn be_value(s: Seq<u8>) -> nat {
    crate::cbor::spec::be_value(s)
}

/// [`crate::cbor::spec::be_bytes`].
pub open spec fn be_bytes(value: nat, width: nat) -> Seq<u8> {
    crate::cbor::spec::be_bytes(value, width)
}

/// The largest payload a frame may carry: 1 MiB.
pub const MAX_FRAME: usize = 1_048_576;

/// The number of bytes of a frame's header.
pub const HEADER_LEN: usize = 4;

/// The payload length a frame header announces, if it is a header (4 bytes)
/// and announces at most [`MAX_FRAME`] bytes.
pub open spec fn payload_length(header: Seq<u8>) -> Option<nat> {
    if header.len() == 4 && be_value(header) <= MAX_FRAME as nat {
        Some(be_value(header))
    } else {
        None
    }
}

/// Split exactly one frame into its payload: the header announces the
/// payload's length, which is within the limit, and nothing follows it.
pub open spec fn decode_frame(frame: Seq<u8>) -> Option<Seq<u8>> {
    if frame.len() < 4 {
        None
    } else {
        match payload_length(frame.subrange(0, 4)) {
            None => None,
            Some(len) => {
                if frame.len() == 4 + len {
                    Some(frame.subrange(4, frame.len() as int))
                } else {
                    None
                }
            },
        }
    }
}

/// The frame holding `payload`: its length in 4 bytes, then the payload.
/// Only defined for payloads within the limit.
pub open spec fn encode_frame(payload: Seq<u8>) -> Seq<u8> {
    be_bytes(payload.len(), 4) + payload
}

/// Whether `payload` can be framed.
pub open spec fn payload_ok(payload: Seq<u8>) -> bool {
    payload.len() <= MAX_FRAME as nat
}

} // verus!
