//! Concrete messages and frames, evaluated on the spec. Kept apart from
//! [`super::lemmas`] so that a mutant that breaks one of them does not stop
//! Verus before it checks a kill certificate there.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// `CookieGet` is `[1]`.
pub proof fn lemma_example_cookie_get()
    ensures
        decode_message(seq![0x81u8, 0x01]) == Some(Message::CookieGet),
        encode_message(Message::CookieGet) == seq![0x81u8, 0x01],
{
    assert(decode_message(seq![0x81u8, 0x01]) == Some(Message::CookieGet)) by (compute_only);
    assert(encode_message(Message::CookieGet) == seq![0x81u8, 0x01]) by (compute_only);
}

/// `CookieSet("a=b")` is `[2, "a=b"]`.
pub proof fn lemma_example_cookie_set()
    ensures
        decode_message(seq![0x82u8, 0x02, 0x63, 0x61, 0x3D, 0x62]) == Some(Message::CookieSet { cookie_string: seq![0x61u8, 0x3D, 0x62] }),
        encode_message(Message::CookieSet { cookie_string: seq![0x61u8, 0x3D, 0x62] }) == seq![0x82u8, 0x02, 0x63, 0x61, 0x3D, 0x62],
{
    assert(decode_message(seq![0x82u8, 0x02, 0x63, 0x61, 0x3D, 0x62]) == Some(Message::CookieSet { cookie_string: seq![0x61u8, 0x3D, 0x62] })) by (compute_only);
    assert(encode_message(Message::CookieSet { cookie_string: seq![0x61u8, 0x3D, 0x62] }) == seq![0x82u8, 0x02, 0x63, 0x61, 0x3D, 0x62]) by (compute_only);
}

/// `StorageSetItem("k", "v")` is `[4, "k", "v"]`.
pub proof fn lemma_example_storage_set_item()
    ensures
        decode_message(seq![0x83u8, 0x04, 0x61, 0x6B, 0x61, 0x76]) == Some(Message::StorageSetItem { key: seq![0x6Bu8], value: seq![0x76u8] }),
        encode_message(Message::StorageSetItem { key: seq![0x6Bu8], value: seq![0x76u8] }) == seq![0x83u8, 0x04, 0x61, 0x6B, 0x61, 0x76],
{
    assert(decode_message(seq![0x83u8, 0x04, 0x61, 0x6B, 0x61, 0x76]) == Some(Message::StorageSetItem { key: seq![0x6Bu8], value: seq![0x76u8] })) by (compute_only);
    assert(encode_message(Message::StorageSetItem { key: seq![0x6Bu8], value: seq![0x76u8] }) == seq![0x83u8, 0x04, 0x61, 0x6B, 0x61, 0x76]) by (compute_only);
}

/// `StorageKey(7)` is `[7, 7]`.
pub proof fn lemma_example_storage_key()
    ensures
        decode_message(seq![0x82u8, 0x07, 0x07]) == Some(Message::StorageKey { index: 7 }),
        encode_message(Message::StorageKey { index: 7 }) == seq![0x82u8, 0x07, 0x07],
{
    assert(decode_message(seq![0x82u8, 0x07, 0x07]) == Some(Message::StorageKey { index: 7 })) by (compute_only);
    assert(encode_message(Message::StorageKey { index: 7 }) == seq![0x82u8, 0x07, 0x07]) by (compute_only);
}

/// `Navigate("x")` is `[9, "x"]`.
pub proof fn lemma_example_navigate()
    ensures
        decode_message(seq![0x82u8, 0x09, 0x61, 0x78]) == Some(Message::Navigate { url: seq![0x78u8] }),
        encode_message(Message::Navigate { url: seq![0x78u8] }) == seq![0x82u8, 0x09, 0x61, 0x78],
{
    assert(decode_message(seq![0x82u8, 0x09, 0x61, 0x78]) == Some(Message::Navigate { url: seq![0x78u8] })) by (compute_only);
    assert(encode_message(Message::Navigate { url: seq![0x78u8] }) == seq![0x82u8, 0x09, 0x61, 0x78]) by (compute_only);
}

/// `StorageValue(absent)` is `[103, false]`; `StorageValue("v")` is
/// `[103, true, "v"]`.
pub proof fn lemma_example_storage_value()
    ensures
        decode_message(seq![0x82u8, 0x18, 0x67, 0xF4]) == Some(Message::StorageValue { value: None }),
        decode_message(seq![0x83u8, 0x18, 0x67, 0xF5, 0x61, 0x76]) == Some(Message::StorageValue { value: Some(seq![0x76u8]) }),
        encode_message(Message::StorageValue { value: None }) == seq![0x82u8, 0x18, 0x67, 0xF4],
{
    assert(decode_message(seq![0x82u8, 0x18, 0x67, 0xF4]) == Some(Message::StorageValue { value: None })) by (compute_only);
    assert(decode_message(seq![0x83u8, 0x18, 0x67, 0xF5, 0x61, 0x76]) == Some(Message::StorageValue { value: Some(seq![0x76u8]) })) by (compute_only);
    assert(encode_message(Message::StorageValue { value: None }) == seq![0x82u8, 0x18, 0x67, 0xF4]) by (compute_only);
}

/// `Error(5)` is `[105, 5]`.
pub proof fn lemma_example_error()
    ensures
        decode_message(seq![0x82u8, 0x18, 0x69, 0x05]) == Some(Message::Error { code: 5 }),
        encode_message(Message::Error { code: 5 }) == seq![0x82u8, 0x18, 0x69, 0x05],
{
    assert(decode_message(seq![0x82u8, 0x18, 0x69, 0x05]) == Some(Message::Error { code: 5 })) by (compute_only);
    assert(encode_message(Message::Error { code: 5 }) == seq![0x82u8, 0x18, 0x69, 0x05]) by (compute_only);
}

/// An unknown tag is rejected.
pub proof fn lemma_reject_unknown_tag()
    ensures
        decode_message(seq![0x81u8, 0x0A]) is None,
{
    assert(decode_message(seq![0x81u8, 0x0A]) is None) by (compute_only);
}

/// A tag with the wrong fields is rejected: `Navigate` with a number.
pub proof fn lemma_reject_wrong_field_type()
    ensures
        decode_message(seq![0x82u8, 0x09, 0x01]) is None,
{
    assert(decode_message(seq![0x82u8, 0x09, 0x01]) is None) by (compute_only);
}

/// A tag with an extra field is rejected: `CookieGet` with a field.
pub proof fn lemma_reject_extra_field()
    ensures
        decode_message(seq![0x82u8, 0x01, 0x01]) is None,
{
    assert(decode_message(seq![0x82u8, 0x01, 0x01]) is None) by (compute_only);
}

/// A message that is not an array is rejected.
pub proof fn lemma_reject_not_an_array()
    ensures
        decode_message(seq![0x01u8]) is None,
{
    assert(decode_message(seq![0x01u8]) is None) by (compute_only);
}

/// The kernel's decoder rejects a kernel-to-renderer message: `Error(5)`.
pub proof fn lemma_reject_wrong_direction()
    ensures
        decode_renderer_message(seq![0x82u8, 0x18, 0x69, 0x05]) is None,
        decode_renderer_message(seq![0x81u8, 0x01]) == Some(Message::CookieGet),
{
    assert(decode_renderer_message(seq![0x82u8, 0x18, 0x69, 0x05]) is None) by (compute_only);
    assert(decode_renderer_message(seq![0x81u8, 0x01]) == Some(Message::CookieGet)) by (compute_only);
}

/// The kernel's decoder accepts a renderer-to-kernel message: `Navigate`.
pub proof fn lemma_example_renderer_navigate()
    ensures
        decode_renderer_message(seq![0x82u8, 0x09, 0x61, 0x78]) == Some(Message::Navigate { url: seq![0x78u8] }),
{
    assert(decode_renderer_message(seq![0x82u8, 0x09, 0x61, 0x78]) == Some(Message::Navigate { url: seq![0x78u8] })) by (compute_only);
}

/// A frame: length 2, then `CookieGet`.
pub proof fn lemma_example_frame()
    ensures
        decode_framed(seq![0x00u8, 0x00, 0x00, 0x02, 0x81, 0x01]) == Some(Message::CookieGet),
{
    assert(decode_framed(seq![0x00u8, 0x00, 0x00, 0x02, 0x81, 0x01]) == Some(Message::CookieGet)) by (compute_only);
}

/// A frame whose header announces more than `MAX_FRAME` is rejected, as is
/// one whose length does not match.
pub proof fn lemma_reject_frames()
    ensures
        decode_framed(seq![0x00u8, 0x10, 0x00, 0x01, 0x81, 0x01]) is None,
        decode_framed(seq![0x00u8, 0x00, 0x00, 0x03, 0x81, 0x01]) is None,
        decode_framed(seq![0x00u8, 0x00, 0x00, 0x01, 0x81, 0x01]) is None,
        decode_framed(seq![0x00u8, 0x00, 0x00]) is None,
{
    assert(decode_framed(seq![0x00u8, 0x10, 0x00, 0x01, 0x81, 0x01]) is None) by (compute_only);
    assert(decode_framed(seq![0x00u8, 0x00, 0x00, 0x03, 0x81, 0x01]) is None) by (compute_only);
    assert(decode_framed(seq![0x00u8, 0x00, 0x00, 0x01, 0x81, 0x01]) is None) by (compute_only);
    assert(decode_framed(seq![0x00u8, 0x00, 0x00]) is None) by (compute_only);
}

} // verus!
