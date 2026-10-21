//! Facts proven about the message schema: the three lemmas of item 2.2 lifted
//! to messages and frames (decode inverts encode, encode inverts decode so no
//! two byte strings are the same message, and decoding allocates no more
//! than the input), and the two schema rules.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use crate::cbor::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The tokens of a message parse back to it.
pub proof fn lemma_parse_message_tokens(m: Message)
    ensures
        parse_message(message_tokens(m)) == Some(m),
{
    let t = message_tokens(m);
    match m {
        Message::CookieGet => { assert(t.subrange(2, 2) =~= Seq::<Token>::empty()); },
        Message::StorageClear => { assert(t.subrange(2, 2) =~= Seq::<Token>::empty()); },
        Message::StorageLength => { assert(t.subrange(2, 2) =~= Seq::<Token>::empty()); },
        Message::CookieSet { cookie_string } => { assert(t.subrange(2, 3) =~= seq![Token::Text(cookie_string)]); },
        Message::StorageGetItem { key } => { assert(t.subrange(2, 3) =~= seq![Token::Text(key)]); },
        Message::StorageSetItem { key, value } => { assert(t.subrange(2, 4) =~= seq![Token::Text(key), Token::Text(value)]); },
        Message::StorageRemoveItem { key } => { assert(t.subrange(2, 3) =~= seq![Token::Text(key)]); },
        Message::StorageKey { index } => { assert(t.subrange(2, 3) =~= seq![Token::Uint(index)]); },
        Message::Navigate { url } => { assert(t.subrange(2, 3) =~= seq![Token::Text(url)]); },
        Message::Commit { url, script } => { assert(t.subrange(2, 4) =~= seq![Token::Text(url), Token::Text(script)]); },
        Message::CookieValue { cookie_string } => { assert(t.subrange(2, 3) =~= seq![Token::Text(cookie_string)]); },
        Message::StorageValue { value } => match value {
            None => { assert(t.subrange(2, 3) =~= seq![Token::Bool(false)]); },
            Some(v) => { assert(t.subrange(2, 4) =~= seq![Token::Bool(true), Token::Text(v)]); },
        },
        Message::StorageLengthValue { length } => { assert(t.subrange(2, 3) =~= seq![Token::Uint(length)]); },
        Message::Error { code } => { assert(t.subrange(2, 3) =~= seq![Token::Uint(code)]); },
    }
}

/// A token sequence that parses is the tokens of the message it parses to.
pub proof fn lemma_message_tokens_parse(t: Seq<Token>)
    ensures
        match parse_message(t) {
            Some(m) => message_tokens(m) =~= t,
            None => true,
        },
{
    if let Some(m) = parse_message(t) {
        let f = t.subrange(2, t.len() as int);
        assert(parse_fields(match t[1] { Token::Uint(tag) => tag, _ => 0 }, f) == Some(m));
        assert(f.len() + 2 == t.len());
        assert forall|i: int| 0 <= i < f.len() implies f[i] == t[i + 2] by {}
        match m {
            Message::StorageValue { value } => match value {
                None => {},
                Some(_) => {},
            },
            _ => {},
        }
        assert(message_tokens(m) =~= t);
    }
}

/// Decode inverts encode: every sendable message decodes from its bytes.
pub proof fn lemma_decode_encode_message(m: Message)
    ensures
        message_ok(m) ==> decode_message(encode_message(m)) == Some(m),
{
    if message_ok(m) {
        crate::cbor::lemmas::lemma_decode_encode(message_tokens(m));
        lemma_parse_message_tokens(m);
    }
}

/// Encode inverts decode: a message that decodes is sendable, and its
/// bytes are exactly the input. No two byte strings are the same message.
pub proof fn lemma_encode_decode_message(b: Seq<u8>)
    ensures
        match decode_message(b) {
            Some(m) => message_ok(m) && encode_message(m) =~= b,
            None => true,
        },
{
    crate::cbor::lemmas::lemma_encode_decode(b);
    if let Some(t) = decode(b) {
        lemma_message_tokens_parse(t);
    }
}

/// Two byte strings that decode to the same message are equal: no parser
/// differential between kernel and renderer.
pub proof fn lemma_decode_message_injective(a: Seq<u8>, b: Seq<u8>)
    requires
        decode_message(a) is Some,
        decode_message(a) == decode_message(b),
    ensures
        a =~= b,
{
    lemma_encode_decode_message(a);
    lemma_encode_decode_message(b);
}

/// The kernel's decoder returns only renderer-to-kernel messages.
pub proof fn lemma_renderer_decode_direction(b: Seq<u8>)
    ensures
        match decode_renderer_message(b) {
            Some(m) => is_from_renderer(m) && decode_message(b) == Some(m),
            None => true,
        },
{
}

/// A message decoded from a few bytes has few tokens: decoding allocates no
/// more than there are input bytes.
pub proof fn lemma_decode_message_alloc_bound(b: Seq<u8>)
    ensures
        match decode_message(b) {
            Some(m) => message_tokens(m).len() <= b.len(),
            None => true,
        },
{
    crate::cbor::lemmas::lemma_decode_alloc_bound(b);
    if let Some(m) = decode_message(b) {
        let t = decode(b).unwrap();
        lemma_message_tokens_parse(t);
    }
}

/// The wire shape follows the field table: an array of the tag and the
/// fields, so a message carries exactly the fields in [`message_fields`].
pub proof fn lemma_fields_match_tokens(m: Message)
    ensures
        message_tokens(m).len() == 2 + message_fields(m).len(),
        message_tokens(m)[0] == Token::Array((1 + message_fields(m).len()) as u64),
{
    match m {
        Message::StorageValue { value } => match value {
            None => {},
            Some(_) => {},
        },
        _ => {},
    }
}

/// Schema rule 1 and 2: no message, in either direction, has a field that
/// is an origin, a renderer id, a tab id or the sender's URL. The kernel
/// learns the sender from the socket, and renderer ids never reach a
/// renderer.
pub proof fn lemma_no_identity_fields(m: Message)
    ensures
        forall|i: int| 0 <= i < message_fields(m).len() ==> !is_identity(#[trigger] message_fields(m)[i]),
{
    match m {
        Message::StorageValue { value } => match value {
            None => {},
            Some(_) => {},
        },
        _ => {},
    }
}

/// A renderer-to-kernel message carries no identity and the kernel-to-
/// renderer messages carry none either, so a renderer cannot claim, or
/// learn, who anyone is, through a message.
pub proof fn lemma_no_identity_on_the_wire(m: Message)
    ensures
        forall|i: int| 0 <= i < message_fields(m).len() ==> !is_identity(#[trigger] message_fields(m)[i]),
        message_tokens(m).len() == 2 + message_fields(m).len(),
{
    lemma_no_identity_fields(m);
    lemma_fields_match_tokens(m);
}

// ---------------------------------------------------------------------------
// Frames and messages together.
// ---------------------------------------------------------------------------

/// A sendable message whose bytes fit a frame is received as itself.
pub proof fn lemma_decode_encode_framed(m: Message)
    ensures
        (message_ok(m) && crate::frame::spec::payload_ok(encode_message(m)))
            ==> decode_framed(crate::frame::spec::encode_frame(encode_message(m))) == Some(m),
{
    if message_ok(m) && crate::frame::spec::payload_ok(encode_message(m)) {
        crate::frame::lemmas::lemma_decode_encode_frame(encode_message(m));
        lemma_decode_encode_message(m);
    }
}

/// A frame that decodes to a message is exactly that message's frame.
pub proof fn lemma_encode_decode_framed(frame: Seq<u8>)
    ensures
        match decode_framed(frame) {
            Some(m) => {
                &&& message_ok(m)
                &&& crate::frame::spec::payload_ok(encode_message(m))
                &&& crate::frame::spec::encode_frame(encode_message(m)) =~= frame
            },
            None => true,
        },
{
    crate::frame::lemmas::lemma_encode_decode_frame(frame);
    if let Some(p) = crate::frame::spec::decode_frame(frame) {
        lemma_encode_decode_message(p);
    }
}

} // verus!
