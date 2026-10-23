//! The frames the kernel sends to renderers: [`crate::spec::reply_frame`],
//! [`crate::spec::error_frame`] and [`crate::spec::commit_frame`], as exec
//! functions over the IPC codec (item 2.3).

use clazel_ipc::message::codec::{Msg, encode_message};
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// A text string the profile can encode.
pub open spec fn text_ok(s: Seq<u8>) -> bool {
    clazel_ipc::cbor::spec::token_ok(clazel_ipc::cbor::spec::Token::Text(s))
}

/// One step of [`is_items`].
proof fn lemma_items_step(t: Seq<clazel_ipc::cbor::spec::Token>, p: nat)
    requires
        t.len() > 0,
        p > 0,
    ensures
        clazel_ipc::cbor::spec::is_items(t, p) == (clazel_ipc::cbor::spec::token_ok(t[0]) && clazel_ipc::cbor::spec::is_items(t.drop_first(), clazel_ipc::cbor::spec::pending_after(p, t[0]))),
{
}

/// The empty sequence of tokens.
proof fn lemma_items_empty(p: nat)
    ensures
        clazel_ipc::cbor::spec::is_items(Seq::<clazel_ipc::cbor::spec::Token>::empty(), p) == (p == 0),
{
}

/// `[Array(n), Uint(tag), t...]`, whatever the rest.
proof fn lemma_items_head(n: u64, tag: u64, rest: Seq<clazel_ipc::cbor::spec::Token>)
    requires
        n >= 1,
    ensures
        clazel_ipc::cbor::spec::is_item(seq![clazel_ipc::cbor::spec::Token::Array(n), clazel_ipc::cbor::spec::Token::Uint(tag)] + rest) == clazel_ipc::cbor::spec::is_items(rest, (n - 1) as nat),
{
    let t = seq![clazel_ipc::cbor::spec::Token::Array(n), clazel_ipc::cbor::spec::Token::Uint(tag)] + rest;
    lemma_items_step(t, 1);
    assert(t[0] == clazel_ipc::cbor::spec::Token::Array(n));
    assert(t.drop_first() =~= seq![clazel_ipc::cbor::spec::Token::Uint(tag)] + rest);
    assert(clazel_ipc::cbor::spec::pending_after(1, clazel_ipc::cbor::spec::Token::Array(n)) == n as nat);
    let t1 = seq![clazel_ipc::cbor::spec::Token::Uint(tag)] + rest;
    lemma_items_step(t1, n as nat);
    assert(t1[0] == clazel_ipc::cbor::spec::Token::Uint(tag));
    assert(t1.drop_first() =~= rest);
    assert(clazel_ipc::cbor::spec::pending_after(n as nat, clazel_ipc::cbor::spec::Token::Uint(tag)) == (n - 1) as nat);
}

/// The exact condition under which a message can be sent: every text string
/// in it is valid UTF-8 (and short enough, which any sequence is, as a `Vec`).
pub open spec fn message_texts_ok(m: clazel_ipc::message::spec::Message) -> bool {
    match m {
        clazel_ipc::message::spec::Message::CookieGet | clazel_ipc::message::spec::Message::StorageClear | clazel_ipc::message::spec::Message::StorageLength => true,
        clazel_ipc::message::spec::Message::StorageKey { .. } | clazel_ipc::message::spec::Message::StorageLengthValue { .. } | clazel_ipc::message::spec::Message::Error { .. } => true,
        clazel_ipc::message::spec::Message::CookieSet { cookie_string } | clazel_ipc::message::spec::Message::CookieValue { cookie_string } => text_ok(cookie_string),
        clazel_ipc::message::spec::Message::StorageGetItem { key } | clazel_ipc::message::spec::Message::StorageRemoveItem { key } => text_ok(key),
        clazel_ipc::message::spec::Message::StorageSetItem { key, value } => text_ok(key) && text_ok(value),
        clazel_ipc::message::spec::Message::Navigate { url } => text_ok(url),
        clazel_ipc::message::spec::Message::Commit { url, script } => text_ok(url) && text_ok(script),
        clazel_ipc::message::spec::Message::StorageValue { value } => match value {
            None => true,
            Some(v) => text_ok(v),
        },
    }
}

/// `message_ok` from the tokens after the head.
proof fn lemma_msg(m: clazel_ipc::message::spec::Message, n: u64, tag: u64, rest: Seq<clazel_ipc::cbor::spec::Token>)
    requires
        n >= 1,
        clazel_ipc::message::spec::message_tokens(m) =~= seq![clazel_ipc::cbor::spec::Token::Array(n), clazel_ipc::cbor::spec::Token::Uint(tag)] + rest,
    ensures
        clazel_ipc::message::spec::message_ok(m) == clazel_ipc::cbor::spec::is_items(rest, (n - 1) as nat),
{
    lemma_items_head(n, tag, rest);
    assert(clazel_ipc::message::spec::message_tokens(m) == seq![clazel_ipc::cbor::spec::Token::Array(n), clazel_ipc::cbor::spec::Token::Uint(tag)] + rest);
}

/// A message can be sent exactly when its texts are valid UTF-8.
pub proof fn lemma_message_ok(m: clazel_ipc::message::spec::Message)
    ensures
        clazel_ipc::message::spec::message_ok(m) == message_texts_ok(m),
{
    match m {
        clazel_ipc::message::spec::Message::CookieGet => {
            lemma_msg(m, 1, 1, Seq::empty());
            lemma_items_empty(0);
        },
        clazel_ipc::message::spec::Message::StorageClear => {
            lemma_msg(m, 1, 6, Seq::empty());
            lemma_items_empty(0);
        },
        clazel_ipc::message::spec::Message::StorageLength => {
            lemma_msg(m, 1, 8, Seq::empty());
            lemma_items_empty(0);
        },
        clazel_ipc::message::spec::Message::StorageKey { index } => {
            lemma_msg(m, 2, 7, seq![clazel_ipc::cbor::spec::Token::Uint(index)]);
            lemma_one(clazel_ipc::cbor::spec::Token::Uint(index));
        },
        clazel_ipc::message::spec::Message::StorageLengthValue { length } => {
            lemma_msg(m, 2, 104, seq![clazel_ipc::cbor::spec::Token::Uint(length)]);
            lemma_one(clazel_ipc::cbor::spec::Token::Uint(length));
        },
        clazel_ipc::message::spec::Message::Error { code } => {
            lemma_msg(m, 2, 105, seq![clazel_ipc::cbor::spec::Token::Uint(code)]);
            lemma_one(clazel_ipc::cbor::spec::Token::Uint(code));
        },
        clazel_ipc::message::spec::Message::CookieSet { cookie_string } => {
            lemma_msg(m, 2, 2, seq![clazel_ipc::cbor::spec::Token::Text(cookie_string)]);
            lemma_one(clazel_ipc::cbor::spec::Token::Text(cookie_string));
        },
        clazel_ipc::message::spec::Message::CookieValue { cookie_string } => {
            lemma_msg(m, 2, 102, seq![clazel_ipc::cbor::spec::Token::Text(cookie_string)]);
            lemma_one(clazel_ipc::cbor::spec::Token::Text(cookie_string));
        },
        clazel_ipc::message::spec::Message::StorageGetItem { key } => {
            lemma_msg(m, 2, 3, seq![clazel_ipc::cbor::spec::Token::Text(key)]);
            lemma_one(clazel_ipc::cbor::spec::Token::Text(key));
        },
        clazel_ipc::message::spec::Message::StorageRemoveItem { key } => {
            lemma_msg(m, 2, 5, seq![clazel_ipc::cbor::spec::Token::Text(key)]);
            lemma_one(clazel_ipc::cbor::spec::Token::Text(key));
        },
        clazel_ipc::message::spec::Message::Navigate { url } => {
            lemma_msg(m, 2, 9, seq![clazel_ipc::cbor::spec::Token::Text(url)]);
            lemma_one(clazel_ipc::cbor::spec::Token::Text(url));
        },
        clazel_ipc::message::spec::Message::StorageSetItem { key, value } => {
            lemma_msg(m, 3, 4, seq![clazel_ipc::cbor::spec::Token::Text(key), clazel_ipc::cbor::spec::Token::Text(value)]);
            lemma_two(clazel_ipc::cbor::spec::Token::Text(key), clazel_ipc::cbor::spec::Token::Text(value));
        },
        clazel_ipc::message::spec::Message::Commit { url, script } => {
            lemma_msg(m, 3, 101, seq![clazel_ipc::cbor::spec::Token::Text(url), clazel_ipc::cbor::spec::Token::Text(script)]);
            lemma_two(clazel_ipc::cbor::spec::Token::Text(url), clazel_ipc::cbor::spec::Token::Text(script));
        },
        clazel_ipc::message::spec::Message::StorageValue { value } => match value {
            None => {
                lemma_msg(m, 2, 103, seq![clazel_ipc::cbor::spec::Token::Bool(false)]);
                lemma_one(clazel_ipc::cbor::spec::Token::Bool(false));
            },
            Some(v) => {
                lemma_msg(m, 3, 103, seq![clazel_ipc::cbor::spec::Token::Bool(true), clazel_ipc::cbor::spec::Token::Text(v)]);
                lemma_two(clazel_ipc::cbor::spec::Token::Bool(true), clazel_ipc::cbor::spec::Token::Text(v));
            },
        },
    }
}

/// One non-array token owed once.
proof fn lemma_one(a: clazel_ipc::cbor::spec::Token)
    requires
        !(a is Array),
    ensures
        clazel_ipc::cbor::spec::is_items(seq![a], 1) == clazel_ipc::cbor::spec::token_ok(a),
{
    lemma_items_step(seq![a], 1);
    assert(seq![a].drop_first() =~= Seq::<clazel_ipc::cbor::spec::Token>::empty());
    lemma_items_empty(0);
}

/// Two non-array tokens owed twice.
proof fn lemma_two(a: clazel_ipc::cbor::spec::Token, b: clazel_ipc::cbor::spec::Token)
    requires
        !(a is Array),
        !(b is Array),
    ensures
        clazel_ipc::cbor::spec::is_items(seq![a, b], 2) == (clazel_ipc::cbor::spec::token_ok(a) && clazel_ipc::cbor::spec::token_ok(b)),
{
    lemma_items_step(seq![a, b], 2);
    assert(seq![a, b].drop_first() =~= seq![b]);
    lemma_one(b);
}

/// The length of a slice as a `u64` (a `usize` is at most 64 bits).
fn len_u64(s: &[u8]) -> (n: u64)
    ensures
        n as nat == s@.len(),
{
    s.len() as u64
}

/// The text string `s` can be sent (`utf8_valid`, as a `Vec` is short).
fn text_ok_exec(s: &[u8]) -> (r: bool)
    ensures
        r == text_ok(s@),
{
    let ok = clazel_encoding::utf8::decode::decode_without_bom_or_fail(s).is_some();
    let _n = len_u64(s);
    assert(_n as nat == s@.len());
    assert(ok == clazel_ipc::cbor::spec::utf8_valid(s@));
    assert(s@.len() < 0x1_0000_0000_0000_0000);
    ok
}

/// [`message_ok`] of an exec message.
pub fn message_ok_exec(m: &Msg) -> (r: bool)
    ensures
        r == clazel_ipc::message::spec::message_ok(m@),
{
    proof {
        lemma_message_ok(m@);
    }
    match m {
        Msg::CookieGet | Msg::StorageClear | Msg::StorageLength => true,
        Msg::StorageKey { .. } | Msg::StorageLengthValue { .. } | Msg::Error { .. } => true,
        Msg::CookieSet { cookie_string } | Msg::CookieValue { cookie_string } => text_ok_exec(cookie_string.as_slice()),
        Msg::StorageGetItem { key } | Msg::StorageRemoveItem { key } => text_ok_exec(key.as_slice()),
        Msg::StorageSetItem { key, value } => text_ok_exec(key.as_slice()) && text_ok_exec(value.as_slice()),
        Msg::Navigate { url } => text_ok_exec(url.as_slice()),
        Msg::Commit { url, script } => text_ok_exec(url.as_slice()) && text_ok_exec(script.as_slice()),
        Msg::StorageValue { value } => match value {
            None => true,
            Some(v) => text_ok_exec(v.as_slice()),
        },
    }
}

/// [`error_frame`]: the frame of `Error { code }`, for `code` the kernel
/// uses (all are below 24, so the frame is 8 octets).
pub fn error_frame_exec(code: u64) -> (r: Vec<u8>)
    requires
        code < 24,
    ensures
        r@ == crate::spec::error_frame(code as u64),
{
    let m = Msg::Error { code };
    proof {
        lemma_message_ok(m@);
    }
    let payload = encode_message(&m);
    assert(payload@.len() <= clazel_ipc::frame::spec::MAX_FRAME as nat) by {
        assert(payload@ == clazel_ipc::message::spec::encode_message(m@));
        lemma_error_payload_len(code);
    }
    match clazel_ipc::frame::codec::encode_frame(payload.as_slice()) {
        Some(f) => f,
        None => {
            assert(false);
            Vec::new()
        },
    }
}

/// The payload of `Error { code }` for a small code is at most 3 tokens of
/// at most 2 octets.
proof fn lemma_error_payload_len(code: u64)
    requires
        code < 24,
    ensures
        clazel_ipc::message::spec::encode_message(clazel_ipc::message::spec::Message::Error { code }).len() <= 4,
{
    // encode_head(0, 105) is 2 octets, the others one.
    let t = clazel_ipc::message::spec::message_tokens(clazel_ipc::message::spec::Message::Error { code });
    assert(t == seq![clazel_ipc::cbor::spec::Token::Array(2), clazel_ipc::cbor::spec::Token::Uint(105), clazel_ipc::cbor::spec::Token::Uint(code)]);
    let e = clazel_ipc::cbor::spec::encode(t);
    assert(clazel_ipc::message::spec::encode_message(clazel_ipc::message::spec::Message::Error { code }) == e);
    reveal_with_fuel(clazel_ipc::cbor::spec::encode, 4);
    assert(t.drop_first() =~= seq![clazel_ipc::cbor::spec::Token::Uint(105), clazel_ipc::cbor::spec::Token::Uint(code)]);
    assert(t.drop_first().drop_first() =~= seq![clazel_ipc::cbor::spec::Token::Uint(code)]);
    assert(t.drop_first().drop_first().drop_first() =~= Seq::<clazel_ipc::cbor::spec::Token>::empty());
    clazel_ipc::cbor::lemmas::lemma_be_bytes_len(105, 1);
    clazel_ipc::cbor::lemmas::lemma_be_bytes_len(code as nat, 1);
    clazel_ipc::cbor::lemmas::lemma_be_bytes_len(2, 1);
    assert(clazel_ipc::cbor::spec::encode(Seq::<clazel_ipc::cbor::spec::Token>::empty()) == Seq::<u8>::empty());
}

/// [`reply_frame`] of an exec message.
pub fn reply_frame_exec(m: &Msg) -> (r: Vec<u8>)
    ensures
        r@ == crate::spec::reply_frame(m@),
{
    if message_ok_exec(m) {
        let payload = encode_message(m);
        match clazel_ipc::frame::codec::encode_frame(payload.as_slice()) {
            Some(f) => f,
            None => error_frame_exec(4),
        }
    } else {
        error_frame_exec(4)
    }
}

/// [`commit_frame`]: the `Commit` of `url`, UTF-8 encoded, running `script`.
pub fn commit_frame_exec(url: &[u32], script: &[u8]) -> (r: Vec<u8>)
    requires
        clazel_encoding::utf8::spec::all_scalar_values(url@),
    ensures
        r@ == crate::spec::commit_frame(url@, script@),
{
    let encoded = clazel_encoding::utf8::encode::encode(url);
    let m = Msg::Commit { url: encoded, script: vstd::slice::slice_to_vec(script) };
    reply_frame_exec(&m)
}

} // verus!
