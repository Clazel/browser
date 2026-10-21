//! The executable message codec, proven to meet [`super::contract`].

use crate::cbor::token::*;
#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// A message, in either direction; see [`Message`], whose view it is.
#[derive(Debug, PartialEq, Eq)]
pub enum Msg {
    /// Renderer to kernel: read `document.cookie`.
    CookieGet,
    /// Renderer to kernel: write `document.cookie`.
    CookieSet {
        /// The cookie string.
        cookie_string: Vec<u8>,
    },
    /// Renderer to kernel: `localStorage.getItem(key)`.
    StorageGetItem {
        /// The key.
        key: Vec<u8>,
    },
    /// Renderer to kernel: `localStorage.setItem(key, value)`.
    StorageSetItem {
        /// The key.
        key: Vec<u8>,
        /// The value.
        value: Vec<u8>,
    },
    /// Renderer to kernel: `localStorage.removeItem(key)`.
    StorageRemoveItem {
        /// The key.
        key: Vec<u8>,
    },
    /// Renderer to kernel: `localStorage.clear()`.
    StorageClear,
    /// Renderer to kernel: `localStorage.key(index)`.
    StorageKey {
        /// The index.
        index: u64,
    },
    /// Renderer to kernel: `localStorage.length`.
    StorageLength,
    /// Renderer to kernel: navigate to a URL.
    Navigate {
        /// The URL to go to (not the sender's).
        url: Vec<u8>,
    },
    /// Kernel to renderer: the document to run.
    Commit {
        /// The committed URL.
        url: Vec<u8>,
        /// The script to run.
        script: Vec<u8>,
    },
    /// Kernel to renderer: the value of `document.cookie`.
    CookieValue {
        /// The cookie string.
        cookie_string: Vec<u8>,
    },
    /// Kernel to renderer: a storage value, if there is one.
    StorageValue {
        /// The value, or `None` if there is none.
        value: Option<Vec<u8>>,
    },
    /// Kernel to renderer: `localStorage.length`.
    StorageLengthValue {
        /// The length.
        length: u64,
    },
    /// Kernel to renderer: a request failed.
    Error {
        /// The error code.
        code: u64,
    },
}

/// The view of an optional string.
pub open spec fn option_bytes(v: Option<Vec<u8>>) -> Option<Seq<u8>> {
    match v {
        Some(v) => Some(v@),
        None => None,
    }
}

impl View for Msg {
    type V = Message;

    open spec fn view(&self) -> Message {
        match self {
            Msg::CookieGet => Message::CookieGet,
            Msg::CookieSet { cookie_string } => Message::CookieSet { cookie_string: cookie_string@ },
            Msg::StorageGetItem { key } => Message::StorageGetItem { key: key@ },
            Msg::StorageSetItem { key, value } => Message::StorageSetItem { key: key@, value: value@ },
            Msg::StorageRemoveItem { key } => Message::StorageRemoveItem { key: key@ },
            Msg::StorageClear => Message::StorageClear,
            Msg::StorageKey { index } => Message::StorageKey { index: *index },
            Msg::StorageLength => Message::StorageLength,
            Msg::Navigate { url } => Message::Navigate { url: url@ },
            Msg::Commit { url, script } => Message::Commit { url: url@, script: script@ },
            Msg::CookieValue { cookie_string } => Message::CookieValue { cookie_string: cookie_string@ },
            Msg::StorageValue { value } => Message::StorageValue { value: option_bytes(*value) },
            Msg::StorageLengthValue { length } => Message::StorageLengthValue { length: *length },
            Msg::Error { code } => Message::Error { code: *code },
        }
    }
}

/// The view of an optional message; `None` is failure.
pub open spec fn option_msg(m: Option<Msg>) -> Option<Message> {
    match m {
        Some(m) => Some(m@),
        None => None,
    }
}

fn copy(s: &[u8]) -> (v: Vec<u8>)
    ensures
        v@ == s@,
{
    vstd::slice::slice_to_vec(s)
}

/// The text at index `i`, if the token there is a text string.
fn text_at(toks: &[Tok], i: usize) -> (r: Option<Vec<u8>>)
    requires
        i < toks.len(),
    ensures
        match r {
            Some(v) => views(toks@)[i as int] == crate::cbor::spec::Token::Text(v@),
            None => !(views(toks@)[i as int] is Text),
        },
{
    match toks.get(i) {
        Some(Tok::Text(v)) => Some(copy(v.as_slice())),
        _ => None,
    }
}

/// The unsigned integer at index `i`, if the token there is one.
fn uint_at(toks: &[Tok], i: usize) -> (r: Option<u64>)
    requires
        i < toks.len(),
    ensures
        match r {
            Some(n) => views(toks@)[i as int] == crate::cbor::spec::Token::Uint(n),
            None => !(views(toks@)[i as int] is Uint),
        },
{
    match toks.get(i) {
        Some(Tok::Uint(n)) => Some(*n),
        _ => None,
    }
}

/// The boolean at index `i`, if the token there is one.
fn bool_at(toks: &[Tok], i: usize) -> (r: Option<bool>)
    requires
        i < toks.len(),
    ensures
        match r {
            Some(b) => views(toks@)[i as int] == crate::cbor::spec::Token::Bool(b),
            None => !(views(toks@)[i as int] is Bool),
        },
{
    match toks.get(i) {
        Some(Tok::Bool(b)) => Some(*b),
        _ => None,
    }
}

/// The message with this `tag` whose fields are the tokens after the first
/// two.
fn parse_fields(tag: u64, toks: &[Tok]) -> (r: Option<Msg>)
    requires
        toks.len() >= 2,
    ensures
        option_msg(r) == super::spec::parse_fields(tag, views(toks@).subrange(2, toks.len() as int)),
{
    // Never saturates: toks.len() >= 2.
    let k = toks.len().saturating_sub(2);
    let ghost f = views(toks@).subrange(2, toks.len() as int);
    assert(f.len() == k);
    assert forall|j: int| 0 <= j < f.len() implies f[j] == views(toks@)[j + 2] by {}
    if tag == 1 {
        if k == 0 { Some(Msg::CookieGet) } else { None }
    } else if tag == 2 {
        if k == 1 {
            let s = text_at(toks, 2)?;
            Some(Msg::CookieSet { cookie_string: s })
        } else { None }
    } else if tag == 3 {
        if k == 1 {
            let s = text_at(toks, 2)?;
            Some(Msg::StorageGetItem { key: s })
        } else { None }
    } else if tag == 4 {
        if k == 2 {
            match (text_at(toks, 2), text_at(toks, 3)) {
                (Some(a), Some(b)) => Some(Msg::StorageSetItem { key: a, value: b }),
                _ => None,
            }
        } else { None }
    } else if tag == 5 {
        if k == 1 {
            let s = text_at(toks, 2)?;
            Some(Msg::StorageRemoveItem { key: s })
        } else { None }
    } else if tag == 6 {
        if k == 0 { Some(Msg::StorageClear) } else { None }
    } else if tag == 7 {
        if k == 1 {
            let n = uint_at(toks, 2)?;
            Some(Msg::StorageKey { index: n })
        } else { None }
    } else if tag == 8 {
        if k == 0 { Some(Msg::StorageLength) } else { None }
    } else if tag == 9 {
        if k == 1 {
            let s = text_at(toks, 2)?;
            Some(Msg::Navigate { url: s })
        } else { None }
    } else if tag == 101 {
        if k == 2 {
            match (text_at(toks, 2), text_at(toks, 3)) {
                (Some(a), Some(b)) => Some(Msg::Commit { url: a, script: b }),
                _ => None,
            }
        } else { None }
    } else if tag == 102 {
        if k == 1 {
            let s = text_at(toks, 2)?;
            Some(Msg::CookieValue { cookie_string: s })
        } else { None }
    } else if tag == 103 {
        if k == 1 {
            match bool_at(toks, 2) {
                Some(false) => Some(Msg::StorageValue { value: None }),
                _ => None,
            }
        } else if k == 2 {
            match (bool_at(toks, 2), text_at(toks, 3)) {
                (Some(true), Some(v)) => Some(Msg::StorageValue { value: Some(v) }),
                _ => None,
            }
        } else { None }
    } else if tag == 104 {
        if k == 1 {
            let n = uint_at(toks, 2)?;
            Some(Msg::StorageLengthValue { length: n })
        } else { None }
    } else if tag == 105 {
        if k == 1 {
            let n = uint_at(toks, 2)?;
            Some(Msg::Error { code: n })
        } else { None }
    } else {
        None
    }
}

/// The message in a token sequence.
fn parse_message(toks: &[Tok]) -> (r: Option<Msg>)
    ensures
        option_msg(r) == super::spec::parse_message(views(toks@)),
{
    if toks.len() < 2 {
        return None;
    }
    let n = match toks.first() {
        Some(Tok::Array(n)) => *n,
        _ => return None,
    };
    let tag = uint_at(toks, 1)?;
    // toks.len() >= 2, so this does not saturate.
    if n == (toks.len() as u64).saturating_sub(1) {
        parse_fields(tag, toks)
    } else {
        None
    }
}

/// Decode one message, in either direction, from the bytes of a CBOR item.
pub fn decode_message(input: &[u8]) -> (output: Option<Msg>)
    ensures
        super::contract::decode_message_ensures(input@, option_msg(output)),
{
    let toks = crate::cbor::decode::decode(input)?;
    parse_message(toks.as_slice())
}

/// Whether `m` is sent by a renderer to the kernel.
pub fn is_from_renderer(m: &Msg) -> (r: bool)
    ensures
        r == super::spec::is_from_renderer(m@),
{
    matches!(
        m,
        Msg::CookieGet
            | Msg::CookieSet { .. }
            | Msg::StorageGetItem { .. }
            | Msg::StorageSetItem { .. }
            | Msg::StorageRemoveItem { .. }
            | Msg::StorageClear
            | Msg::StorageKey { .. }
            | Msg::StorageLength
            | Msg::Navigate { .. }
    )
}

/// Decode a message the kernel receives from a renderer: only
/// renderer-to-kernel messages.
pub fn decode_renderer_message(input: &[u8]) -> (output: Option<Msg>)
    ensures
        super::contract::decode_renderer_message_ensures(input@, option_msg(output)),
{
    let m = decode_message(input)?;
    if is_from_renderer(&m) { Some(m) } else { None }
}

/// Decode a message from a whole frame.
pub fn decode_framed(frame: &[u8]) -> (output: Option<Msg>)
    ensures
        super::contract::decode_framed_ensures(frame@, option_msg(output)),
{
    let payload = crate::frame::codec::decode_frame(frame)?;
    decode_message(payload.as_slice())
}

fn toks2(a: Tok, b: Tok) -> (t: Vec<Tok>)
    ensures
        views(t@) =~= seq![a@, b@],
{
    let t = vec![a, b];
    assert(views(t@) =~= seq![a@, b@]);
    t
}

fn toks3(a: Tok, b: Tok, c: Tok) -> (t: Vec<Tok>)
    ensures
        views(t@) =~= seq![a@, b@, c@],
{
    let t = vec![a, b, c];
    assert(views(t@) =~= seq![a@, b@, c@]);
    t
}

fn toks4(a: Tok, b: Tok, c: Tok, d: Tok) -> (t: Vec<Tok>)
    ensures
        views(t@) =~= seq![a@, b@, c@, d@],
{
    let t = vec![a, b, c, d];
    assert(views(t@) =~= seq![a@, b@, c@, d@]);
    t
}

/// The tokens of a message.
fn message_tokens(m: &Msg) -> (t: Vec<Tok>)
    ensures
        views(t@) =~= super::spec::message_tokens(m@),
{
    match m {
        Msg::CookieGet => toks2(Tok::Array(1), Tok::Uint(1)),
        Msg::CookieSet { cookie_string } => toks3(Tok::Array(2), Tok::Uint(2), Tok::Text(copy(cookie_string.as_slice()))),
        Msg::StorageGetItem { key } => toks3(Tok::Array(2), Tok::Uint(3), Tok::Text(copy(key.as_slice()))),
        Msg::StorageSetItem { key, value } => toks4(
            Tok::Array(3),
            Tok::Uint(4),
            Tok::Text(copy(key.as_slice())),
            Tok::Text(copy(value.as_slice())),
        ),
        Msg::StorageRemoveItem { key } => toks3(Tok::Array(2), Tok::Uint(5), Tok::Text(copy(key.as_slice()))),
        Msg::StorageClear => toks2(Tok::Array(1), Tok::Uint(6)),
        Msg::StorageKey { index } => toks3(Tok::Array(2), Tok::Uint(7), Tok::Uint(*index)),
        Msg::StorageLength => toks2(Tok::Array(1), Tok::Uint(8)),
        Msg::Navigate { url } => toks3(Tok::Array(2), Tok::Uint(9), Tok::Text(copy(url.as_slice()))),
        Msg::Commit { url, script } => toks4(
            Tok::Array(3),
            Tok::Uint(101),
            Tok::Text(copy(url.as_slice())),
            Tok::Text(copy(script.as_slice())),
        ),
        Msg::CookieValue { cookie_string } => toks3(Tok::Array(2), Tok::Uint(102), Tok::Text(copy(cookie_string.as_slice()))),
        Msg::StorageValue { value } => match value {
            None => toks3(Tok::Array(2), Tok::Uint(103), Tok::Bool(false)),
            Some(v) => toks4(Tok::Array(3), Tok::Uint(103), Tok::Bool(true), Tok::Text(copy(v.as_slice()))),
        },
        Msg::StorageLengthValue { length } => toks3(Tok::Array(2), Tok::Uint(104), Tok::Uint(*length)),
        Msg::Error { code } => toks3(Tok::Array(2), Tok::Uint(105), Tok::Uint(*code)),
    }
}

/// The bytes of a message.
pub fn encode_message(m: &Msg) -> (output: Vec<u8>)
    requires
        super::contract::encode_message_requires(m@),
    ensures
        super::contract::encode_message_ensures(m@, output@),
{
    let toks = message_tokens(m);
    assert(views(toks@) =~= message_tokens_spec(m@));
    crate::cbor::encode::encode(toks.as_slice())
}

/// The frame of a message; `None` if its bytes are over `MAX_FRAME`.
pub fn encode_framed(m: &Msg) -> (output: Option<Vec<u8>>)
    requires
        super::contract::encode_message_requires(m@),
    ensures
        super::contract::encode_framed_ensures(
            m@,
            match output {
                Some(v) => Some(v@),
                None => None,
            },
        ),
{
    let payload = encode_message(m);
    crate::frame::codec::encode_frame(payload.as_slice())
}

/// The spec's tokens of a message (a name for the spec function, which the
/// exec function of the same name shadows).
spec fn message_tokens_spec(m: Message) -> Seq<crate::cbor::spec::Token> {
    super::spec::message_tokens(m)
}

} // verus!
