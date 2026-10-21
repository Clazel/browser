//! Executable-style specification of the IPC message schema (phase-2.md item
//! 2.3). The schema is ours: this file is the definition.
//!
//! A message is a CBOR array (`crate::cbor`) whose first element is an
//! unsigned integer tag and whose other elements are the message's fields,
//! in order. Fields are text strings, unsigned integers or booleans.
//!
//! | Tag | Direction | Message | Fields |
//! |-----|-----------|---------|--------|
//! | 1 | renderer to kernel | `CookieGet` | |
//! | 2 | renderer to kernel | `CookieSet` | cookie string (text) |
//! | 3 | renderer to kernel | `StorageGetItem` | key (text) |
//! | 4 | renderer to kernel | `StorageSetItem` | key (text), value (text) |
//! | 5 | renderer to kernel | `StorageRemoveItem` | key (text) |
//! | 6 | renderer to kernel | `StorageClear` | |
//! | 7 | renderer to kernel | `StorageKey` | index (unsigned) |
//! | 8 | renderer to kernel | `StorageLength` | |
//! | 9 | renderer to kernel | `Navigate` | url (text) |
//! | 101 | kernel to renderer | `Commit` | url (text), script (text) |
//! | 102 | kernel to renderer | `CookieValue` | cookie string (text) |
//! | 103 | kernel to renderer | `StorageValue` | present (bool), then value (text) only if present |
//! | 104 | kernel to renderer | `StorageLengthValue` | length (unsigned) |
//! | 105 | kernel to renderer | `Error` | code (unsigned) |
//!
//! `StorageLengthValue` is not in the plan's list, which has no reply for
//! `StorageLength`; the schema needs one.
//!
//! Two rules are part of the schema's spec ([`message_fields`], and
//! `lemmas::lemma_no_identity_fields`):
//! - **No message carries a claimed identity.** No origin, renderer id, tab
//!   id or sender URL appears in any message. The kernel learns the sender
//!   from the socket. (`Navigate`'s `url` is the address to go to, not the
//!   sender's.)
//! - **Renderer ids never reach a renderer.** They are assigned in order, so
//!   showing one would let a renderer count another's spawns.
//!
//! Modelling choices:
//! - Text is the bytes of its UTF-8 encoding (`Seq<u8>`), as in a CBOR text
//!   string token; a message is well formed ([`message_ok`]) when its
//!   token sequence is one data item of the profile, i.e. text is valid
//!   UTF-8.
//! - An absent storage value is `present = false` with no value, because
//!   the profile has no null.
//! - "Failure" is `None`.

#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The CBOR profile's token, as this schema uses it.
pub type Token = crate::cbor::spec::Token;

/// [`crate::cbor::spec::decode`].
pub open spec fn decode(b: Seq<u8>) -> Option<Seq<Token>> {
    crate::cbor::spec::decode(b)
}

/// [`crate::cbor::spec::encode`].
pub open spec fn encode(t: Seq<Token>) -> Seq<u8> {
    crate::cbor::spec::encode(t)
}

/// [`crate::cbor::spec::is_item`].
pub open spec fn is_item(t: Seq<Token>) -> bool {
    crate::cbor::spec::is_item(t)
}

/// A message, in either direction.
pub enum Message {
    /// Renderer to kernel: read `document.cookie`.
    CookieGet,
    /// Renderer to kernel: write `document.cookie`.
    CookieSet {
        /// The cookie string.
        cookie_string: Seq<u8>,
    },
    /// Renderer to kernel: `localStorage.getItem(key)`.
    StorageGetItem {
        /// The key.
        key: Seq<u8>,
    },
    /// Renderer to kernel: `localStorage.setItem(key, value)`.
    StorageSetItem {
        /// The key.
        key: Seq<u8>,
        /// The value.
        value: Seq<u8>,
    },
    /// Renderer to kernel: `localStorage.removeItem(key)`.
    StorageRemoveItem {
        /// The key.
        key: Seq<u8>,
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
        url: Seq<u8>,
    },
    /// Kernel to renderer: the document to run.
    Commit {
        /// The committed URL.
        url: Seq<u8>,
        /// The script to run.
        script: Seq<u8>,
    },
    /// Kernel to renderer: the value of `document.cookie`.
    CookieValue {
        /// The cookie string.
        cookie_string: Seq<u8>,
    },
    /// Kernel to renderer: a storage value, if there is one.
    StorageValue {
        /// The value, or `None` if there is none.
        value: Option<Seq<u8>>,
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

/// Whether `m` is sent by a renderer to the kernel.
pub open spec fn is_from_renderer(m: Message) -> bool {
    match m {
        Message::CookieGet
        | Message::CookieSet { .. }
        | Message::StorageGetItem { .. }
        | Message::StorageSetItem { .. }
        | Message::StorageRemoveItem { .. }
        | Message::StorageClear
        | Message::StorageKey { .. }
        | Message::StorageLength
        | Message::Navigate { .. } => true,
        _ => false,
    }
}

/// The kind of each field of a message.
pub enum Field {
    /// A cookie string.
    CookieString,
    /// A storage key.
    Key,
    /// A storage value.
    Value,
    /// A URL to navigate to or commit.
    Url,
    /// A script.
    Script,
    /// A storage index.
    Index,
    /// Whether a storage value is present.
    Present,
    /// A storage length.
    Length,
    /// An error code.
    Code,
    /// A claimed origin. No message has one.
    Origin,
    /// A renderer id. No message has one.
    RendererId,
    /// A tab id. No message has one.
    TabId,
    /// The URL of the sender. No message has one.
    SenderUrl,
}

/// The fields a message carries, in order. The two schema rules say none of
/// them is an identity ([`is_identity`]).
pub open spec fn message_fields(m: Message) -> Seq<Field> {
    match m {
        Message::CookieGet => seq![],
        Message::CookieSet { .. } => seq![Field::CookieString],
        Message::StorageGetItem { .. } => seq![Field::Key],
        Message::StorageSetItem { .. } => seq![Field::Key, Field::Value],
        Message::StorageRemoveItem { .. } => seq![Field::Key],
        Message::StorageClear => seq![],
        Message::StorageKey { .. } => seq![Field::Index],
        Message::StorageLength => seq![],
        Message::Navigate { .. } => seq![Field::Url],
        Message::Commit { .. } => seq![Field::Url, Field::Script],
        Message::CookieValue { .. } => seq![Field::CookieString],
        Message::StorageValue { value } => match value {
            None => seq![Field::Present],
            Some(_) => seq![Field::Present, Field::Value],
        },
        Message::StorageLengthValue { .. } => seq![Field::Length],
        Message::Error { .. } => seq![Field::Code],
    }
}

/// A field that names who is speaking or which renderer: forbidden.
pub open spec fn is_identity(f: Field) -> bool {
    match f {
        Field::Origin | Field::RendererId | Field::TabId | Field::SenderUrl => true,
        _ => false,
    }
}

/// The tokens of a message: an array of the tag and the fields.
pub open spec fn message_tokens(m: Message) -> Seq<Token> {
    match m {
        Message::CookieGet => seq![Token::Array(1), Token::Uint(1)],
        Message::CookieSet { cookie_string } => seq![Token::Array(2), Token::Uint(2), Token::Text(cookie_string)],
        Message::StorageGetItem { key } => seq![Token::Array(2), Token::Uint(3), Token::Text(key)],
        Message::StorageSetItem { key, value } => seq![Token::Array(3), Token::Uint(4), Token::Text(key), Token::Text(value)],
        Message::StorageRemoveItem { key } => seq![Token::Array(2), Token::Uint(5), Token::Text(key)],
        Message::StorageClear => seq![Token::Array(1), Token::Uint(6)],
        Message::StorageKey { index } => seq![Token::Array(2), Token::Uint(7), Token::Uint(index)],
        Message::StorageLength => seq![Token::Array(1), Token::Uint(8)],
        Message::Navigate { url } => seq![Token::Array(2), Token::Uint(9), Token::Text(url)],
        Message::Commit { url, script } => seq![Token::Array(3), Token::Uint(101), Token::Text(url), Token::Text(script)],
        Message::CookieValue { cookie_string } => seq![Token::Array(2), Token::Uint(102), Token::Text(cookie_string)],
        Message::StorageValue { value } => match value {
            None => seq![Token::Array(2), Token::Uint(103), Token::Bool(false)],
            Some(v) => seq![Token::Array(3), Token::Uint(103), Token::Bool(true), Token::Text(v)],
        },
        Message::StorageLengthValue { length } => seq![Token::Array(2), Token::Uint(104), Token::Uint(length)],
        Message::Error { code } => seq![Token::Array(2), Token::Uint(105), Token::Uint(code)],
    }
}

/// Whether `m` can be sent: its tokens are one data item of the profile.
pub open spec fn message_ok(m: Message) -> bool {
    is_item(message_tokens(m))
}

/// The message with this `tag` and these field tokens.
pub open spec fn parse_fields(tag: u64, f: Seq<Token>) -> Option<Message> {
    if tag == 1 {
        if f.len() == 0 { Some(Message::CookieGet) } else { None }
    } else if tag == 2 {
        if f.len() == 1 { match f[0] { Token::Text(s) => Some(Message::CookieSet { cookie_string: s }), _ => None } } else { None }
    } else if tag == 3 {
        if f.len() == 1 { match f[0] { Token::Text(s) => Some(Message::StorageGetItem { key: s }), _ => None } } else { None }
    } else if tag == 4 {
        if f.len() == 2 {
            match (f[0], f[1]) {
                (Token::Text(k), Token::Text(v)) => Some(Message::StorageSetItem { key: k, value: v }),
                _ => None,
            }
        } else { None }
    } else if tag == 5 {
        if f.len() == 1 { match f[0] { Token::Text(s) => Some(Message::StorageRemoveItem { key: s }), _ => None } } else { None }
    } else if tag == 6 {
        if f.len() == 0 { Some(Message::StorageClear) } else { None }
    } else if tag == 7 {
        if f.len() == 1 { match f[0] { Token::Uint(i) => Some(Message::StorageKey { index: i }), _ => None } } else { None }
    } else if tag == 8 {
        if f.len() == 0 { Some(Message::StorageLength) } else { None }
    } else if tag == 9 {
        if f.len() == 1 { match f[0] { Token::Text(s) => Some(Message::Navigate { url: s }), _ => None } } else { None }
    } else if tag == 101 {
        if f.len() == 2 {
            match (f[0], f[1]) {
                (Token::Text(u), Token::Text(s)) => Some(Message::Commit { url: u, script: s }),
                _ => None,
            }
        } else { None }
    } else if tag == 102 {
        if f.len() == 1 { match f[0] { Token::Text(s) => Some(Message::CookieValue { cookie_string: s }), _ => None } } else { None }
    } else if tag == 103 {
        if f.len() == 1 {
            match f[0] { Token::Bool(false) => Some(Message::StorageValue { value: None }), _ => None }
        } else if f.len() == 2 {
            match (f[0], f[1]) {
                (Token::Bool(true), Token::Text(v)) => Some(Message::StorageValue { value: Some(v) }),
                _ => None,
            }
        } else { None }
    } else if tag == 104 {
        if f.len() == 1 { match f[0] { Token::Uint(n) => Some(Message::StorageLengthValue { length: n }), _ => None } } else { None }
    } else if tag == 105 {
        if f.len() == 1 { match f[0] { Token::Uint(n) => Some(Message::Error { code: n }), _ => None } } else { None }
    } else {
        None
    }
}

/// The message in a token sequence: an array whose first element is the
/// tag, and which has exactly the message's fields after it.
pub open spec fn parse_message(t: Seq<Token>) -> Option<Message> {
    if t.len() < 2 {
        None
    } else {
        match (t[0], t[1]) {
            (Token::Array(n), Token::Uint(tag)) => {
                if n as nat + 1 == t.len() {
                    parse_fields(tag, t.subrange(2, t.len() as int))
                } else {
                    None
                }
            },
            _ => None,
        }
    }
}

/// Decode one message, in either direction, from the bytes of a CBOR item.
pub open spec fn decode_message(b: Seq<u8>) -> Option<Message> {
    match decode(b) {
        Some(t) => parse_message(t),
        None => None,
    }
}

/// Decode a message the kernel receives: only renderer-to-kernel messages.
pub open spec fn decode_renderer_message(b: Seq<u8>) -> Option<Message> {
    match decode_message(b) {
        Some(m) => if is_from_renderer(m) { Some(m) } else { None },
        None => None,
    }
}

/// The bytes of a message.
pub open spec fn encode_message(m: Message) -> Seq<u8> {
    encode(message_tokens(m))
}

/// Decode a message from a whole frame: split the frame, then decode.
pub open spec fn decode_framed(frame: Seq<u8>) -> Option<Message> {
    match crate::frame::spec::decode_frame(frame) {
        Some(p) => decode_message(p),
        None => None,
    }
}

} // verus!
