//! The script format: the plan leaves it open, so it is as small as it can be.
//!
//! A script is UTF-8 text, one operation per line. Blank lines and lines
//! starting with `#` are ignored; the rest are one of
//!
//! ```text
//! cookie-get                    document.cookie
//! cookie-set <cookie string>    document.cookie = "<cookie string>"
//! storage-get <key>             localStorage.getItem(key)
//! storage-set <key> <value>     localStorage.setItem(key, value)
//! storage-remove <key>          localStorage.removeItem(key)
//! storage-clear                 localStorage.clear()
//! storage-key <index>           localStorage.key(index)
//! storage-length                localStorage.length
//! ```
//!
//! A key has no space; a value or a cookie string is the rest of the line.
//! The decoder is total: it uses no indexing, no arithmetic that can
//! overflow and nothing that panics, so any bytes give a script or an error.
//! The script reaches the renderer only in a `Commit`, which the kernel
//! sends for the user's `OpenTab` or `NavigateTab`, never from a web page.

use clazel_ipc::message::codec::Msg;

/// One operation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Op {
    /// `cookie-get`.
    CookieGet,
    /// `cookie-set <cookie string>`.
    CookieSet(Vec<u8>),
    /// `storage-get <key>`.
    StorageGet(Vec<u8>),
    /// `storage-set <key> <value>`.
    StorageSet(Vec<u8>, Vec<u8>),
    /// `storage-remove <key>`.
    StorageRemove(Vec<u8>),
    /// `storage-clear`.
    StorageClear,
    /// `storage-key <index>`.
    StorageKey(u64),
    /// `storage-length`.
    StorageLength,
}

/// A line that is not an operation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ScriptError {
    /// The line, counting from 1.
    pub line: usize,
    /// What is wrong with it.
    pub reason: &'static str,
}

/// Split at the first space: the word, and the rest (empty if there is none).
fn split_word(s: &[u8]) -> (&[u8], &[u8]) {
    match s.iter().position(|b| *b == b' ') {
        Some(i) => match s.split_at_checked(i) {
            Some((word, rest)) => (word, rest.get(1..).unwrap_or_default()),
            None => (s, &[]),
        },
        None => (s, &[]),
    }
}

/// One line, already trimmed and not blank.
fn parse_line(line: &[u8]) -> Result<Op, &'static str> {
    let (cmd, arg) = split_word(line);
    let (key, value) = split_word(arg);
    let no_arg = |op: Op| if arg.is_empty() { Ok(op) } else { Err("unexpected argument") };
    let key_only = |f: fn(Vec<u8>) -> Op| {
        if key.is_empty() || !value.is_empty() { Err("expected one key") } else { Ok(f(key.to_vec())) }
    };
    match cmd {
        b"cookie-get" => no_arg(Op::CookieGet),
        b"cookie-set" => Ok(Op::CookieSet(arg.to_vec())),
        b"storage-get" => key_only(Op::StorageGet),
        b"storage-set" if !key.is_empty() => Ok(Op::StorageSet(key.to_vec(), value.to_vec())),
        b"storage-set" => Err("expected a key"),
        b"storage-remove" => key_only(Op::StorageRemove),
        b"storage-clear" => no_arg(Op::StorageClear),
        b"storage-key" => match std::str::from_utf8(arg).ok().and_then(|n| n.parse().ok()) {
            Some(n) => Ok(Op::StorageKey(n)),
            None => Err("expected an index"),
        },
        b"storage-length" => no_arg(Op::StorageLength),
        _ => Err("unknown operation"),
    }
}

/// Decode a script. Total: every input is a list of operations or an error.
pub fn parse(script: &[u8]) -> Result<Vec<Op>, ScriptError> {
    let mut ops = Vec::new();
    for (i, raw) in script.split(|b| *b == b'\n').enumerate() {
        let line = raw.trim_ascii();
        if line.is_empty() || line.first() == Some(&b'#') {
            continue;
        }
        match parse_line(line) {
            Ok(op) => ops.push(op),
            Err(reason) => return Err(ScriptError { line: i.saturating_add(1), reason }),
        }
    }
    Ok(ops)
}

impl Op {
    /// The renderer-to-kernel message that performs the operation.
    pub fn to_message(&self) -> Msg {
        match self {
            Op::CookieGet => Msg::CookieGet,
            Op::CookieSet(s) => Msg::CookieSet { cookie_string: s.clone() },
            Op::StorageGet(k) => Msg::StorageGetItem { key: k.clone() },
            Op::StorageSet(k, v) => Msg::StorageSetItem { key: k.clone(), value: v.clone() },
            Op::StorageRemove(k) => Msg::StorageRemoveItem { key: k.clone() },
            Op::StorageClear => Msg::StorageClear,
            Op::StorageKey(n) => Msg::StorageKey { index: *n },
            Op::StorageLength => Msg::StorageLength,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{Op, ScriptError, parse};

    #[test]
    fn every_operation_parses() {
        let script = b"# comment\n\ncookie-get\ncookie-set a=1; Path=/\nstorage-set k v w\n\
                       storage-set k\nstorage-get k\nstorage-remove k\nstorage-clear\n  storage-key 3  \nstorage-length";
        assert_eq!(
            parse(script),
            Ok(vec![
                Op::CookieGet,
                Op::CookieSet(b"a=1; Path=/".to_vec()),
                Op::StorageSet(b"k".to_vec(), b"v w".to_vec()),
                Op::StorageSet(b"k".to_vec(), Vec::new()),
                Op::StorageGet(b"k".to_vec()),
                Op::StorageRemove(b"k".to_vec()),
                Op::StorageClear,
                Op::StorageKey(3),
                Op::StorageLength,
            ])
        );
    }

    #[test]
    fn bad_lines_name_their_line() {
        let bad = |s: &[u8]| parse(s).map_err(|e: ScriptError| (e.line, e.reason));
        assert_eq!(bad(b"cookie-get\nfly"), Err((2, "unknown operation")));
        assert_eq!(bad(b"storage-get"), Err((1, "expected one key")));
        assert_eq!(bad(b"storage-get a b"), Err((1, "expected one key")));
        assert_eq!(bad(b"storage-set"), Err((1, "expected a key")));
        assert_eq!(bad(b"storage-key x"), Err((1, "expected an index")));
        assert_eq!(bad(b"storage-key -1"), Err((1, "expected an index")));
        assert_eq!(bad(b"cookie-get x"), Err((1, "unexpected argument")));
    }

    #[test]
    fn any_bytes_are_a_script_or_an_error() {
        // Total on arbitrary input, including invalid UTF-8 and a lone space.
        for s in [&b" "[..], b"\xff\xfe", b"storage-key \xff", b"\n\n\r\n", b"#"] {
            let _ = parse(s);
        }
    }
}
