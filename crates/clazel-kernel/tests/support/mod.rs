//! Helpers shared by the kernel conformance tests: fake renderers that talk
//! to the exec kernel in frames, and the URL functions the kernel is given.
//!
//! The URL functions ([`TestUrls`]) are a **test-only** implementation of
//! `UrlFnsExec` built on `clazel-url`'s proven parser, `clazel-origin`'s
//! proven `url_origin_exec` and the URL serializer. They are not item 2.13's
//! instantiation: nothing proves they equal the spec's `UrlFns`, only that
//! each is the composition the plan names (the origin of the parsed URL; the
//! serialized path; the serialization of the parse against a base). The
//! kernel proof holds for any implementation, so the tests exercise it with
//! this one.

use clazel_ipc::message::codec::{Msg, decode_framed, encode_framed};
use clazel_kernel::exec::records::{EventRecord, OutputRecord, StateRecord, init_record};
use clazel_kernel::exec::step::step_exec;
use clazel_kernel::exec::urls::UrlFnsExec;
use clazel_origin::exec::{ParsedOrigin, url_origin_exec};
use clazel_url::url::parse::basic_url_parser;
use clazel_url::url::serialize::url_path_serializer;

/// The code points of a string.
pub fn code_points(s: &str) -> Vec<u32> {
    s.chars().map(u32::from).collect()
}

/// The URL functions of the tests.
pub struct TestUrls;

impl UrlFnsExec for TestUrls {
    fn origin_of(&self, url: &[u32]) -> Option<ParsedOrigin> {
        let parsed = basic_url_parser(url, None)?;
        Some(url_origin_exec(&parsed, 0))
    }

    fn path_of(&self, url: &[u32]) -> Vec<u8> {
        match basic_url_parser(url, None) {
            Some(parsed) => url_path_serializer(&parsed.path)
                .iter()
                .map(|c| u8::try_from(*c).unwrap_or(b'?'))
                .collect(),
            None => Vec::new(),
        }
    }

    fn resolve(&self, base: &[u32], input: &[u32]) -> Option<Vec<u32>> {
        let base = basic_url_parser(base, None)?;
        let parsed = basic_url_parser(input, Some(&base))?;
        Some(parsed.serialize(false))
    }
}

/// What the kernel sent, decoded.
#[derive(Debug, PartialEq, Eq)]
pub enum Out {
    /// A frame to a renderer, decoded.
    To(u64, Msg),
    /// A frame to a renderer that does not decode (a kernel bug).
    Garbled(u64),
    /// A renderer started.
    Spawn(u64),
    /// A renderer killed.
    Kill(u64),
}

/// The exec kernel, driven as the host shell would.
pub struct Kernel {
    /// The state, absent only while a step runs.
    pub state: Option<StateRecord>,
}

impl Kernel {
    /// A kernel before anything happens.
    pub fn new() -> Self {
        Self {
            state: Some(init_record()),
        }
    }

    /// One event; the outputs, decoded.
    pub fn event(&mut self, e: &EventRecord) -> Vec<Out> {
        let Some(s) = self.state.take() else {
            return Vec::new();
        };
        let (next, outputs) = step_exec(&TestUrls, s, e);
        self.state = Some(next);
        outputs
            .into_iter()
            .map(|o| match o {
                OutputRecord::ToRenderer { id, bytes } => match decode_framed(&bytes) {
                    Some(m) => Out::To(id, m),
                    None => Out::Garbled(id),
                },
                OutputRecord::Spawn { id } => Out::Spawn(id),
                OutputRecord::Kill { id } => Out::Kill(id),
            })
            .collect()
    }

    /// The user opens a tab; the id of its renderer, and what was sent.
    pub fn open_tab(&mut self, url: &str, script: &str) -> (Option<u64>, Vec<Out>) {
        let out = self.event(&EventRecord::OpenTab {
            url: code_points(url),
            script: script.as_bytes().to_vec(),
        });
        let id = out.iter().find_map(|o| match o {
            Out::Spawn(id) => Some(*id),
            _ => None,
        });
        (id, out)
    }

    /// Renderer `id` sends `m`, framed by the IPC codec.
    pub fn send(&mut self, id: u64, m: &Msg) -> Vec<Out> {
        let bytes = encode_framed(m).unwrap_or_default();
        self.event(&EventRecord::FromRenderer { id, bytes })
    }
}
