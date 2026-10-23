//! The kernel host shell (phase-2.md item 2.15): the I/O around the proven
//! kernel `step`. One socket pair per renderer, `clazel-renderer` spawned with
//! its end as stdin and stdout, a table from renderer id to socket, and a
//! thread per socket that reads whole frames. The id of an event is the id
//! the socket was created for, never anything in a frame. A frame over
//! `MAX_FRAME` (refused from its first 4 bytes) or a closed socket becomes
//! `RendererExited`. Outputs are carried out in order. The host prints every
//! frame it carries, decoded, and each renderer's exit and stderr (which
//! names a failed sandbox layer).

use std::collections::HashMap;
use std::io::{Read, Write};
use std::net::Shutdown;
use std::os::fd::OwnedFd;
use std::os::unix::net::UnixStream;
use std::process::{Child, Command, Stdio};
use std::sync::mpsc::{Receiver, Sender, channel};
use std::time::{Duration, Instant, SystemTime, UNIX_EPOCH};

use clazel_ipc::frame::codec::payload_length;
use clazel_ipc::message::codec::{Msg, decode_framed};
use clazel_kernel::exec::real_urls::step_real;
use clazel_kernel::exec::records::{EventRecord, OutputRecord, StateRecord, init_record};

/// What a socket's reader thread reports; the id is the socket's.
enum Ev {
    Frame(u64, Vec<u8>),
    Gone(u64, String),
}

struct Renderer {
    sock: UnixStream,
    child: Child,
}

/// The host: the kernel state and the renderers it runs.
pub struct Host {
    state: StateRecord,
    table: HashMap<u64, Renderer>,
    tx: Sender<Ev>,
    rx: Receiver<Ev>,
    command: Box<dyn FnMut(u64) -> Command>,
    /// Every line the host has printed.
    pub log: Vec<String>,
}

/// Read whole frames until the socket closes or announces too much.
fn read_frames(id: u64, mut sock: UnixStream, tx: Sender<Ev>) {
    let why = loop {
        let mut header = [0u8; 4];
        if sock.read_exact(&mut header).is_err() {
            break "closed its socket".to_owned();
        }
        let Some(len) = payload_length(&header) else {
            break format!("sent a frame over MAX_FRAME (announced {} bytes)", u32::from_be_bytes(header));
        };
        let mut payload = vec![0u8; len];
        if sock.read_exact(&mut payload).is_err() {
            break "closed its socket inside a frame".to_owned();
        }
        let mut frame = header.to_vec();
        frame.extend_from_slice(&payload);
        if tx.send(Ev::Frame(id, frame)).is_err() {
            return;
        }
    };
    let _ = tx.send(Ev::Gone(id, why));
}

/// Seconds since 1601-01-01, the kernel's clock; far below its upper bound.
fn now() -> u64 {
    let unix = SystemTime::now().duration_since(UNIX_EPOCH).map_or(0, |d| d.as_secs());
    unix.saturating_add(11_644_473_600)
}

fn text(b: &[u8]) -> String {
    format!("{:?}", String::from_utf8_lossy(b))
}

/// A frame as the call or answer it carries.
fn describe(frame: &[u8]) -> String {
    let Some(m) = decode_framed(frame) else { return format!("undecodable frame of {} bytes", frame.len()) };
    match m {
        Msg::CookieGet => "document.cookie".to_owned(),
        Msg::CookieSet { cookie_string } => format!("document.cookie = {}", text(&cookie_string)),
        Msg::StorageGetItem { key } => format!("localStorage.getItem({})", text(&key)),
        Msg::StorageSetItem { key, value } => format!("localStorage.setItem({}, {})", text(&key), text(&value)),
        Msg::StorageRemoveItem { key } => format!("localStorage.removeItem({})", text(&key)),
        Msg::StorageClear => "localStorage.clear()".to_owned(),
        Msg::StorageKey { index } => format!("localStorage.key({index})"),
        Msg::StorageLength => "localStorage.length".to_owned(),
        Msg::Navigate { url } => format!("navigate({})", text(&url)),
        Msg::Commit { url, script } => format!("commit {} with a script of {} bytes", text(&url), script.len()),
        Msg::CookieValue { cookie_string } => format!("result {}", text(&cookie_string)),
        Msg::StorageValue { value } => format!("result {}", value.map_or("null".to_owned(), |v| text(&v))),
        Msg::StorageLengthValue { length } => format!("result {length}"),
        Msg::Error { code } => format!("error code {code}"),
    }
}

impl Host {
    /// A host whose renderers are started with `command(id)` (stdio is set
    /// by the host).
    pub fn new(command: impl FnMut(u64) -> Command + 'static) -> Host {
        let (tx, rx) = channel();
        Host { state: init_record(), table: HashMap::new(), tx, rx, command: Box::new(command), log: Vec::new() }
    }

    /// Live renderers.
    pub fn live(&self) -> usize {
        self.table.len()
    }

    fn say(&mut self, line: String) {
        println!("{line}");
        self.log.push(line);
    }

    /// The kernel's step, unless its ids are used up (`step_requires`).
    fn step(&mut self, e: EventRecord) -> Vec<OutputRecord> {
        if self.state.next_id == u64::MAX {
            self.say("kernel ids exhausted; event dropped".to_owned());
            return Vec::new();
        }
        let s = std::mem::replace(&mut self.state, init_record());
        let (s, outputs) = step_real(s, &e);
        self.state = s;
        outputs
    }

    /// Give the kernel an event, after a `Tick`, and carry out its outputs.
    pub fn event(&mut self, e: EventRecord) {
        self.step(EventRecord::Tick { time: now() });
        let mut dead = Vec::new();
        for output in self.step(e) {
            match output {
                OutputRecord::Spawn { id } => {
                    if let Err(e) = self.spawn(id) {
                        self.say(format!("renderer {id}: cannot start: {e}"));
                        dead.push((id, "cannot start"));
                    }
                }
                OutputRecord::ToRenderer { id, bytes } => {
                    if !self.send(id, &bytes) {
                        dead.push((id, "cannot write"));
                    }
                }
                OutputRecord::Kill { id } => self.reap(id, "killed by the kernel", Duration::ZERO),
            }
        }
        for (id, why) in dead {
            self.exit(id, why);
        }
    }

    /// The user opens a tab at `url`; the script's format is `clazel-renderer`'s.
    pub fn open_tab(&mut self, url: &str, script: &str) {
        let url = url.chars().map(u32::from).collect();
        self.event(EventRecord::OpenTab { url, script: script.as_bytes().to_vec() });
    }

    /// The user navigates tab `tab` (the id of the renderer that opened it).
    pub fn navigate_tab(&mut self, tab: u64, url: &str, script: &str) {
        let url = url.chars().map(u32::from).collect();
        self.event(EventRecord::NavigateTab { tab, url, script: script.as_bytes().to_vec() });
    }

    fn spawn(&mut self, id: u64) -> std::io::Result<()> {
        let (host_end, child_end) = UnixStream::pair()?;
        host_end.set_write_timeout(Some(Duration::from_secs(5)))?;
        let reader = host_end.try_clone()?;
        let stdin: OwnedFd = child_end.into();
        let stdout = stdin.try_clone()?;
        let child = (self.command)(id).stdin(stdin).stdout(stdout).stderr(Stdio::piped()).spawn()?;
        let tx = self.tx.clone();
        std::thread::spawn(move || read_frames(id, reader, tx));
        self.table.insert(id, Renderer { sock: host_end, child });
        Ok(())
    }

    /// Write a frame to a renderer; false if its socket failed.
    fn send(&mut self, id: u64, frame: &[u8]) -> bool {
        let Some(r) = self.table.get_mut(&id) else { return true };
        let ok = r.sock.write_all(frame).is_ok();
        self.say(format!("renderer {id} <- {}", describe(frame)));
        ok
    }

    /// Close the socket, wait up to `grace` for the process to exit on its
    /// own, then kill it; report how it ended and what it wrote to stderr.
    fn reap(&mut self, id: u64, why: &str, grace: Duration) {
        let Some(mut r) = self.table.remove(&id) else { return };
        let _ = r.sock.shutdown(Shutdown::Both);
        let end = Instant::now().checked_add(grace).unwrap_or_else(Instant::now);
        while matches!(r.child.try_wait(), Ok(None)) && Instant::now() < end {
            std::thread::sleep(Duration::from_millis(10));
        }
        let _ = r.child.kill();
        let status = r.child.wait().map_or_else(|e| e.to_string(), |s| s.to_string());
        let mut stderr = String::new();
        if let Some(mut e) = r.child.stderr.take() {
            let _ = e.read_to_string(&mut stderr);
        }
        let stderr = stderr.trim();
        let note = if stderr.is_empty() { String::new() } else { format!("; stderr: {stderr}") };
        self.say(format!("renderer {id} exited: {why}; {status}{note}"));
    }

    /// A renderer is gone (or never started): tell the kernel.
    fn exit(&mut self, id: u64, why: &str) {
        self.reap(id, why, Duration::from_secs(1));
        self.event(EventRecord::RendererExited { id });
    }

    /// Handle one thing a renderer's socket reported, waiting up to `wait`.
    /// What a renderer the host no longer has sends is dropped.
    pub fn pump(&mut self, wait: Duration) -> bool {
        match self.rx.recv_timeout(wait) {
            Ok(Ev::Frame(id, bytes)) if self.table.contains_key(&id) => {
                self.say(format!("renderer {id} -> {}", describe(&bytes)));
                self.event(EventRecord::FromRenderer { id, bytes });
                true
            }
            Ok(Ev::Gone(id, why)) if self.table.contains_key(&id) => {
                self.exit(id, &why);
                true
            }
            Ok(_) => true,
            Err(_) => false,
        }
    }

    /// Pump until no renderer is left or `limit` passes; whether none is left.
    pub fn run(&mut self, limit: Duration) -> bool {
        let end = Instant::now().checked_add(limit).unwrap_or_else(Instant::now);
        while !self.table.is_empty() && Instant::now() < end {
            self.pump(Duration::from_millis(100));
        }
        self.table.is_empty()
    }
}

impl Drop for Host {
    fn drop(&mut self) {
        let ids: Vec<u64> = self.table.keys().copied().collect();
        for id in ids {
            self.reap(id, "host shutting down", Duration::ZERO);
        }
    }
}
