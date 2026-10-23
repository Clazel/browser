//! WPT `webstorage/` conformance (docs/phases/phase-2.md item 2.12).
//!
//! The proofs show the exec kernel equals `spec.rs`; this file checks the
//! spec against the web platform's own `localStorage` tests, through the
//! proven code. Every case of the table converted from the vendored files
//! (`tests/data/wpt-webstorage/`, whose `SOURCE.md` says which and which
//! not) is run as a fake renderer would run it: the kernel opens a tab on
//! `http://web-platform.test:8000/webstorage/<file>` (a new renderer is
//! spawned and sent a `Commit`), and the renderer sends one frame per call,
//! through the IPC codec, and checks each reply frame against the test's
//! assertion. A call with no result (`setItem`, `removeItem`, `clear`) must
//! get no reply at all. Every case starts with a fresh kernel.
//!
//! The URL functions are the real ones (`step_real`, item 2.13).
//! Under Miri every 6th case is run.

mod support;

use clazel_ipc::message::codec::Msg;
use support::{Kernel, Out};

/// One operation of a test, on `localStorage`.
enum Op {
    Clear,
    Set(&'static [u8], &'static [u8]),
    Remove(&'static [u8]),
    /// `getItem(key)` is the value, or `None` for no such key.
    Get(&'static [u8], Option<&'static [u8]>),
    /// The key exists, or not.
    Has(&'static [u8], bool),
    Length(u64),
}

/// One converted case.
struct Case {
    file: &'static str,
    index: usize,
    name: &'static str,
    ops: &'static [Op],
}

// `const WPT_WEBSTORAGE: &[Case]`, generated from the vendored files.
include!("generated/wpt_webstorage.rs");

/// Cases that are expected to fail: (file, name, reason). None.
const XFAIL: &[(&str, &str, &str)] = &[];

/// What the renderer `id` must get back for a call with a reply, or nothing.
fn expect_reply(out: &[Out], id: u64, want: Option<Msg>) -> bool {
    match (out, want) {
        ([], None) => true,
        ([Out::To(to, got)], Some(want)) => *to == id && *got == want,
        _ => false,
    }
}

/// Run one case; whether every assertion held.
fn run(c: &Case) -> bool {
    let mut kernel = Kernel::new();
    let (Some(id), _) = kernel.open_tab(
        &format!("http://web-platform.test:8000/webstorage/{}", c.file),
        "",
    ) else {
        return false;
    };
    for op in c.ops {
        let ok = match op {
            Op::Clear => expect_reply(&kernel.send(id, &Msg::StorageClear), id, None),
            Op::Set(key, value) => expect_reply(
                &kernel.send(
                    id,
                    &Msg::StorageSetItem {
                        key: key.to_vec(),
                        value: value.to_vec(),
                    },
                ),
                id,
                None,
            ),
            Op::Remove(key) => expect_reply(
                &kernel.send(id, &Msg::StorageRemoveItem { key: key.to_vec() }),
                id,
                None,
            ),
            Op::Get(key, want) => expect_reply(
                &kernel.send(id, &Msg::StorageGetItem { key: key.to_vec() }),
                id,
                Some(Msg::StorageValue {
                    value: want.map(<[u8]>::to_vec),
                }),
            ),
            Op::Has(key, present) => match kernel
                .send(id, &Msg::StorageGetItem { key: key.to_vec() })
                .as_slice()
            {
                [Out::To(to, Msg::StorageValue { value })] => {
                    *to == id && value.is_some() == *present
                }
                _ => false,
            },
            Op::Length(n) => expect_reply(
                &kernel.send(id, &Msg::StorageLength),
                id,
                Some(Msg::StorageLengthValue { length: *n }),
            ),
        };
        if !ok {
            return false;
        }
    }
    true
}

#[test]
fn wpt_webstorage() {
    let step = if cfg!(miri) { 6 } else { 1 };
    let mut pass: u64 = 0;
    let mut xfail: u64 = 0;
    let mut failed: u64 = 0;
    let mut total: u64 = 0;
    for c in WPT_WEBSTORAGE.iter().step_by(step) {
        total = total.saturating_add(1);
        let ok = run(c);
        let expected_failure = XFAIL.iter().find(|(f, n, _)| *f == c.file && *n == c.name);
        match (ok, expected_failure) {
            (true, None) => pass = pass.saturating_add(1),
            (false, Some(_)) => xfail = xfail.saturating_add(1),
            (true, Some((_, _, reason))) => {
                failed = failed.saturating_add(1);
                println!(
                    "FAIL (expected to fail, but passes: {reason}) {}[{}] {:?}",
                    c.file, c.index, c.name
                );
            }
            (false, None) => {
                failed = failed.saturating_add(1);
                println!("FAIL {}[{}] {:?}", c.file, c.index, c.name);
            }
        }
    }
    if !cfg!(miri) {
        assert_eq!(
            total,
            u64::try_from(WPT_WEBSTORAGE.len()).unwrap_or(u64::MAX)
        );
    }
    println!(
        "clazel-conformance: suite=\"WPT webstorage/ localStorage calls\" pass={pass} xfail={xfail} fail={failed} total={total}"
    );
    assert_eq!(failed, 0);
}
