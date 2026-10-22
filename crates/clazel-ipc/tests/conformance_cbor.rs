//! CBOR profile conformance (docs/phases/phase-2.md item 2.2).
//!
//! The proofs show the decoder and encoder equal `spec.rs`. This file checks
//! the spec against the outside world:
//!
//! 1. Every vector of RFC 8949 Appendix A (`cbor/test-vectors`
//!    `appendix_a.json`, converted by `cargo xtask testdata`): vectors inside
//!    the profile must decode to the stated value and re-encode to the same
//!    bytes; every vector outside it must be rejected.
//! 2. A differential test against `minicbor` on random items and on random
//!    and mutated byte strings. `minicbor` accepts non-shortest arguments,
//!    so the only permitted difference is: we reject, and `minicbor`
//!    accepts bytes that are not its own re-encoding of what it read.

use clazel_ipc::cbor::decode::decode;
use clazel_ipc::cbor::encode::encode;
use clazel_ipc::cbor::token::Tok;

/// What a vector's tokens must be.
enum Exp {
    Uint(u64),
    Bytes(&'static [u8]),
    Text(&'static [u8]),
    Bool(bool),
    Array(u64),
}

struct Case {
    index: usize,
    bytes: &'static [u8],
    /// `None`: decode must fail.
    expected: Option<&'static [Exp]>,
}

include!("generated/cbor_appendix_a.rs");

fn matches(tok: &Tok, exp: &Exp) -> bool {
    match (tok, exp) {
        (Tok::Uint(a), Exp::Uint(b)) | (Tok::Array(a), Exp::Array(b)) => a == b,
        (Tok::Bytes(a), Exp::Bytes(b)) | (Tok::Text(a), Exp::Text(b)) => a.as_slice() == *b,
        (Tok::Bool(a), Exp::Bool(b)) => a == b,
        _ => false,
    }
}

#[test]
fn appendix_a() {
    let mut failures = Vec::new();
    let mut failed = 0usize;
    let mut inside = 0usize;
    for c in APPENDIX_A {
        let before = failures.len();
        let got = decode(c.bytes);
        match (c.expected, &got) {
            (None, None) => {}
            (Some(exp), Some(toks)) => {
                inside = inside.saturating_add(1);
                if toks.len() != exp.len() || !toks.iter().zip(exp).all(|(t, e)| matches(t, e)) {
                    failures.push(format!("appendix_a.json[{}]: decoded {toks:?}", c.index));
                } else if encode(toks) != c.bytes {
                    failures.push(format!("appendix_a.json[{}]: does not re-encode", c.index));
                }
            }
            (None, Some(toks)) => failures.push(format!(
                "appendix_a.json[{}]: outside the profile but decoded {toks:?}",
                c.index
            )),
            (Some(_), None) => failures.push(format!(
                "appendix_a.json[{}]: inside the profile but rejected",
                c.index
            )),
        }
        if failures.len() != before {
            failed = failed.saturating_add(1);
        }
    }
    // Summary line for the README table; format in xtask/src/conformance.rs.
    println!(
        "clazel-conformance: suite=\"RFC 8949 Appendix A (cbor/test-vectors)\" pass={} xfail=0 fail={failed} total={}",
        APPENDIX_A.len().saturating_sub(failed),
        APPENDIX_A.len()
    );
    assert_eq!(APPENDIX_A.len(), 82, "appendix_a.json has 82 vectors");
    assert_eq!(inside, 26, "26 vectors lie inside the profile");
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

/// A small deterministic generator (xorshift), so failures reproduce.
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }
    fn below(&mut self, n: usize) -> usize {
        usize::try_from(
            self.next()
                .checked_rem(u64::try_from(n).unwrap_or(1))
                .unwrap_or(0),
        )
        .unwrap_or(0)
    }
}

/// An item as a tree, to feed `minicbor`.
#[derive(Debug, Clone, PartialEq)]
enum Ex {
    Uint(u64),
    Bytes(Vec<u8>),
    Text(String),
    Bool(bool),
    Array(Vec<Ex>),
}

fn random_uint(r: &mut Rng) -> u64 {
    // Values around every argument-width boundary.
    let edges: [u64; 12] = [
        0,
        23,
        24,
        255,
        256,
        65535,
        65536,
        4_294_967_295,
        4_294_967_296,
        u64::MAX,
        1,
        1000,
    ];
    match r.below(3) {
        0 => *edges.get(r.below(edges.len())).unwrap_or(&0),
        1 => r.next() >> r.below(64),
        _ => u64::try_from(r.below(300)).unwrap_or(0),
    }
}

fn random_text(r: &mut Rng) -> String {
    let n = r.below(30);
    (0..n)
        .map(|_| match r.below(4) {
            0 => 'é',
            1 => '水',
            2 => '\u{10151}',
            _ => char::from(b'a'.saturating_add(u8::try_from(r.below(26)).unwrap_or(0))),
        })
        .collect()
}

fn random_item(r: &mut Rng, depth: usize) -> Ex {
    match r.below(if depth == 0 { 4 } else { 5 }) {
        0 => Ex::Uint(random_uint(r)),
        1 => Ex::Bytes(
            (0..r.below(40))
                .map(|_| u8::try_from(r.below(256)).unwrap_or(0))
                .collect(),
        ),
        2 => Ex::Text(random_text(r)),
        3 => Ex::Bool(r.below(2) == 0),
        _ => Ex::Array(
            (0..r.below(5))
                .map(|_| random_item(r, depth.saturating_sub(1)))
                .collect(),
        ),
    }
}

fn flatten(e: &Ex, out: &mut Vec<Tok>) {
    match e {
        Ex::Uint(n) => out.push(Tok::Uint(*n)),
        Ex::Bytes(b) => out.push(Tok::Bytes(b.clone())),
        Ex::Text(s) => out.push(Tok::Text(s.as_bytes().to_vec())),
        Ex::Bool(b) => out.push(Tok::Bool(*b)),
        Ex::Array(items) => {
            out.push(Tok::Array(u64::try_from(items.len()).unwrap_or(0)));
            for i in items {
                flatten(i, out);
            }
        }
    }
}

fn mini_encode(e: &Ex, enc: &mut minicbor::Encoder<Vec<u8>>) {
    // Writing to a Vec cannot fail.
    match e {
        Ex::Uint(n) => {
            let _ = enc.u64(*n);
        }
        Ex::Bytes(b) => {
            let _ = enc.bytes(b);
        }
        Ex::Text(s) => {
            let _ = enc.str(s);
        }
        Ex::Bool(b) => {
            let _ = enc.bool(*b);
        }
        Ex::Array(items) => {
            let _ = enc.array(u64::try_from(items.len()).unwrap_or(0));
            for i in items {
                mini_encode(i, enc);
            }
        }
    }
}

/// Read one item with `minicbor`, in the profile's types only. `None` for
/// anything else, including a decode error. Accepts non-shortest forms.
fn mini_read(d: &mut minicbor::Decoder<'_>, depth: usize) -> Option<Ex> {
    use minicbor::data::Type;
    if depth > 64 {
        return None;
    }
    match d.datatype().ok()? {
        Type::U8 | Type::U16 | Type::U32 | Type::U64 => Some(Ex::Uint(d.u64().ok()?)),
        Type::Bytes => Some(Ex::Bytes(d.bytes().ok()?.to_vec())),
        Type::String => Some(Ex::Text(d.str().ok()?.to_owned())),
        Type::Bool => Some(Ex::Bool(d.bool().ok()?)),
        Type::Array => {
            let n = d.array().ok()??;
            let mut items = Vec::new();
            for _ in 0..n {
                items.push(mini_read(d, depth.saturating_add(1))?);
            }
            Some(Ex::Array(items))
        }
        _ => None,
    }
}

fn mini_parse(bytes: &[u8]) -> Option<Ex> {
    let mut d = minicbor::Decoder::new(bytes);
    let e = mini_read(&mut d, 0)?;
    (d.position() == bytes.len()).then_some(e)
}

fn mini_bytes(e: &Ex) -> Vec<u8> {
    let mut enc = minicbor::Encoder::new(Vec::new());
    mini_encode(e, &mut enc);
    enc.into_writer()
}

#[test]
fn differential_random_items() {
    let mut r = Rng(0x2545_F491_4F6C_DD1D);
    let cases = if cfg!(miri) { 200 } else { 20_000usize };
    let mut failed = 0usize;
    for n in 0..cases {
        let item = random_item(&mut r, 3);
        let mut toks = Vec::new();
        flatten(&item, &mut toks);
        let theirs = mini_bytes(&item);
        let ours = encode(&toks);
        let ok = ours == theirs
            && decode(&theirs).is_some_and(|d| d == toks)
            && mini_parse(&ours).as_ref() == Some(&item);
        if !ok {
            failed = failed.saturating_add(1);
            eprintln!("random item {n}: {item:?}: ours {ours:02X?}, minicbor {theirs:02X?}");
        }
    }
    println!(
        "clazel-conformance: suite=\"minicbor differential: random items\" pass={} xfail=0 fail={failed} total={cases}",
        cases.saturating_sub(failed)
    );
    assert_eq!(failed, 0);
}

/// Mutate an encoding: flip, drop, insert or widen bytes.
fn mutate(r: &mut Rng, mut b: Vec<u8>) -> Vec<u8> {
    for _ in 0..=r.below(3) {
        match r.below(5) {
            0 if !b.is_empty() => {
                let i = r.below(b.len());
                if let Some(x) = b.get_mut(i) {
                    *x = u8::try_from(r.below(256)).unwrap_or(0);
                }
            }
            1 if !b.is_empty() => {
                let i = r.below(b.len());
                b.remove(i);
            }
            2 => {
                let i = r.below(b.len().saturating_add(1));
                b.insert(i, u8::try_from(r.below(256)).unwrap_or(0));
            }
            3 if !b.is_empty() => {
                // Rewrite the first argument in a wider (non-shortest) form.
                let (&ib, rest) = b.split_first().unwrap_or((&0, &[]));
                let v = ib % 32;
                if v < 24 {
                    let (ai, n) = [(24u8, 1usize), (25, 2), (26, 4), (27, 8)]
                        .get(r.below(4))
                        .copied()
                        .unwrap_or((24, 1));
                    let mut w = vec![ib.saturating_sub(v).saturating_add(ai)];
                    w.extend(std::iter::repeat_n(0u8, n.saturating_sub(1)));
                    w.push(v);
                    w.extend_from_slice(rest);
                    b = w;
                }
            }
            _ => b.truncate(r.below(b.len().saturating_add(1))),
        }
    }
    b
}

#[test]
fn differential_random_bytes() {
    let mut r = Rng(0x9E37_79B9_7F4A_7C15);
    let cases = if cfg!(miri) { 500 } else { 60_000usize };
    let mut failed = 0usize;
    let (mut both, mut only_theirs) = (0usize, 0usize);
    for n in 0..cases {
        let bytes = if r.below(4) == 0 {
            (0..r.below(12))
                .map(|_| u8::try_from(r.below(256)).unwrap_or(0))
                .collect()
        } else {
            let base = mini_bytes(&random_item(&mut r, 3));
            mutate(&mut r, base)
        };
        let ours = decode(&bytes);
        let theirs = mini_parse(&bytes);
        let ok = match (&ours, &theirs) {
            (Some(o), Some(t)) => {
                both = both.saturating_add(1);
                let mut want = Vec::new();
                flatten(t, &mut want);
                *o == want && encode(o) == bytes
            }
            // The only permitted difference: minicbor accepts what is not
            // its own (shortest-form) encoding of what it read.
            (None, Some(t)) => {
                only_theirs = only_theirs.saturating_add(1);
                mini_bytes(t) != bytes
            }
            (None, None) => true,
            (Some(_), None) => false,
        };
        if !ok {
            failed = failed.saturating_add(1);
            eprintln!("random bytes {n}: {bytes:02X?}: ours {ours:?}, minicbor {theirs:?}");
        }
    }
    println!(
        "clazel-conformance: suite=\"minicbor differential: random and mutated bytes\" pass={} xfail=0 fail={failed} total={cases}",
        cases.saturating_sub(failed)
    );
    // Both kinds of input must be well represented: over 1000 each in the
    // full run, and in the same proportion under Miri.
    let floor = cases / 60;
    assert!(both > floor && only_theirs > floor, "{both} {only_theirs}");
    assert_eq!(failed, 0);
}
