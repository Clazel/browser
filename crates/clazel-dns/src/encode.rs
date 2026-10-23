//! The executable query builder and the TCP length prefix, proven to meet
//! [`super::contract`]. Each follows [`super::spec`] (the quotes live
//! there).

use super::decode::{append_range, read_u16};
use super::spec;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Scan a dotted name; see `spec::dotted_scan`. The wire format of the
/// labels, without the final zero octet.
fn scan(s: &[u8]) -> (r: Option<Vec<u8>>)
    ensures
        super::types::opt_bytes(r) == spec::dotted_scan(s@, 0, 0, seq![]),
{
    let mut i: usize = 0;
    let mut start: usize = 0;
    let mut acc: Vec<u8> = Vec::new();
    while i < s.len()
        invariant
            start <= i <= s.len(),
            acc@.len() == start,
            spec::dotted_scan(s@, i as nat, start as nat, acc@) == spec::dotted_scan(s@, 0, 0, seq![]),
        decreases s.len() - i,
    {
        let c = match s.get(i) {
            Some(&c) => c,
            None => return None,
        };
        if c == 46 {
            // i >= start, so this does not saturate.
            let label_len = i.saturating_sub(start);
            if label_len == 0 || label_len > spec::MAX_LABEL {
                return None;
            }
            let ghost old_acc = acc@;
            acc.push(label_len as u8);
            append_range(&mut acc, s, start, i);
            assert(acc@ =~= old_acc + seq![label_len as u8] + s@.subrange(start as int, i as int));
            // i < s.len(), so this does not saturate.
            i = i.saturating_add(1);
            start = i;
        } else if c >= 128 {
            return None;
        } else {
            // i < s.len(), so this does not saturate.
            i = i.saturating_add(1);
        }
    }
    // i == s.len() >= start.
    if i > start {
        let label_len = i.saturating_sub(start);
        if label_len > spec::MAX_LABEL {
            return None;
        }
        let ghost old_acc = acc@;
        acc.push(label_len as u8);
        append_range(&mut acc, s, start, i);
        assert(acc@ =~= old_acc + seq![label_len as u8] + s@.subrange(start as int, i as int));
    }
    Some(acc)
}

/// A host name as a dotted ASCII string, in wire format; see
/// `spec::dotted_to_wire`.
pub fn dotted_to_wire(s: &[u8]) -> (output: Option<Vec<u8>>)
    ensures
        super::contract::dotted_to_wire_ensures(s@, super::types::opt_bytes(output)),
{
    if s.is_empty() {
        return None;
    }
    let is_root = match s.first() {
        Some(&c) => s.len() == 1 && c == 46,
        None => false,
    };
    proof {
        // `s` is the root exactly when it is the single octet ".".
        if is_root {
            assert(s@ =~= seq![46u8]);
        } else if s@.len() == 1 {
            assert(s@[0] != 46);
            assert(s@ != seq![46u8]);
        } else {
            assert(s@ != seq![46u8]);
        }
    }
    if is_root {
        // "." alone is the root.
        let mut root: Vec<u8> = Vec::new();
        append_range(&mut root, [0u8].as_slice(), 0, 1);
        assert(root@ =~= seq![0u8]);
        return Some(root);
    }
    let mut w = scan(s)?;
    // w holds the labels: at most `s.len()` octets, so this does not
    // saturate.
    if w.len().saturating_add(1) > spec::MAX_NAME {
        return None;
    }
    let ghost labels = w@;
    w.push(0);
    assert(w@ =~= labels + seq![0u8]);
    Some(w)
}

/// A standard query: see `spec::encode_query`.
pub fn encode_query(id: u16, name: &[u8], qtype: u16) -> (output: Option<Vec<u8>>)
    ensures
        super::contract::encode_query_ensures(id, name@, qtype, super::types::opt_bytes(output)),
{
    let w = dotted_to_wire(name)?;
    // The ID, then the flags word 0x0100 (only RD), then QDCOUNT 1 and
    // ANCOUNT, NSCOUNT, ARCOUNT 0.
    let header: [u8; 12] = [(id / 256) as u8, (id % 256) as u8, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0];
    let mut out: Vec<u8> = Vec::new();
    append_range(&mut out, header.as_slice(), 0, 12);
    assert(out@ =~= spec::query_header_bytes(id));
    append_range(&mut out, w.as_slice(), 0, w.len());
    // QTYPE, then QCLASS IN.
    let tail: [u8; 4] = [(qtype / 256) as u8, (qtype % 256) as u8, 0, 1];
    append_range(&mut out, tail.as_slice(), 0, 4);
    assert(out@ =~= spec::query_header_bytes(id) + w@ + spec::be16(qtype as nat) + spec::be16(spec::CLASS_IN as nat));
    Some(out)
}

/// §4.2.2: a message with its two octet length prefix; see
/// `spec::tcp_frame`.
pub fn tcp_frame(msg: &[u8]) -> (output: Option<Vec<u8>>)
    ensures
        super::contract::tcp_frame_ensures(msg@, super::types::opt_bytes(output)),
{
    if msg.len() > spec::MAX_TCP {
        return None;
    }
    let prefix: [u8; 2] = [(msg.len() / 256) as u8, (msg.len() % 256) as u8];
    let mut out: Vec<u8> = Vec::new();
    append_range(&mut out, prefix.as_slice(), 0, 2);
    append_range(&mut out, msg, 0, msg.len());
    assert(out@ =~= spec::be16(msg@.len()) + msg@);
    Some(out)
}

/// §4.2.2: the length of the message at the start of `input`, once the
/// length prefix and the whole message have arrived; see
/// `spec::tcp_message_len`.
pub fn tcp_message_len(input: &[u8]) -> (output: Option<usize>)
    ensures
        super::contract::tcp_message_len_ensures(input@, super::decode::opt_nat(output)),
{
    if input.len() < 2 {
        return None;
    }
    let n = read_u16(input, 0) as usize;
    // n <= 65535, so this does not saturate.
    if input.len() < n.saturating_add(2) {
        return None;
    }
    Some(n)
}

} // verus!
