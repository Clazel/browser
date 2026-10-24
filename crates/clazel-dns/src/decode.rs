//! The executable decoder, proven to meet [`super::contract`].
//!
//! It follows [`super::spec`] step by step (the step comments and quotes
//! live there). The name decoder is one loop whose state is the arguments
//! of `spec::read_name`; the sections are loops that push only the
//! questions and records they have read, never reserving room for a count
//! the header declares (`lemmas::lemma_decode_alloc_bound`).

use super::spec;
use super::spec::Header;
use super::types::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// `o` as an optional `nat`.
pub open spec fn opt_nat(o: Option<usize>) -> Option<nat> {
    match o {
        Some(e) => Some(e as nat),
        None => None,
    }
}

/// Append `input[from..to]` to `out`.
pub(crate) fn append_range(out: &mut Vec<u8>, input: &[u8], from: usize, to: usize)
    requires
        from <= to <= input.len(),
    ensures
        final(out)@ == old(out)@ + input@.subrange(from as int, to as int),
{
    let ghost start = out@;
    let mut j: usize = from;
    while j < to
        invariant
            from <= j <= to,
            to <= input.len(),
            out@ == start + input@.subrange(from as int, j as int),
        decreases to - j,
    {
        if let Some(c) = input.get(j) {
            out.push(*c);
        }
        j = j.saturating_add(1);
        assert(out@ =~= start + input@.subrange(from as int, j as int));
    }
}

/// A copy of `input[from..to]`.
pub(crate) fn copy_range(input: &[u8], from: usize, to: usize) -> (out: Vec<u8>)
    requires
        from <= to <= input.len(),
    ensures
        out@ == input@.subrange(from as int, to as int),
{
    let mut out: Vec<u8> = Vec::new();
    append_range(&mut out, input, from, to);
    assert(Seq::<u8>::empty() + input@.subrange(from as int, to as int) =~= input@.subrange(from as int, to as int));
    out
}

/// The 16-bit field at `pos`.
pub(crate) fn read_u16(input: &[u8], pos: usize) -> (v: u16)
    requires
        pos + 2 <= input.len(),
    ensures
        v as nat == spec::u16_at(input@, pos as nat),
{
    let hi = match input.get(pos) {
        Some(&b) => b,
        None => 0,
    };
    // pos + 2 <= input.len(), so this does not saturate.
    let lo = match input.get(pos.saturating_add(1)) {
        Some(&b) => b,
        None => 0,
    };
    // hi * 256 + lo <= 65535: neither saturates.
    (hi as u16).saturating_mul(256).saturating_add(lo as u16)
}

/// The 32-bit field at `pos`.
pub(crate) fn read_u32(input: &[u8], pos: usize) -> (v: u32)
    requires
        pos + 4 <= input.len(),
    ensures
        v as nat == spec::u32_at(input@, pos as nat),
{
    let hi = read_u16(input, pos);
    // pos + 4 <= input.len(), so this does not saturate.
    let lo = read_u16(input, pos.saturating_add(2));
    // hi * 65536 + lo <= 2^32 - 1: neither saturates.
    (hi as u32).saturating_mul(65536).saturating_add(lo as u32)
}

/// The 128-bit field at `pos`: sixteen octets in network byte order.
pub(crate) fn read_u128(input: &[u8], pos: usize) -> (v: u128)
    requires
        pos + 16 <= input.len(),
    ensures
        v as nat == spec::be_value(input@.subrange(pos as int, pos as int + 16)),
{
    let mut k: usize = 0;
    let mut acc: u128 = 0;
    while k < 16
        invariant
            k <= 16,
            pos + 16 <= input.len(),
            acc as nat == spec::be_value(input@.subrange(pos as int, pos as int + k as int)),
        decreases 16 - k,
    {
        // pos + k < input.len(), so this does not saturate.
        let b = match input.get(pos.saturating_add(k)) {
            Some(&b) => b,
            None => 0,
        };
        proof {
            let s = input@.subrange(pos as int, pos as int + k as int + 1);
            let init = input@.subrange(pos as int, pos as int + k as int);
            assert(s.drop_last() =~= init);
            assert(s.last() == input@[pos as int + k as int]);
            super::lemmas::lemma_be_value_bound(init);
            super::lemmas::lemma_pow256_up_to_16(k as nat + 1);
            assert(super::lemmas::pow256(k as nat + 1) == 256 * super::lemmas::pow256(k as nat));
            assert(acc as nat * 256 + 255 <= 0xFFFF_FFFF_FFFF_FFFF_FFFF_FFFF_FFFF_FFFF);
        }
        // acc * 256 + b <= 2^128 - 1 (shown above): neither saturates.
        acc = acc.saturating_mul(256).saturating_add(b as u128);
        k = k.saturating_add(1);
    }
    acc
}

/// §4.1.1: the header.
pub(crate) fn header_at(input: &[u8]) -> (r: Option<Header>)
    ensures
        r == spec::decode_header(input@),
{
    if input.len() < 12 {
        return None;
    }
    let w = read_u16(input, 2);
    let z = (w / 16) % 8;
    if z != 0 {
        return None;
    }
    Some(Header {
        id: read_u16(input, 0),
        qr: (w / 32768) % 2 == 1,
        opcode: ((w / 2048) % 16) as u8,
        aa: (w / 1024) % 2 == 1,
        tc: (w / 512) % 2 == 1,
        rd: (w / 256) % 2 == 1,
        ra: (w / 128) % 2 == 1,
        z: z as u8,
        rcode: (w % 16) as u8,
        qdcount: read_u16(input, 4),
        ancount: read_u16(input, 6),
        nscount: read_u16(input, 8),
        arcount: read_u16(input, 10),
    })
}

/// §3.1 and §4.1.4: the domain name at `start`, which must end at or
/// before `limit0` (`spec::decode_name` and the CNAME case of
/// `spec::decode_rdata`).
pub(crate) fn name_at(input: &[u8], start: usize, limit0: usize) -> (r: Option<(Vec<u8>, usize)>)
    ensures
        match r {
            Some((w, e)) => spec::read_name(input@, start as nat, limit0 as nat, seq![], None) == Some((w@, e as nat)),
            None => spec::read_name(input@, start as nat, limit0 as nat, seq![], None) is None,
        },
{
    if start >= limit0 {
        return None;
    }
    let mut pos: usize = start;
    let mut limit: usize = limit0;
    let mut acc: Vec<u8> = Vec::new();
    let mut end: Option<usize> = None;
    loop
        invariant
            acc@.len() <= 254,
            pos <= limit,
            spec::read_name(input@, pos as nat, limit as nat, acc@, opt_nat(end)) == spec::read_name(
                input@,
                start as nat,
                limit0 as nat,
                seq![],
                None,
            ),
        decreases limit, limit - pos,
    {
        if pos >= limit || limit > input.len() {
            return None;
        }
        let len = match input.get(pos) {
            Some(&b) => b,
            None => return None,
        };
        if len == 0 {
            // §3.1: "a domain name is terminated by a length byte of zero".
            acc.push(0);
            let e = match end {
                Some(e) => e,
                None => pos.saturating_add(1),
            };
            return Some((acc, e));
        } else if len < 64 {
            // §4.1.4: a label of `len` octets.
            let l = len as usize;
            // pos < limit, so pos + 1 + l > limit exactly when l >= limit - pos.
            if l >= limit.saturating_sub(pos) {
                return None;
            }
            // acc is at most 254 long: this does not saturate.
            if acc.len().saturating_add(1).saturating_add(l) > 254 {
                return None;
            }
            // pos + 1 + l <= limit: this does not saturate.
            let next = pos.saturating_add(1).saturating_add(l);
            append_range(&mut acc, input, pos, next);
            pos = next;
        } else if len >= 192 {
            // §4.1.4: a pointer, two octets.
            if limit.saturating_sub(pos) < 2 {
                return None;
            }
            // pos + 2 <= limit <= input.len(), so this does not saturate.
            let second = match input.get(pos.saturating_add(1)) {
                Some(&b) => b,
                None => return None,
            };
            // (len - 192) * 256 + second <= 63 * 256 + 255: neither
            // operation can overflow or saturate.
            let target = ((len as usize).saturating_sub(192)).saturating_mul(256).saturating_add(second as usize);
            if target >= pos {
                // "a prior occurance": a target at or after the pointer is
                // not one.
                return None;
            }
            end = match end {
                Some(e) => Some(e),
                None => Some(pos.saturating_add(2)),
            };
            // The name continues at the target and must end before this
            // pointer.
            limit = pos;
            pos = target;
        } else {
            // §4.1.4: the 10 and 01 combinations are reserved.
            return None;
        }
    }
}

/// §4.1.2: the question at `pos`.
fn question_at(input: &[u8], pos: usize) -> (r: Option<(Quest, usize)>)
    ensures
        match r {
            Some((q, e)) => spec::read_question(input@, pos as nat) == Some((q@, e as nat)),
            None => spec::read_question(input@, pos as nat) is None,
        },
{
    let (name, p) = name_at(input, pos, input.len())?;
    proof {
        super::lemmas::lemma_read_name_end(input@, pos as nat, input@.len(), seq![], None);
    }
    // p + 4 > input.len() exactly when p > input.len() - 4 (p >= 1).
    if p > input.len().saturating_sub(4) {
        return None;
    }
    let qtype = read_u16(input, p);
    // p + 4 <= input.len(), so this does not saturate.
    let qclass = read_u16(input, p.saturating_add(2));
    Some((Quest { name, qtype, qclass }, p.saturating_add(4)))
}

/// §3.3.1, §3.4.1 and RFC 3596 §2.2: the RDATA from `rstart` to `rend`.
fn rdata_at(input: &[u8], rtype: u16, rclass: u16, rstart: usize, rend: usize) -> (r: Option<Rd>)
    requires
        rstart <= rend <= input.len(),
    ensures
        match r {
            Some(d) => spec::decode_rdata(input@, rtype, rclass, rstart as nat, rend as nat) == Some(d@),
            None => spec::decode_rdata(input@, rtype, rclass, rstart as nat, rend as nat) is None,
        },
{
    let rdlength = rend.saturating_sub(rstart);
    if rclass == spec::CLASS_IN && rtype == spec::TYPE_A {
        if rdlength == 4 {
            Some(Rd::A(read_u32(input, rstart)))
        } else {
            None
        }
    } else if rclass == spec::CLASS_IN && rtype == spec::TYPE_AAAA {
        if rdlength == 16 {
            Some(Rd::Aaaa(read_u128(input, rstart)))
        } else {
            None
        }
    } else if rclass == spec::CLASS_IN && rtype == spec::TYPE_CNAME {
        match name_at(input, rstart, rend) {
            Some((name, e)) => {
                if e == rend {
                    Some(Rd::Cname(name))
                } else {
                    None
                }
            },
            None => None,
        }
    } else {
        Some(Rd::Opaque(copy_range(input, rstart, rend)))
    }
}

/// §4.1.3: the resource record at `pos`.
fn record_at(input: &[u8], pos: usize) -> (r: Option<(Rec, usize)>)
    ensures
        match r {
            Some((rec, e)) => spec::read_rr(input@, pos as nat) == Some((rec@, e as nat)),
            None => spec::read_rr(input@, pos as nat) is None,
        },
{
    let (name, p) = name_at(input, pos, input.len())?;
    proof {
        super::lemmas::lemma_read_name_end(input@, pos as nat, input@.len(), seq![], None);
    }
    // p + 10 > input.len() exactly when p > input.len() - 10 (p >= 1).
    if p > input.len().saturating_sub(10) {
        return None;
    }
    // p + 10 <= input.len(): none of these saturates.
    let rdlength = read_u16(input, p.saturating_add(8)) as usize;
    let rstart = p.saturating_add(10);
    // rstart <= input.len(), so rstart + rdlength > input.len() exactly
    // when rdlength > input.len() - rstart.
    if rdlength > input.len().saturating_sub(rstart) {
        return None;
    }
    // rstart + rdlength <= input.len(): this does not saturate.
    let rend = rstart.saturating_add(rdlength);
    let rtype = read_u16(input, p);
    let rclass = read_u16(input, p.saturating_add(2));
    let ttl = read_u32(input, p.saturating_add(4));
    let rdata = rdata_at(input, rtype, rclass, rstart, rend)?;
    Some((Rec { name, rtype, rclass, ttl, rdata }, rend))
}

/// §4.1.2: `n` questions from `pos`.
fn questions_at(input: &[u8], start: usize, n: usize) -> (r: Option<(Vec<Quest>, usize)>)
    requires
        start <= input.len(),
    ensures
        match r {
            Some((qs, e)) => spec::read_questions(input@, start as nat, n as nat, seq![]) == Some((quest_views(qs@), e as nat))
                && qs@.len() == n && e <= input.len(),
            None => spec::read_questions(input@, start as nat, n as nat, seq![]) is None,
        },
{
    let mut pos: usize = start;
    let mut questions: Vec<Quest> = Vec::new();
    let mut i: usize = 0;
    proof {
        assert(quest_views(questions@) =~= Seq::<spec::Question>::empty());
    }
    while i < n
        invariant
            i <= n,
            pos <= input.len(),
            questions@.len() == i,
            spec::read_questions(input@, pos as nat, (n - i) as nat, quest_views(questions@)) == spec::read_questions(
                input@,
                start as nat,
                n as nat,
                seq![],
            ),
        decreases n - i,
    {
        let (q, e) = question_at(input, pos)?;
        proof {
            super::lemmas::lemma_read_question_progress(input@, pos as nat);
            lemma_quest_views_push(questions@, q);
        }
        questions.push(q);
        pos = e;
        // i < n, so this does not saturate.
        i = i.saturating_add(1);
    }
    Some((questions, pos))
}

/// §4.1.3: `n` resource records from `pos`.
fn records_at(input: &[u8], start: usize, n: usize) -> (r: Option<(Vec<Rec>, usize)>)
    requires
        start <= input.len(),
    ensures
        match r {
            Some((rs, e)) => spec::read_rrs(input@, start as nat, n as nat, seq![]) == Some((rec_views(rs@), e as nat))
                && rs@.len() == n && e <= input.len(),
            None => spec::read_rrs(input@, start as nat, n as nat, seq![]) is None,
        },
{
    let mut pos: usize = start;
    let mut records: Vec<Rec> = Vec::new();
    let mut i: usize = 0;
    proof {
        assert(rec_views(records@) =~= Seq::<spec::Rr>::empty());
    }
    while i < n
        invariant
            i <= n,
            pos <= input.len(),
            records@.len() == i,
            spec::read_rrs(input@, pos as nat, (n - i) as nat, rec_views(records@)) == spec::read_rrs(
                input@,
                start as nat,
                n as nat,
                seq![],
            ),
        decreases n - i,
    {
        let (r, e) = record_at(input, pos)?;
        proof {
            super::lemmas::lemma_read_rr_progress(input@, pos as nat);
            lemma_rec_views_push(records@, r);
        }
        records.push(r);
        pos = e;
        // i < n, so this does not saturate.
        i = i.saturating_add(1);
    }
    Some((records, pos))
}

/// §4.1: decode a message. `None` unless the bytes are exactly one
/// message. The decoded sections hold only the questions and records that
/// were read, so no more than the input has octets.
pub fn decode_message(input: &[u8]) -> (output: Option<Msg>)
    ensures
        super::contract::decode_message_ensures(input@, option_msg(output)),
        super::contract::decode_alloc_ensures(
            input@.len(),
            match output {
                Some(m) => Some(m.questions@.len() + m.answers@.len() + m.authority@.len() + m.additional@.len()),
                None => None,
            },
        ),
{
    if input.len() > spec::MAX_TCP {
        return None;
    }
    let header = header_at(input)?;
    let (questions, p1) = questions_at(input, 12, header.qdcount as usize)?;
    let (answers, p2) = records_at(input, p1, header.ancount as usize)?;
    let (authority, p3) = records_at(input, p2, header.nscount as usize)?;
    let (additional, p4) = records_at(input, p3, header.arcount as usize)?;
    if p4 != input.len() {
        return None;
    }
    proof {
        super::lemmas::lemma_decode_alloc_bound(input@);
    }
    Some(Msg { header, questions, answers, authority, additional })
}

/// §2.3.4: decode a datagram, at most 512 octets.
pub fn decode_udp(input: &[u8]) -> (output: Option<Msg>)
    ensures
        super::contract::decode_udp_ensures(input@, option_msg(output)),
        super::contract::decode_alloc_ensures(
            input@.len(),
            match output {
                Some(m) => Some(m.questions@.len() + m.answers@.len() + m.authority@.len() + m.additional@.len()),
                None => None,
            },
        ),
{
    if input.len() > spec::MAX_UDP {
        return None;
    }
    decode_message(input)
}

} // verus!
