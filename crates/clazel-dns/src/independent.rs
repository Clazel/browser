//! A second transcription of the message format, from RFC 883 "Domain Names
//! - Implementation and Specification" (Mockapetris, November 1983,
//! <https://www.rfc-editor.org/rfc/rfc883>), §4 "Messages": "Header section
//! format", "Question section format", "Resource record format" and "Domain
//! name representation and compression", with RFC 1035 where RFC 883 is
//! silent or was changed (listed below). RFC 883 is the predecessor of RFC
//! 1035 and has the same message layout; it was obsoleted by RFC 1034 and
//! RFC 1035.
//!
//! **Same in substance.** The two texts describe the same wire format by
//! the same author, one revised from the other, so this is a transcription
//! from a second text of the same family, not from a second body (as
//! `clazel-ipc`'s RFC 7049 transcription was for RFC 8949). What it checks
//! is that [`super::spec`] and this file, written in different forms,
//! compute the same function; a misreading shared by both RFCs, or by the
//! two transcriptions (the same agent wrote both), would not show here.
//! That is why the conformance tests (`tests/conformance_dns.rs`), which
//! use another implementation, carry the weight.
//!
//! The definitions below (up to "Equal to the spec") were written from the
//! RFC 883 text before `spec.rs` was read again; only the lemmas that
//! compare the two refer to it.
//!
//! ## What RFC 883 says differently, and what is done about it
//!
//! - **TTL.** RFC 883 §4 "Resource record format": "TTL - a 16 bit unsigned
//!   integer". RFC 1035 §3.2.1 widened it to 32 bits. This transcription
//!   reads 32 bits: the 16-bit field would put every later octet of a
//!   record in a different place from every message on the wire.
//! - **Z.** RFC 883's header diagram shows three unnamed bits between RA
//!   and RCODE and says nothing of them (its preface says the position
//!   "of the single bit fields" is "subject to change"). RFC 1035 §4.1.1
//!   names them Z, "must be zero". This transcription rejects a message with
//!   any of them set, as `spec.rs` does; RFC 883 alone would not decide it.
//! - **Reserved label types.** RFC 883: "The 01 and 10 values of the high
//!   order bits are reserved for future use and should not be used." A
//!   decoder cannot read past one, so it is an error here, as in RFC 1035
//!   §4.1.4.
//! - **TC, OPCODE, RCODE.** RFC 883 gives fewer values (OPCODE 4 to 15 and
//!   RCODE 6 to 15 "reserved"); a decoder keeps every value it is sent.
//! - **AAAA.** RFC 883 predates IPv6: type 28 is from RFC 3596 §2.1, which
//!   the first transcription also cites.
//! - **"A previously specified label string".** RFC 883: "the sequence of
//!   octets that defines a domain name may be terminated by a pointer to
//!   the length octet of a previously specified label string. The label
//!   string that the pointer specifies is appended to the already
//!   specified label string ... Multiple levels are allowed." Like RFC
//!   1035's "prior occurance", this does not say that the string must end
//!   before the pointer. This transcription reads "previously specified" as
//!   a name found in the part of the message before the pointer, so it
//!   resolves a pointer at offset `p` in the message cut off at `p` (the
//!   evident intent, `ERRATA.md`).
//!
//! ## How it differs in form from `spec.rs`
//!
//! - 16- and 32-bit fields are read with shifts and `|`; the flag fields of
//!   the header are tested with shifts and masks, not division and
//!   remainder.
//! - A name is read by recursion on the *rest of the message* that
//!   returns its octets (the label, then the rest), not by a loop that
//!   carries an accumulator; the 255-octet limit is checked on the whole
//!   name once it is read.
//! - A pointer is followed in the message **cut off at the pointer**
//!   (`m.take(pos)`), and a name in RDATA is read in the message **cut off at
//!   the end of the RDATA**, where `spec.rs` passes a `limit`.
//! - Questions and records are read by recursion that prepends, where
//!   `spec.rs` appends to an accumulator.
//! - The AAAA number is accumulated from the first octet ([`ind_fold`]),
//!   where `spec.rs` reads it from the last.
//!
//! Proven equal to [`super::spec::decode_message`] on every message
//! ([`lemma_equals_decode_message`]).

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------
// Fields.
// ---------------------------------------------------------------------------

/// The 16-bit field at octet `p` of `m`, most significant octet first.
pub open spec fn ind_u16(m: Seq<u8>, p: nat) -> u16 {
    ((m[p as int] as u16) << 8) | (m[p as int + 1] as u16)
}

/// The 32-bit field at octet `p` of `m`.
pub open spec fn ind_u32(m: Seq<u8>, p: nat) -> u32 {
    ((ind_u16(m, p) as u32) << 16) | (ind_u16(m, p + 2) as u32)
}

/// The number that the octets of `s` spell, accumulated from the first
/// octet.
pub open spec fn ind_fold(s: Seq<u8>, acc: nat) -> nat
    decreases s.len(),
{
    if s.len() == 0 {
        acc
    } else {
        ind_fold(s.drop_first(), acc * 256 + s[0] as nat)
    }
}

/// RFC 883 §4 "Header section format", with RFC 1035 §4.1.1 for Z.
pub open spec fn ind_header(m: Seq<u8>) -> Option<Header> {
    if m.len() < 12 {
        None
    } else {
        let flags = ind_u16(m, 2);
        if (flags >> 4) & 7 != 0 {
            None
        } else {
            Some(Header {
                id: ind_u16(m, 0),
                qr: (flags >> 15) & 1 == 1,
                opcode: ((flags >> 11) & 15) as u8,
                aa: (flags >> 10) & 1 == 1,
                tc: (flags >> 9) & 1 == 1,
                rd: (flags >> 8) & 1 == 1,
                ra: (flags >> 7) & 1 == 1,
                z: ((flags >> 4) & 7) as u8,
                rcode: (flags & 15) as u8,
                qdcount: ind_u16(m, 4),
                ancount: ind_u16(m, 6),
                nscount: ind_u16(m, 8),
                arcount: ind_u16(m, 10),
            })
        }
    }
}

// ---------------------------------------------------------------------------
// Domain names.
// ---------------------------------------------------------------------------

/// RFC 883 §4 "Domain name representation and compression": the domain name
/// at octet `pos` of the message `m`, as its octets expanded (each label
/// after its length octet, then the zero octet) and the offset after the
/// name in `m`. A label is "a one octet length field followed by that
/// number of octets"; a name ends with "a length byte of zero", or with "a
/// pointer": "two octet field in which the high order 2 bits are ones, and
/// the low order 14 bits specify an offset from the start of the message",
/// to "a previously specified label string". The 255-octet limit is not
/// applied here, see [`ind_name_limited`].
pub open spec fn ind_name(m: Seq<u8>, pos: nat) -> Option<(Seq<u8>, nat)>
    decreases m.len(), m.len() - pos,
{
    if pos >= m.len() {
        None
    } else {
        let l = m[pos as int];
        if l == 0 {
            // "a length byte of zero".
            Some((seq![0u8], pos + 1))
        } else if (l >> 6) == 0 {
            // "the high order two bits of the length field must be zero":
            // a label of 1 to 63 octets.
            if pos + 1 + l as nat > m.len() {
                None
            } else {
                match ind_name(m, pos + 1 + l as nat) {
                    None => None,
                    Some((rest, e)) => Some((m.subrange(pos as int, pos as int + 1 + l as int) + rest, e)),
                }
            }
        } else if (l >> 6) == 3 {
            // A pointer: two octets, the low 14 bits an offset.
            if pos + 2 > m.len() {
                None
            } else {
                let offset = ((((l & 63) as u16) << 8) | (m[pos as int + 1] as u16)) as nat;
                if offset >= pos {
                    // Not "previously specified".
                    None
                } else {
                    // The string is found in the part of the message before
                    // the pointer, and the name ends after the pointer.
                    match ind_name(m.take(pos as int), offset) {
                        None => None,
                        Some((w, _)) => Some((w, pos + 2)),
                    }
                }
            }
        } else {
            // 01 and 10: "reserved for future use".
            None
        }
    }
}

/// A domain name of at most 255 octets: "the total length of label octets
/// and label length octets that make up a domain name is restricted to 255
/// octets or less".
pub open spec fn ind_name_limited(m: Seq<u8>, pos: nat) -> Option<(Seq<u8>, nat)> {
    match ind_name(m, pos) {
        Some((w, e)) => if w.len() <= 255 {
            Some((w, e))
        } else {
            None
        },
        None => None,
    }
}

// ---------------------------------------------------------------------------
// Question and resource records.
// ---------------------------------------------------------------------------

/// "Question section format": QNAME, "QTYPE - a two octet code" and "QCLASS
/// - a two octet code".
pub open spec fn ind_question(m: Seq<u8>, pos: nat) -> Option<(Question, nat)> {
    match ind_name_limited(m, pos) {
        None => None,
        Some((name, p)) => if p + 4 <= m.len() {
            Some((Question { name, qtype: ind_u16(m, p), qclass: ind_u16(m, p + 2) }, p + 4))
        } else {
            None
        },
    }
}

/// The RDATA of a record of TYPE `t` and CLASS `c` between octets `start`
/// and `end` of `m`: "if the TYPE is A and the CLASS is IN, the RDATA field
/// is a 4 octet ARPA Internet address"; CNAME's is a "compressed domain
/// name"; every other is kept as octets.
pub open spec fn ind_rdata(m: Seq<u8>, t: u16, c: u16, start: nat, end: nat) -> Option<Rdata> {
    if c == 1 && t == 1 {
        if end - start == 4 {
            Some(Rdata::A(ind_u32(m, start)))
        } else {
            None
        }
    } else if c == 1 && t == 28 {
        if end - start == 16 {
            Some(Rdata::Aaaa(ind_fold(m.subrange(start as int, end as int), 0) as u128))
        } else {
            None
        }
    } else if c == 1 && t == 5 {
        // "the length of the compressed name is used in the length
        // calculation": the name is read in the message cut off at the end
        // of the RDATA, and must reach it exactly.
        match ind_name_limited(m.take(end as int), start) {
            Some((n, e)) => if e == end {
                Some(Rdata::Cname(n))
            } else {
                None
            },
            None => None,
        }
    } else {
        Some(Rdata::Opaque(m.subrange(start as int, end as int)))
    }
}

/// "Resource record format": NAME, TYPE, CLASS, TTL, RDLENGTH, RDATA (the
/// TTL is 32 bits, see above).
pub open spec fn ind_rr(m: Seq<u8>, pos: nat) -> Option<(Rr, nat)> {
    match ind_name_limited(m, pos) {
        None => None,
        Some((name, p)) => if p + 10 > m.len() {
            None
        } else {
            let start = p + 10;
            let end = start + ind_u16(m, p + 8) as nat;
            if end > m.len() {
                None
            } else {
                match ind_rdata(m, ind_u16(m, p), ind_u16(m, p + 2), start, end) {
                    None => None,
                    Some(rdata) => Some((Rr { name, rtype: ind_u16(m, p), rclass: ind_u16(m, p + 2), ttl: ind_u32(m, p + 4), rdata }, end)),
                }
            }
        },
    }
}

/// `n` questions from `pos`: the first, then the rest.
pub open spec fn ind_questions(m: Seq<u8>, pos: nat, n: nat) -> Option<(Seq<Question>, nat)>
    decreases n,
{
    if n == 0 {
        Some((seq![], pos))
    } else {
        match ind_question(m, pos) {
            None => None,
            Some((q, e)) => match ind_questions(m, e, (n - 1) as nat) {
                None => None,
                Some((rest, end)) => Some((seq![q] + rest, end)),
            },
        }
    }
}

/// `n` resource records from `pos`: the first, then the rest.
pub open spec fn ind_rrs(m: Seq<u8>, pos: nat, n: nat) -> Option<(Seq<Rr>, nat)>
    decreases n,
{
    if n == 0 {
        Some((seq![], pos))
    } else {
        match ind_rr(m, pos) {
            None => None,
            Some((r, e)) => match ind_rrs(m, e, (n - 1) as nat) {
                None => None,
                Some((rest, end)) => Some((seq![r] + rest, end)),
            },
        }
    }
}

/// A whole message: header, question section, then the answer, authority
/// and additional sections of the counts the header gives, ending with the
/// last record.
pub open spec fn ind_decode(m: Seq<u8>) -> Option<Message> {
    if m.len() > 65535 {
        None
    } else {
        match ind_header(m) {
            None => None,
            Some(h) => match ind_questions(m, 12, h.qdcount as nat) {
                None => None,
                Some((qs, p1)) => match ind_rrs(m, p1, h.ancount as nat) {
                    None => None,
                    Some((an, p2)) => match ind_rrs(m, p2, h.nscount as nat) {
                        None => None,
                        Some((ns, p3)) => match ind_rrs(m, p3, h.arcount as nat) {
                            None => None,
                            Some((ar, p4)) => if p4 == m.len() {
                                Some(Message { header: h, questions: qs, answers: an, authority: ns, additional: ar })
                            } else {
                                None
                            },
                        },
                    },
                },
            },
        }
    }
}

// ---------------------------------------------------------------------------
// Equal to the spec.
// ---------------------------------------------------------------------------

/// Shifts and `|` read the number that the division and remainder of the
/// spec do.
pub proof fn lemma_u16_eq(m: Seq<u8>, p: nat)
    requires
        p + 2 <= m.len(),
    ensures
        ind_u16(m, p) as nat == u16_at(m, p),
{
    let x = m[p as int];
    let y = m[p as int + 1];
    assert((((x as u16) << 8) | (y as u16)) == ((x as u16) * 256 + (y as u16)) as u16) by (bit_vector);
    assert((x as u16) * 256 + (y as u16) <= 65535) by (nonlinear_arith)
        requires
            x <= 255,
            y <= 255,
    ;
}

/// The same for 32-bit fields.
pub proof fn lemma_u32_eq(m: Seq<u8>, p: nat)
    requires
        p + 4 <= m.len(),
    ensures
        ind_u32(m, p) as nat == u32_at(m, p),
{
    lemma_u16_eq(m, p);
    lemma_u16_eq(m, p + 2);
    let hi = ind_u16(m, p);
    let lo = ind_u16(m, p + 2);
    assert((((hi as u32) << 16) | (lo as u32)) == ((hi as u32) * 65536 + (lo as u32)) as u32) by (bit_vector);
    assert((hi as u32) * 65536 + (lo as u32) <= 0xFFFF_FFFF) by (nonlinear_arith)
        requires
            hi <= 65535,
            lo <= 65535,
    ;
}

/// The flag fields by shifts and masks are the spec's by division and
/// remainder.
pub proof fn lemma_flags_eq(w: u16)
    ensures
        ((w >> 15) & 1) as nat == (w as nat / 32768) % 2,
        ((w >> 11) & 15) as nat == (w as nat / 2048) % 16,
        ((w >> 10) & 1) as nat == (w as nat / 1024) % 2,
        ((w >> 9) & 1) as nat == (w as nat / 512) % 2,
        ((w >> 8) & 1) as nat == (w as nat / 256) % 2,
        ((w >> 7) & 1) as nat == (w as nat / 128) % 2,
        ((w >> 4) & 7) as nat == (w as nat / 16) % 8,
        (w & 15) as nat == w as nat % 16,
{
    assert(((w >> 15) & 1) == (w / 32768) % 2) by (bit_vector);
    assert(((w >> 11) & 15) == (w / 2048) % 16) by (bit_vector);
    assert(((w >> 10) & 1) == (w / 1024) % 2) by (bit_vector);
    assert(((w >> 9) & 1) == (w / 512) % 2) by (bit_vector);
    assert(((w >> 8) & 1) == (w / 256) % 2) by (bit_vector);
    assert(((w >> 7) & 1) == (w / 128) % 2) by (bit_vector);
    assert(((w >> 4) & 7) == (w / 16) % 8) by (bit_vector);
    assert((w & 15) == w % 16) by (bit_vector);
}

/// The two header readers agree.
pub proof fn lemma_header_eq(m: Seq<u8>)
    ensures
        ind_header(m) == decode_header(m),
{
    if m.len() >= 12 {
        lemma_u16_eq(m, 0);
        lemma_u16_eq(m, 2);
        lemma_u16_eq(m, 4);
        lemma_u16_eq(m, 6);
        lemma_u16_eq(m, 8);
        lemma_u16_eq(m, 10);
        lemma_flags_eq(ind_u16(m, 2));
    }
}

/// An independent name is never empty: it ends with the zero octet.
pub proof fn lemma_ind_name_nonempty(m: Seq<u8>, pos: nat)
    ensures
        match ind_name(m, pos) {
            Some((w, e)) => w.len() >= 1,
            None => true,
        },
    decreases m.len(), m.len() - pos,
{
    if pos < m.len() {
        let l = m[pos as int];
        if l == 0 {
        } else if (l >> 6) == 0 {
            if pos + 1 + l as nat <= m.len() {
                lemma_ind_name_nonempty(m, pos + 1 + l as nat);
            }
        } else if (l >> 6) == 3 {
            if pos + 2 <= m.len() {
                let offset = ((((l & 63) as u16) << 8) | (m[pos as int + 1] as u16)) as nat;
                if offset < pos {
                    lemma_ind_name_nonempty(m.take(pos as int), offset);
                }
            }
        }
    }
}

/// The length octet's two high bits are the spec's ranges.
pub proof fn lemma_length_octet_eq(l: u8)
    ensures
        (l >> 6) == 0 <==> l < 64,
        (l >> 6) == 3 <==> l >= 192,
        (l >> 6) <= 3,
        (l & 63) as nat == l as nat % 64,
        l >= 192 ==> ((l & 63) as nat) == l as nat - 192,
{
    assert(((l >> 6) == 0) == (l < 64)) by (bit_vector);
    assert(((l >> 6) == 3) == (l >= 192)) by (bit_vector);
    assert((l >> 6) <= 3) by (bit_vector);
    assert((l & 63) == l % 64) by (bit_vector);
    assert(l >= 192 ==> (l & 63) == l - 192) by (bit_vector);
}

/// The pointer's offset, by shifts, is the spec's.
pub proof fn lemma_offset_eq(l: u8, x: u8)
    requires
        l >= 192,
    ensures
        ((((l & 63) as u16) << 8) | (x as u16)) as nat == (l as nat - 192) * 256 + x as nat,
{
    lemma_length_octet_eq(l);
    let hi = (l & 63) as u16;
    assert(((l & 63) as u16) <= 63) by (bit_vector);
    assert(((hi << 8) | (x as u16)) == (hi * 256 + (x as u16)) as u16) by (bit_vector)
        requires
            hi <= 63,
    ;
    assert(((l & 63) as u16) <= 63) by (bit_vector);
    assert(hi * 256 + (x as u16) <= 65535) by (nonlinear_arith)
        requires
            hi <= 63,
            x <= 255,
    ;
}

/// The loop of the spec and the recursion here read the same name: for any
/// accumulated start `acc` of at most 254 octets and `limit` within the
/// message, `read_name` is `ind_name` in the message cut off at `limit`,
/// with the accumulator put in front and the 255-octet limit checked on
/// the whole.
pub proof fn lemma_name_eq(b: Seq<u8>, pos: nat, limit: nat, acc: Seq<u8>, end: Option<nat>)
    requires
        limit <= b.len(),
        acc.len() <= 254,
    ensures
        read_name(b, pos, limit, acc, end) == match ind_name(b.take(limit as int), pos) {
            Some((w, e)) => if acc.len() + w.len() <= 255 {
                Some((acc + w, match end {
                    Some(x) => x,
                    None => e,
                }))
            } else {
                None
            },
            None => None,
        },
    decreases limit, limit - pos,
{
    let m = b.take(limit as int);
    assert(m.len() == limit);
    if pos >= limit {
    } else {
        let l = b[pos as int];
        assert(m[pos as int] == l);
        lemma_length_octet_eq(l);
        if l == 0 {
            assert(acc + seq![0u8] =~= acc.push(0));
        } else if l < 64 {
            if pos + 1 + l as nat <= limit {
                let piece = b.subrange(pos as int, pos as int + 1 + l as int);
                assert(m.subrange(pos as int, pos as int + 1 + l as int) =~= piece);
                lemma_ind_name_nonempty(m, pos + 1 + l as nat);
                if acc.len() + 1 + l as nat <= 254 {
                    lemma_name_eq(b, pos + 1 + l as nat, limit, acc + piece, end);
                    if let Some((rest, e)) = ind_name(m, pos + 1 + l as nat) {
                        assert(acc + piece + rest =~= acc + (piece + rest));
                    }
                } else {
                    // The spec stops at this label; so does the total.
                    if let Some((rest, e)) = ind_name(m, pos + 1 + l as nat) {
                        assert(acc.len() + (piece + rest).len() > 255);
                    }
                }
            }
        } else if l >= 192 {
            if pos + 2 <= limit {
                lemma_offset_eq(l, b[pos as int + 1]);
                let target: nat = ((l as nat - 192) * 256 + b[pos as int + 1] as nat) as nat;
                assert(m[pos as int + 1] == b[pos as int + 1]);
                if target < pos {
                    let end2 = Some(match end {
                        Some(e) => e,
                        None => pos + 2,
                    });
                    lemma_name_eq(b, target, pos, acc, end2);
                    assert(m.take(pos as int) =~= b.take(pos as int));
                }
            }
        }
    }
}

/// A name in the whole message: the same under both readers.
pub proof fn lemma_decode_name_eq(b: Seq<u8>, pos: nat)
    ensures
        decode_name(b, pos) == ind_name_limited(b, pos),
{
    lemma_name_eq(b, pos, b.len(), seq![], None);
    assert(b.take(b.len() as int) =~= b);
    if let Some((w, e)) = ind_name(b, pos) {
        assert(seq![] + w =~= w);
    }
}

/// A question under both readers.
pub proof fn lemma_question_eq(b: Seq<u8>, pos: nat)
    ensures
        read_question(b, pos) == ind_question(b, pos),
{
    lemma_decode_name_eq(b, pos);
    lemma_read_name_progress(b, pos);
    if let Some((name, p)) = decode_name(b, pos) {
        if p + 4 <= b.len() {
            lemma_u16_eq(b, p);
            lemma_u16_eq(b, p + 2);
        }
    }
}

/// A name read ends within the message (when it ends at all).
pub proof fn lemma_read_name_progress(b: Seq<u8>, pos: nat)
    ensures
        match decode_name(b, pos) {
            Some((w, e)) => e <= b.len(),
            None => true,
        },
{
    super::lemmas::lemma_read_name_end(b, pos, b.len(), seq![], None);
}

/// A resource record's RDATA under both readers.
pub proof fn lemma_rdata_eq(b: Seq<u8>, t: u16, c: u16, start: nat, end: nat)
    requires
        start <= end <= b.len(),
    ensures
        decode_rdata(b, t, c, start, end) == ind_rdata(b, t, c, start, end),
{
    if c == 1 && t == 1 {
        if end - start == 4 {
            lemma_u32_eq(b, start);
        }
    } else if c == 1 && t == 28 {
        if end - start == 16 {
            lemma_fold_eq(b.subrange(start as int, end as int), 0);
        }
    } else if c == 1 && t == 5 {
        lemma_name_eq(b, start, end, seq![], None);
        if let Some((w, e)) = ind_name(b.take(end as int), start) {
            assert(seq![] + w =~= w);
        }
    }
}

/// Reading the number from the first octet or from the last is the same.
pub proof fn lemma_fold_eq(s: Seq<u8>, acc: nat)
    ensures
        ind_fold(s, acc) == acc * super::lemmas::pow256(s.len()) + be_value(s),
    decreases s.len(),
{
    if s.len() > 0 {
        let rest = s.drop_first();
        let s0 = s[0] as nat;
        lemma_fold_eq(rest, acc * 256 + s0);
        lemma_be_value_cons(s);
        assert(rest.len() == s.len() - 1);
        let pn1 = super::lemmas::pow256(rest.len());
        let pn = super::lemmas::pow256(s.len());
        assert(pn == 256 * pn1);
        assert((acc * 256 + s0) * pn1 == acc * pn + s0 * pn1) by (nonlinear_arith)
            requires
                pn == 256 * pn1,
        ;
        assert(be_value(s) == s0 * pn1 + be_value(rest));
        assert(ind_fold(s, acc) == ind_fold(rest, acc * 256 + s0));
        assert(ind_fold(rest, acc * 256 + s0) == (acc * 256 + s0) * pn1 + be_value(rest));
        assert(ind_fold(s, acc) == acc * pn + be_value(s));
    } else {
        assert(s.len() == 0);
        assert(super::lemmas::pow256(0) == 1);
        assert(be_value(s) == 0);
        assert(ind_fold(s, acc) == acc);
    }
}

/// `be_value` of a sequence is its first octet times 256^(rest) plus the
/// value of the rest: the accumulation from the front.
pub proof fn lemma_be_value_cons(s: Seq<u8>)
    requires
        s.len() > 0,
    ensures
        be_value(s) == s[0] as nat * super::lemmas::pow256((s.len() - 1) as nat) + be_value(s.drop_first()),
    decreases s.len(),
{
    let rest = s.drop_first();
    if rest.len() == 0 {
        assert(s.drop_last() =~= Seq::<u8>::empty());
        assert(be_value(Seq::<u8>::empty()) == 0);
        assert(be_value(s) == s.last() as nat);
        assert(s.last() == s[0]);
        assert(s.len() == 1);
        assert(super::lemmas::pow256(0) == 1);
        assert(rest =~= Seq::<u8>::empty());
        assert((s.len() - 1) as nat == 0);
        assert(be_value(rest) == 0);
        assert(super::lemmas::pow256((s.len() - 1) as nat) == 1);
        assert(s[0] as nat * 1 == s[0] as nat);
    } else {
        let d = s.drop_last();
        lemma_be_value_cons(d);
        assert(d.drop_first() =~= rest.drop_last());
        assert(d[0] == s[0]);
        assert(rest.last() == s.last());
        let p = super::lemmas::pow256((s.len() - 2) as nat);
        assert(super::lemmas::pow256((s.len() - 1) as nat) == 256 * p);
        assert(d.len() - 1 == s.len() - 2);
        let d0 = s[0] as nat;
        assert(d0 * p * 256 == d0 * (256 * p)) by (nonlinear_arith);
        assert(be_value(s) == be_value(d) * 256 + s.last() as nat);
        assert(be_value(rest) == be_value(rest.drop_last()) * 256 + rest.last() as nat);
        assert(be_value(d) == d0 * p + be_value(rest.drop_last()));
        assert((d0 * p + be_value(rest.drop_last())) * 256 == d0 * p * 256 + be_value(rest.drop_last()) * 256) by (nonlinear_arith);
        assert(s[0] as nat * super::lemmas::pow256((s.len() - 1) as nat) == d0 * (256 * p));
        assert(be_value(s) == d0 * (256 * p) + be_value(rest));
    }
}

/// A resource record under both readers.
pub proof fn lemma_rr_eq(b: Seq<u8>, pos: nat)
    ensures
        read_rr(b, pos) == ind_rr(b, pos),
{
    lemma_decode_name_eq(b, pos);
    lemma_read_name_progress(b, pos);
    if let Some((name, p)) = decode_name(b, pos) {
        if p + 10 <= b.len() {
            lemma_u16_eq(b, p);
            lemma_u16_eq(b, p + 2);
            lemma_u16_eq(b, p + 8);
            lemma_u32_eq(b, p + 4);
            let rstart = p + 10;
            let rend = rstart + u16_at(b, p + 8);
            if rend <= b.len() {
                lemma_rdata_eq(b, u16_at(b, p) as u16, u16_at(b, p + 2) as u16, rstart, rend);
            }
        }
    }
}

/// `n` questions under both readers: the accumulated ones are put in front
/// of the ones read by recursion.
pub proof fn lemma_questions_eq(b: Seq<u8>, pos: nat, n: nat, acc: Seq<Question>)
    ensures
        read_questions(b, pos, n, acc) == match ind_questions(b, pos, n) {
            Some((qs, e)) => Some((acc + qs, e)),
            None => None,
        },
    decreases n,
{
    if n == 0 {
        assert(acc + Seq::<Question>::empty() =~= acc);
    } else {
        lemma_question_eq(b, pos);
        if let Some((q, e)) = read_question(b, pos) {
            lemma_questions_eq(b, e, (n - 1) as nat, acc.push(q));
            if let Some((rest, end)) = ind_questions(b, e, (n - 1) as nat) {
                assert(acc.push(q) + rest =~= acc + (seq![q] + rest));
            }
        }
    }
}

/// `n` records under both readers.
pub proof fn lemma_rrs_eq(b: Seq<u8>, pos: nat, n: nat, acc: Seq<Rr>)
    ensures
        read_rrs(b, pos, n, acc) == match ind_rrs(b, pos, n) {
            Some((rs, e)) => Some((acc + rs, e)),
            None => None,
        },
    decreases n,
{
    if n == 0 {
        assert(acc + Seq::<Rr>::empty() =~= acc);
    } else {
        lemma_rr_eq(b, pos);
        if let Some((r, e)) = read_rr(b, pos) {
            lemma_rrs_eq(b, e, (n - 1) as nat, acc.push(r));
            if let Some((rest, end)) = ind_rrs(b, e, (n - 1) as nat) {
                assert(acc.push(r) + rest =~= acc + (seq![r] + rest));
            }
        }
    }
}

/// The independent decoder equals the spec's on every message: the same
/// messages are valid, and each decodes to the same record. (Differences
/// between RFC 883 and RFC 1035, which this file resolves in favour of RFC
/// 1035, are listed at the top.)
pub proof fn lemma_equals_decode_message(b: Seq<u8>)
    ensures
        ind_decode(b) == decode_message(b),
{
    lemma_header_eq(b);
    if b.len() <= MAX_TCP {
        if let Some(h) = decode_header(b) {
            lemma_questions_eq(b, 12, h.qdcount as nat, seq![]);
            if let Some((qs, p1)) = ind_questions(b, 12, h.qdcount as nat) {
                assert(Seq::<Question>::empty() + qs =~= qs);
                lemma_rrs_eq(b, p1, h.ancount as nat, seq![]);
                if let Some((an, p2)) = ind_rrs(b, p1, h.ancount as nat) {
                    assert(Seq::<Rr>::empty() + an =~= an);
                    lemma_rrs_eq(b, p2, h.nscount as nat, seq![]);
                    if let Some((ns, p3)) = ind_rrs(b, p2, h.nscount as nat) {
                        assert(Seq::<Rr>::empty() + ns =~= ns);
                        lemma_rrs_eq(b, p3, h.arcount as nat, seq![]);
                        if let Some((ar, p4)) = ind_rrs(b, p3, h.arcount as nat) {
                            assert(Seq::<Rr>::empty() + ar =~= ar);
                        }
                    }
                }
            }
        }
    }
}

/// The same for a datagram.
pub proof fn lemma_equals_decode_udp(b: Seq<u8>)
    ensures
        (if b.len() > MAX_UDP {
            None
        } else {
            ind_decode(b)
        }) == decode_udp(b),
{
    lemma_equals_decode_message(b);
}

} // verus!
