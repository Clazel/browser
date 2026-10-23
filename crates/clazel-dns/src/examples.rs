//! The standard's examples, and the rejections the spec's rules demand,
//! evaluated on the spec: RFC 1035 §4.1.4's compression example (F.ISI.ARPA,
//! FOO.F.ISI.ARPA, ARPA and the root), a header with every field different,
//! the pointer errors, the size limits, a query, and replies for the answer
//! rules.
//!
//! This is a module of its own because Verus evaluates every `by
//! (compute_only)` assertion of a module it verifies, even with
//! `--verify-function`. A mutant that breaks an example would otherwise
//! fail every kill certificate placed next to it, not only the one about
//! the example. The lemmas here are theorems about the spec like any other,
//! so kill certificates (`mutations.json`) may name them.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// `n` octets of `v`.
pub open spec fn fill(v: u8, n: nat) -> Seq<u8>
    decreases n,
{
    if n == 0 {
        seq![]
    } else {
        fill(v, (n - 1) as nat).push(v)
    }
}

// ---------------------------------------------------------------------------
// RFC 1035 §4.1.4: the compression example.
// ---------------------------------------------------------------------------

/// The message of §4.1.4's figure, ignoring "the other fields of the
/// message": the names F.ISI.ARPA at offset 20, FOO.F.ISI.ARPA at 40 (FOO,
/// then a pointer to 20), ARPA at 64 (a pointer to 26) and the root at 92.
/// Every other octet is zero.
pub open spec fn rfc_figure() -> Seq<u8> {
    fill(0, 20) + seq![1u8, 70, 3, 73, 83, 73, 4, 65, 82, 80, 65, 0] + fill(0, 8) + seq![3u8, 70, 79, 79, 0xC0, 20] + fill(0, 18)
        + seq![0xC0u8, 26] + fill(0, 26) + seq![0u8]
}

/// §4.1.4: "The domain name for F.ISI.ARPA is shown at offset 20. The domain
/// name FOO.F.ISI.ARPA is shown at offset 40; this definition uses a
/// pointer to concatenate a label for FOO to the previously defined
/// F.ISI.ARPA. The domain name ARPA is defined at offset 64 using a pointer
/// to the ARPA component of the name F.ISI.ARPA at 20; note that this
/// pointer relies on ARPA being the last label in the string at 20. The
/// root domain name is defined by a single zero octet at 92." Each name is
/// read back in full, and the offset after it is where the name ended in
/// the message.
pub proof fn lemma_rfc_1035_4_1_4_example()
    ensures
        rfc_figure().len() == 93,
        decode_name(rfc_figure(), 20) == Some((seq![1u8, 70, 3, 73, 83, 73, 4, 65, 82, 80, 65, 0], 32nat)),
        decode_name(rfc_figure(), 40) == Some((seq![3u8, 70, 79, 79, 1, 70, 3, 73, 83, 73, 4, 65, 82, 80, 65, 0], 46nat)),
        decode_name(rfc_figure(), 64) == Some((seq![4u8, 65, 82, 80, 65, 0], 66nat)),
        decode_name(rfc_figure(), 92) == Some((seq![0u8], 93nat)),
{
    assert(rfc_figure().len() == 93) by (compute_only);
    assert(decode_name(rfc_figure(), 20) == Some((seq![1u8, 70, 3, 73, 83, 73, 4, 65, 82, 80, 65, 0], 32nat))) by (compute_only);
    assert(decode_name(rfc_figure(), 40) == Some((seq![3u8, 70, 79, 79, 1, 70, 3, 73, 83, 73, 4, 65, 82, 80, 65, 0], 46nat))) by (compute_only);
    assert(decode_name(rfc_figure(), 64) == Some((seq![4u8, 65, 82, 80, 65, 0], 66nat))) by (compute_only);
    assert(decode_name(rfc_figure(), 92) == Some((seq![0u8], 93nat))) by (compute_only);
}

// ---------------------------------------------------------------------------
// §4.1.4: pointers that are errors.
// ---------------------------------------------------------------------------

/// A pointer to itself, and a pointer forward, are errors: neither is "a
/// prior occurance".
pub proof fn lemma_pointer_not_prior()
    ensures
        decode_name(seq![0xC0u8, 0], 0) is None,
        decode_name(seq![0xC0u8, 2, 0], 0) is None,
        decode_name(seq![0x00u8, 0xC0, 3, 0], 1) is None,
{
    assert(decode_name(seq![0xC0u8, 0], 0) is None) by (compute_only);
    assert(decode_name(seq![0xC0u8, 2, 0], 0) is None) by (compute_only);
    assert(decode_name(seq![0x00u8, 0xC0, 3, 0], 1) is None) by (compute_only);
}

/// A pointer to a lower offset is not enough: a label at offset 0 and a
/// pointer at offset 2 back to 0 would be read forever. The name read from
/// the pointer's target must end before the pointer, so it is an error.
pub proof fn lemma_pointer_loop_rejected()
    ensures
        decode_name(seq![1u8, 97, 0xC0, 0], 2) is None,
        decode_name(seq![1u8, 97, 0xC0, 0], 0) is None,
        // Two pointers that point at each other's predecessor.
        decode_name(seq![0xC0u8, 2, 0xC0, 0], 2) is None,
{
    assert(decode_name(seq![1u8, 97, 0xC0, 0], 2) is None) by (compute_only);
    assert(decode_name(seq![1u8, 97, 0xC0, 0], 0) is None) by (compute_only);
    assert(decode_name(seq![0xC0u8, 2, 0xC0, 0], 2) is None) by (compute_only);
}

/// A pointer whose target name would run over the pointer itself is an
/// error, though it is at a lower offset: the label at offset 0 covers the
/// octets of the pointer at offset 2.
pub proof fn lemma_pointer_overlap_rejected()
    ensures
        decode_name(seq![4u8, 0x41, 0xC0, 0x00, 0x42, 0], 2) is None,
{
    assert(decode_name(seq![4u8, 0x41, 0xC0, 0x00, 0x42, 0], 2) is None) by (compute_only);
}

/// A pointer to an earlier name that itself ends in a pointer is followed
/// to the end (a name at 0, a pointer at 3 to it, a pointer at 5 to that
/// one), and the name ends after the first pointer.
pub proof fn lemma_pointer_chain()
    ensures
        decode_name(seq![1u8, 97, 0, 0xC0, 0, 0xC0, 3], 5) == Some((seq![1u8, 97, 0], 7nat)),
        decode_name(seq![1u8, 97, 0, 2, 98, 99, 0xC0, 0], 3) == Some((seq![2u8, 98, 99, 1, 97, 0], 8nat)),
{
    assert(decode_name(seq![1u8, 97, 0, 0xC0, 0, 0xC0, 3], 5) == Some((seq![1u8, 97, 0], 7nat))) by (compute_only);
    assert(decode_name(seq![1u8, 97, 0, 2, 98, 99, 0xC0, 0], 3) == Some((seq![2u8, 98, 99, 1, 97, 0], 8nat))) by (compute_only);
}

/// §4.1.4: "(The 10 and 01 combinations are reserved for future use.)", a
/// pointer cut short, and a label cut short are errors.
pub proof fn lemma_name_errors()
    ensures
        decode_name(seq![0x40u8, 0], 0) is None,
        decode_name(seq![0x80u8, 0], 0) is None,
        decode_name(seq![0xC0u8], 0) is None,
        decode_name(seq![3u8, 97, 98], 0) is None,
        decode_name(seq![1u8, 97], 0) is None,
        decode_name(seq![0u8], 1) is None,
{
    assert(decode_name(seq![0x40u8, 0], 0) is None) by (compute_only);
    assert(decode_name(seq![0x80u8, 0], 0) is None) by (compute_only);
    assert(decode_name(seq![0xC0u8], 0) is None) by (compute_only);
    assert(decode_name(seq![3u8, 97, 98], 0) is None) by (compute_only);
    assert(decode_name(seq![1u8, 97], 0) is None) by (compute_only);
    assert(decode_name(seq![0u8], 1) is None) by (compute_only);
}

// ---------------------------------------------------------------------------
// §2.3.4: size limits.
// ---------------------------------------------------------------------------

/// A label of 63 octets is the longest: the length octet 64 begins with the
/// bits 01, which are reserved.
pub proof fn lemma_label_limit()
    ensures
        decode_name(seq![63u8] + fill(97, 63) + seq![0u8], 0) == Some((seq![63u8] + fill(97, 63) + seq![0u8], 65nat)),
        decode_name(seq![64u8] + fill(97, 64) + seq![0u8], 0) is None,
{
    assert(decode_name(seq![63u8] + fill(97, 63) + seq![0u8], 0) == Some((seq![63u8] + fill(97, 63) + seq![0u8], 65nat)))
        by (compute_only);
    assert(decode_name(seq![64u8] + fill(97, 64) + seq![0u8], 0) is None) by (compute_only);
}

/// A name of 255 octets is the longest: three labels of 63 octets, one of
/// 61, and the zero octet make 255; one more octet in the last label makes
/// 256.
pub proof fn lemma_name_limit()
    ensures
        decode_name(max_name(61), 0) == Some((max_name(61), 255nat)),
        decode_name(max_name(62), 0) is None,
{
    assert(decode_name(max_name(61), 0) == Some((max_name(61), 255nat))) by (compute_only);
    assert(decode_name(max_name(62), 0) is None) by (compute_only);
}

/// Three labels of 63 octets, then one of `n`, and the zero octet.
pub open spec fn max_name(n: nat) -> Seq<u8> {
    seq![63u8] + fill(97, 63) + seq![63u8] + fill(97, 63) + seq![63u8] + fill(97, 63) + seq![n as u8] + fill(97, n) + seq![0u8]
}

/// The same limits for the names of queries, which are dotted: a label of
/// 63 octets and a name of 255 are accepted, and 64 and 256 are not.
pub proof fn lemma_dotted_limits()
    ensures
        dotted_to_wire(fill(97, 63)) == Some(seq![63u8] + fill(97, 63) + seq![0u8]),
        dotted_to_wire(fill(97, 64)) is None,
        dotted_to_wire(dotted_name(61)) == Some(max_name(61)),
        dotted_to_wire(dotted_name(62)) is None,
{
    assert(dotted_to_wire(fill(97, 63)) == Some(seq![63u8] + fill(97, 63) + seq![0u8])) by (compute_only);
    assert(dotted_to_wire(fill(97, 64)) is None) by (compute_only);
    assert(dotted_to_wire(dotted_name(61)) == Some(max_name(61))) by (compute_only);
    assert(dotted_to_wire(dotted_name(62)) is None) by (compute_only);
}

/// Three labels of 63 octets and one of `n`, separated by dots.
pub open spec fn dotted_name(n: nat) -> Seq<u8> {
    fill(97, 63) + seq![46u8] + fill(97, 63) + seq![46u8] + fill(97, 63) + seq![46u8] + fill(97, n)
}

/// Dotted names: the root, a trailing dot, and what is not a name.
pub proof fn lemma_dotted_names()
    ensures
        dotted_to_wire(seq![46u8]) == Some(seq![0u8]),
        dotted_to_wire(seq![97u8]) == Some(seq![1u8, 97, 0]),
        dotted_to_wire(seq![97u8, 46]) == Some(seq![1u8, 97, 0]),
        dotted_to_wire(seq![97u8, 46, 98, 99]) == Some(seq![1u8, 97, 2, 98, 99, 0]),
        dotted_to_wire(seq![]) is None,
        dotted_to_wire(seq![97u8, 46, 46, 98]) is None,
        dotted_to_wire(seq![46u8, 97]) is None,
        dotted_to_wire(seq![46u8, 46]) is None,
        dotted_to_wire(seq![97u8, 128]) is None,
{
    assert(dotted_to_wire(seq![46u8]) == Some(seq![0u8])) by (compute_only);
    assert(dotted_to_wire(seq![97u8]) == Some(seq![1u8, 97, 0])) by (compute_only);
    assert(dotted_to_wire(seq![97u8, 46]) == Some(seq![1u8, 97, 0])) by (compute_only);
    assert(dotted_to_wire(seq![97u8, 46, 98, 99]) == Some(seq![1u8, 97, 2, 98, 99, 0])) by (compute_only);
    assert(dotted_to_wire(seq![]) is None) by (compute_only);
    assert(dotted_to_wire(seq![97u8, 46, 46, 98]) is None) by (compute_only);
    assert(dotted_to_wire(seq![46u8, 97]) is None) by (compute_only);
    assert(dotted_to_wire(seq![46u8, 46]) is None) by (compute_only);
    assert(dotted_to_wire(seq![97u8, 128]) is None) by (compute_only);
}

// ---------------------------------------------------------------------------
// §4.1.1: the header.
// ---------------------------------------------------------------------------

/// A header with every field different from its neighbours: ID 0x1234,
/// flags 0xAA8A (QR, OPCODE 5, TC, RA, RCODE 10) and the counts 3, 2, 1, 4.
pub proof fn lemma_header_fields()
    ensures
        decode_header(seq![0x12u8, 0x34, 0xAA, 0x8A, 0, 3, 0, 2, 0, 1, 0, 4]) == Some(
            Header {
                id: 0x1234,
                qr: true,
                opcode: 5,
                aa: false,
                tc: true,
                rd: false,
                ra: true,
                z: 0,
                rcode: 10,
                qdcount: 3,
                ancount: 2,
                nscount: 1,
                arcount: 4,
            },
        ),
{
    assert(decode_header(seq![0x12u8, 0x34, 0xAA, 0x8A, 0, 3, 0, 2, 0, 1, 0, 4]) == Some(
        Header {
            id: 0x1234,
            qr: true,
            opcode: 5,
            aa: false,
            tc: true,
            rd: false,
            ra: true,
            z: 0,
            rcode: 10,
            qdcount: 3,
            ancount: 2,
            nscount: 1,
            arcount: 4,
        },
    )) by (compute_only);
}

/// The other flag bits, one at a time: AA and RD (clear above), and the
/// header is too short, or has Z set (§4.1.1: "Must be zero in all queries
/// and responses").
pub proof fn lemma_header_other_bits()
    ensures
        decode_header(seq![0u8, 0, 0x05, 0x00, 0, 0, 0, 0, 0, 0, 0, 0]) == Some(
            Header {
                id: 0,
                qr: false,
                opcode: 0,
                aa: true,
                tc: false,
                rd: true,
                ra: false,
                z: 0,
                rcode: 0,
                qdcount: 0,
                ancount: 0,
                nscount: 0,
                arcount: 0,
            },
        ),
        decode_header(seq![0u8, 0, 0x00, 0x10, 0, 0, 0, 0, 0, 0, 0, 0]) is None,
        decode_header(seq![0u8, 0, 0x00, 0x20, 0, 0, 0, 0, 0, 0, 0, 0]) is None,
        decode_header(seq![0u8, 0, 0x00, 0x40, 0, 0, 0, 0, 0, 0, 0, 0]) is None,
        decode_header(seq![0u8, 0, 0x00, 0x00, 0, 0, 0, 0, 0, 0, 0]) is None,
{
    assert(decode_header(seq![0u8, 0, 0x05, 0x00, 0, 0, 0, 0, 0, 0, 0, 0]) == Some(
        Header {
            id: 0,
            qr: false,
            opcode: 0,
            aa: true,
            tc: false,
            rd: true,
            ra: false,
            z: 0,
            rcode: 0,
            qdcount: 0,
            ancount: 0,
            nscount: 0,
            arcount: 0,
        },
    )) by (compute_only);
    assert(decode_header(seq![0u8, 0, 0x00, 0x10, 0, 0, 0, 0, 0, 0, 0, 0]) is None) by (compute_only);
    assert(decode_header(seq![0u8, 0, 0x00, 0x20, 0, 0, 0, 0, 0, 0, 0, 0]) is None) by (compute_only);
    assert(decode_header(seq![0u8, 0, 0x00, 0x40, 0, 0, 0, 0, 0, 0, 0, 0]) is None) by (compute_only);
    assert(decode_header(seq![0u8, 0, 0x00, 0x00, 0, 0, 0, 0, 0, 0, 0]) is None) by (compute_only);
}

// ---------------------------------------------------------------------------
// §3.3.1, §3.4.1, RFC 3596, RFC 1034 §3.6.2 and RFC 5452: answers.
// ---------------------------------------------------------------------------

/// The name `a` in wire format.
pub open spec fn na() -> Seq<u8> {
    seq![1u8, 97, 0]
}

/// The name `b` in wire format.
pub open spec fn nb() -> Seq<u8> {
    seq![1u8, 98, 0]
}

/// The name `c` in wire format.
pub open spec fn nc() -> Seq<u8> {
    seq![1u8, 99, 0]
}

/// The name `A` (the same as `a` up to case).
pub open spec fn na_upper() -> Seq<u8> {
    seq![1u8, 65, 0]
}

/// An A record of class IN.
pub open spec fn a_rr(owner: Seq<u8>, address: u32) -> Rr {
    Rr { name: owner, rtype: 1, rclass: 1, ttl: 300, rdata: Rdata::A(address) }
}

/// An AAAA record of class IN.
pub open spec fn aaaa_rr(owner: Seq<u8>, address: u128) -> Rr {
    Rr { name: owner, rtype: 28, rclass: 1, ttl: 300, rdata: Rdata::Aaaa(address) }
}

/// A CNAME record of class IN.
pub open spec fn cname_rr(owner: Seq<u8>, target: Seq<u8>) -> Rr {
    Rr { name: owner, rtype: 5, rclass: 1, ttl: 300, rdata: Rdata::Cname(target) }
}

/// The header of a reply with ID 7, QR set, OPCODE 0, TC `tc`, RCODE
/// `rcode`, RD and RA set, and the given counts.
pub open spec fn reply_header(tc: bool, rcode: u8, qd: u16, an: u16, ns: u16, ar: u16) -> Header {
    Header {
        id: 7,
        qr: true,
        opcode: 0,
        aa: false,
        tc,
        rd: true,
        ra: true,
        z: 0,
        rcode,
        qdcount: qd,
        ancount: an,
        nscount: ns,
        arcount: ar,
    }
}

/// A reply with ID 7, QR set, OPCODE 0, TC `tc`, RCODE `rcode` and the
/// question `qname`, QTYPE `qtype`, class IN.
pub open spec fn reply(
    qname: Seq<u8>,
    qtype: u16,
    tc: bool,
    rcode: u8,
    answers: Seq<Rr>,
    authority: Seq<Rr>,
    additional: Seq<Rr>,
) -> Message {
    Message {
        header: reply_header(tc, rcode, 1, answers.len() as u16, authority.len() as u16, additional.len() as u16),
        questions: seq![Question { name: qname, qtype, qclass: 1 }],
        answers,
        authority,
        additional,
    }
}

/// The query "a", type A, ID 7.
pub open spec fn query_a() -> Query {
    Query { id: 7, name: seq![97u8], qtype: 1 }
}

/// The query "a", type AAAA, ID 7.
pub open spec fn query_aaaa() -> Query {
    Query { id: 7, name: seq![97u8], qtype: 28 }
}

/// A direct answer, and the reply's case: the owner `A` matches the query
/// `a` (§2.3.3), and the question `A` matches too (RFC 5452 §6).
pub proof fn lemma_answer_direct()
    ensures
        answer_addresses(query_a(), reply(na(), 1, false, 0, seq![a_rr(na(), 0x01020304), a_rr(na(), 0x05060708)], seq![], seq![]))
            == Some(Resolution { addresses: seq![Addr::V4(0x01020304), Addr::V4(0x05060708)], redirect: None }),
        answer_addresses(query_a(), reply(na_upper(), 1, false, 0, seq![a_rr(na_upper(), 0x01020304)], seq![], seq![]))
            == Some(Resolution { addresses: seq![Addr::V4(0x01020304)], redirect: None }),
        answer_addresses(query_a(), reply(na(), 1, false, 0, seq![a_rr(nb(), 0x01020304)], seq![], seq![]))
            == Some(Resolution { addresses: seq![], redirect: None }),
{
    assert(answer_addresses(
        query_a(),
        reply(na(), 1, false, 0, seq![a_rr(na(), 0x01020304), a_rr(na(), 0x05060708)], seq![], seq![]),
    ) == Some(Resolution { addresses: seq![Addr::V4(0x01020304), Addr::V4(0x05060708)], redirect: None })) by (compute_only);
    assert(answer_addresses(query_a(), reply(na_upper(), 1, false, 0, seq![a_rr(na_upper(), 0x01020304)], seq![], seq![]))
        == Some(Resolution { addresses: seq![Addr::V4(0x01020304)], redirect: None })) by (compute_only);
    assert(answer_addresses(query_a(), reply(na(), 1, false, 0, seq![a_rr(nb(), 0x01020304)], seq![], seq![]))
        == Some(Resolution { addresses: seq![], redirect: None })) by (compute_only);
}

/// RFC 3596: an AAAA query takes AAAA records and ignores A records, and an
/// A query takes A records and ignores AAAA records; only A and AAAA are
/// queried.
pub proof fn lemma_answer_types()
    ensures
        answer_addresses(query_aaaa(), reply(na(), 28, false, 0, seq![aaaa_rr(na(), 0x0102030405060708090a0b0c0d0e0f10)], seq![], seq![]))
            == Some(Resolution { addresses: seq![Addr::V6(0x0102030405060708090a0b0c0d0e0f10)], redirect: None }),
        answer_addresses(query_aaaa(), reply(na(), 28, false, 0, seq![a_rr(na(), 1)], seq![], seq![]))
            == Some(Resolution { addresses: seq![], redirect: None }),
        answer_addresses(query_a(), reply(na(), 1, false, 0, seq![aaaa_rr(na(), 1)], seq![], seq![]))
            == Some(Resolution { addresses: seq![], redirect: None }),
        answer_addresses(Query { id: 7, name: seq![97u8], qtype: 5 }, reply(na(), 5, false, 0, seq![], seq![], seq![])) is None,
{
    assert(answer_addresses(
        query_aaaa(),
        reply(na(), 28, false, 0, seq![aaaa_rr(na(), 0x0102030405060708090a0b0c0d0e0f10)], seq![], seq![]),
    ) == Some(Resolution { addresses: seq![Addr::V6(0x0102030405060708090a0b0c0d0e0f10)], redirect: None })) by (compute_only);
    assert(answer_addresses(query_aaaa(), reply(na(), 28, false, 0, seq![a_rr(na(), 1)], seq![], seq![]))
        == Some(Resolution { addresses: seq![], redirect: None })) by (compute_only);
    assert(answer_addresses(query_a(), reply(na(), 1, false, 0, seq![aaaa_rr(na(), 1)], seq![], seq![]))
        == Some(Resolution { addresses: seq![], redirect: None })) by (compute_only);
    assert(answer_addresses(Query { id: 7, name: seq![97u8], qtype: 5 }, reply(na(), 5, false, 0, seq![], seq![], seq![])) is None)
        by (compute_only);
}

/// RFC 1034 §3.6.2: a CNAME chain inside the answer section is followed,
/// in whatever order the records come, and its owners are compared up to
/// case; only the final name's addresses are returned.
pub proof fn lemma_answer_cname_chain()
    ensures
        answer_addresses(query_a(), reply(na(), 1, false, 0, seq![cname_rr(na(), nb()), cname_rr(nb(), nc()), a_rr(nc(), 9)], seq![], seq![]))
            == Some(Resolution { addresses: seq![Addr::V4(9)], redirect: None }),
        answer_addresses(
            query_a(),
            reply(na(), 1, false, 0, seq![a_rr(nc(), 9), cname_rr(seq![1u8, 66, 0], nc()), cname_rr(na_upper(), nb())], seq![], seq![]),
        ) == Some(Resolution { addresses: seq![Addr::V4(9)], redirect: None }),
        answer_addresses(query_a(), reply(na(), 1, false, 0, seq![a_rr(na(), 5), cname_rr(na(), nb()), a_rr(nb(), 6)], seq![], seq![]))
            == Some(Resolution { addresses: seq![Addr::V4(6)], redirect: None }),
{
    assert(answer_addresses(
        query_a(),
        reply(na(), 1, false, 0, seq![cname_rr(na(), nb()), cname_rr(nb(), nc()), a_rr(nc(), 9)], seq![], seq![]),
    ) == Some(Resolution { addresses: seq![Addr::V4(9)], redirect: None })) by (compute_only);
    assert(answer_addresses(
        query_a(),
        reply(na(), 1, false, 0, seq![a_rr(nc(), 9), cname_rr(seq![1u8, 66, 0], nc()), cname_rr(na_upper(), nb())], seq![], seq![]),
    ) == Some(Resolution { addresses: seq![Addr::V4(9)], redirect: None })) by (compute_only);
    assert(answer_addresses(query_a(), reply(na(), 1, false, 0, seq![a_rr(na(), 5), cname_rr(na(), nb()), a_rr(nb(), 6)], seq![], seq![]))
        == Some(Resolution { addresses: seq![Addr::V4(6)], redirect: None })) by (compute_only);
}

/// RFC 1034 §5.3.3 step 3a: a chain that leaves the answer section gives
/// the last target to ask about and no addresses; a loop is an error.
pub proof fn lemma_answer_cname_redirect()
    ensures
        answer_addresses(query_a(), reply(na(), 1, false, 0, seq![cname_rr(na(), nb()), cname_rr(nb(), nc())], seq![], seq![]))
            == Some(Resolution { addresses: seq![], redirect: Some(nc()) }),
        answer_addresses(query_a(), reply(na(), 1, false, 0, seq![cname_rr(na(), nb())], seq![], seq![]))
            == Some(Resolution { addresses: seq![], redirect: Some(nb()) }),
        answer_addresses(query_a(), reply(na(), 1, false, 0, seq![cname_rr(na(), nb()), cname_rr(nb(), na())], seq![], seq![])) is None,
        answer_addresses(query_a(), reply(na(), 1, false, 0, seq![cname_rr(na(), na())], seq![], seq![])) is None,
{
    assert(answer_addresses(query_a(), reply(na(), 1, false, 0, seq![cname_rr(na(), nb()), cname_rr(nb(), nc())], seq![], seq![]))
        == Some(Resolution { addresses: seq![], redirect: Some(nc()) })) by (compute_only);
    assert(answer_addresses(query_a(), reply(na(), 1, false, 0, seq![cname_rr(na(), nb())], seq![], seq![]))
        == Some(Resolution { addresses: seq![], redirect: Some(nb()) })) by (compute_only);
    assert(answer_addresses(query_a(), reply(na(), 1, false, 0, seq![cname_rr(na(), nb()), cname_rr(nb(), na())], seq![], seq![])) is None)
        by (compute_only);
    assert(answer_addresses(query_a(), reply(na(), 1, false, 0, seq![cname_rr(na(), na())], seq![], seq![])) is None) by (compute_only);
}

/// The authority and additional sections are never used: addresses in them
/// are not returned, and a CNAME there is not followed.
pub proof fn lemma_answer_sections()
    ensures
        answer_addresses(query_a(), reply(na(), 1, false, 0, seq![], seq![a_rr(na(), 1)], seq![a_rr(na(), 2)]))
            == Some(Resolution { addresses: seq![], redirect: None }),
        answer_addresses(query_a(), reply(na(), 1, false, 0, seq![], seq![cname_rr(na(), nb())], seq![cname_rr(na(), nb()), a_rr(nb(), 2)]))
            == Some(Resolution { addresses: seq![], redirect: None }),
{
    assert(answer_addresses(query_a(), reply(na(), 1, false, 0, seq![], seq![a_rr(na(), 1)], seq![a_rr(na(), 2)]))
        == Some(Resolution { addresses: seq![], redirect: None })) by (compute_only);
    assert(answer_addresses(
        query_a(),
        reply(na(), 1, false, 0, seq![], seq![cname_rr(na(), nb())], seq![cname_rr(na(), nb()), a_rr(nb(), 2)]),
    ) == Some(Resolution { addresses: seq![], redirect: None })) by (compute_only);
}

/// RCODE 3 (name error) gives no addresses; every other RCODE but 0 is
/// refused (RFC 1035 §4.1.1: 1 format error, 2 server failure, 4 not
/// implemented, 5 refused).
pub proof fn lemma_answer_rcodes()
    ensures
        answer_addresses(query_a(), reply(na(), 1, false, 3, seq![], seq![], seq![]))
            == Some(Resolution { addresses: seq![], redirect: None }),
        answer_addresses(query_a(), reply(na(), 1, false, 3, seq![a_rr(na(), 1)], seq![], seq![]))
            == Some(Resolution { addresses: seq![], redirect: None }),
        answer_addresses(query_a(), reply(na(), 1, false, 1, seq![a_rr(na(), 1)], seq![], seq![])) is None,
        answer_addresses(query_a(), reply(na(), 1, false, 2, seq![a_rr(na(), 1)], seq![], seq![])) is None,
        answer_addresses(query_a(), reply(na(), 1, false, 4, seq![a_rr(na(), 1)], seq![], seq![])) is None,
        answer_addresses(query_a(), reply(na(), 1, false, 5, seq![a_rr(na(), 1)], seq![], seq![])) is None,
{
    assert(answer_addresses(query_a(), reply(na(), 1, false, 3, seq![], seq![], seq![]))
        == Some(Resolution { addresses: seq![], redirect: None })) by (compute_only);
    assert(answer_addresses(query_a(), reply(na(), 1, false, 3, seq![a_rr(na(), 1)], seq![], seq![]))
        == Some(Resolution { addresses: seq![], redirect: None })) by (compute_only);
    assert(answer_addresses(query_a(), reply(na(), 1, false, 1, seq![a_rr(na(), 1)], seq![], seq![])) is None) by (compute_only);
    assert(answer_addresses(query_a(), reply(na(), 1, false, 2, seq![a_rr(na(), 1)], seq![], seq![])) is None) by (compute_only);
    assert(answer_addresses(query_a(), reply(na(), 1, false, 4, seq![a_rr(na(), 1)], seq![], seq![])) is None) by (compute_only);
    assert(answer_addresses(query_a(), reply(na(), 1, false, 5, seq![a_rr(na(), 1)], seq![], seq![])) is None) by (compute_only);
}

/// RFC 5452 §4 to §6: a reply is refused if its ID or question differ from
/// the query's, if it is not a response to a standard query, or if it is
/// truncated.
pub proof fn lemma_answer_matching()
    ensures
        answer_addresses(Query { id: 8, name: seq![97u8], qtype: 1 }, reply(na(), 1, false, 0, seq![a_rr(na(), 1)], seq![], seq![])) is None,
        answer_addresses(query_a(), reply(nb(), 1, false, 0, seq![a_rr(na(), 1)], seq![], seq![])) is None,
        answer_addresses(query_a(), reply(na(), 28, false, 0, seq![a_rr(na(), 1)], seq![], seq![])) is None,
        answer_addresses(
            query_a(),
            Message {
                questions: seq![Question { name: na(), qtype: 1, qclass: 3 }],
                ..reply(na(), 1, false, 0, seq![a_rr(na(), 1)], seq![], seq![])
            },
        ) is None,
        answer_addresses(
            query_a(),
            Message { questions: seq![], ..reply(na(), 1, false, 0, seq![a_rr(na(), 1)], seq![], seq![]) },
        ) is None,
        answer_addresses(
            query_a(),
            Message {
                questions: seq![Question { name: na(), qtype: 1, qclass: 1 }, Question { name: na(), qtype: 1, qclass: 1 }],
                ..reply(na(), 1, false, 0, seq![a_rr(na(), 1)], seq![], seq![])
            },
        ) is None,
        answer_addresses(
            query_a(),
            Message {
                header: Header { qr: false, ..reply_header(false, 0, 1, 1, 0, 0) },
                ..reply(na(), 1, false, 0, seq![a_rr(na(), 1)], seq![], seq![])
            },
        ) is None,
        answer_addresses(
            query_a(),
            Message {
                header: Header { opcode: 2, ..reply_header(false, 0, 1, 1, 0, 0) },
                ..reply(na(), 1, false, 0, seq![a_rr(na(), 1)], seq![], seq![])
            },
        ) is None,
        answer_addresses(query_a(), reply(na(), 1, true, 0, seq![a_rr(na(), 1)], seq![], seq![])) is None,
{
    assert(answer_addresses(Query { id: 8, name: seq![97u8], qtype: 1 }, reply(na(), 1, false, 0, seq![a_rr(na(), 1)], seq![], seq![])) is None)
        by (compute_only);
    assert(answer_addresses(query_a(), reply(nb(), 1, false, 0, seq![a_rr(na(), 1)], seq![], seq![])) is None) by (compute_only);
    assert(answer_addresses(query_a(), reply(na(), 28, false, 0, seq![a_rr(na(), 1)], seq![], seq![])) is None) by (compute_only);
    assert(answer_addresses(
        query_a(),
        Message {
            questions: seq![Question { name: na(), qtype: 1, qclass: 3 }],
            ..reply(na(), 1, false, 0, seq![a_rr(na(), 1)], seq![], seq![])
        },
    ) is None) by (compute_only);
    assert(answer_addresses(
        query_a(),
        Message { questions: seq![], ..reply(na(), 1, false, 0, seq![a_rr(na(), 1)], seq![], seq![]) },
    ) is None) by (compute_only);
    assert(answer_addresses(
        query_a(),
        Message {
            questions: seq![Question { name: na(), qtype: 1, qclass: 1 }, Question { name: na(), qtype: 1, qclass: 1 }],
            ..reply(na(), 1, false, 0, seq![a_rr(na(), 1)], seq![], seq![])
        },
    ) is None) by (compute_only);
    assert(answer_addresses(
        query_a(),
        Message {
            header: Header { qr: false, ..reply_header(false, 0, 1, 1, 0, 0) },
            ..reply(na(), 1, false, 0, seq![a_rr(na(), 1)], seq![], seq![])
        },
    ) is None) by (compute_only);
    assert(answer_addresses(
        query_a(),
        Message {
            header: Header { opcode: 2, ..reply_header(false, 0, 1, 1, 0, 0) },
            ..reply(na(), 1, false, 0, seq![a_rr(na(), 1)], seq![], seq![])
        },
    ) is None) by (compute_only);
    assert(answer_addresses(query_a(), reply(na(), 1, true, 0, seq![a_rr(na(), 1)], seq![], seq![])) is None) by (compute_only);
}

// ---------------------------------------------------------------------------
// §4.1: a whole message, and the query we send.
// ---------------------------------------------------------------------------

/// The query for "example.com", type A, ID 0x1234, built octet by octet from
/// §4.1: the header (ID, flags 0x0100, QDCOUNT 1, no records), QNAME, QTYPE
/// 1 and QCLASS 1; and for AAAA, a trailing dot, the root, and a bad name.
pub proof fn lemma_query_example()
    ensures
        encode_query(Query { id: 0x1234, name: seq![101u8, 120, 97, 109, 112, 108, 101, 46, 99, 111, 109], qtype: 1 }) == Some(
            seq![0x12u8, 0x34, 0x01, 0x00, 0, 1, 0, 0, 0, 0, 0, 0, 7, 101, 120, 97, 109, 112, 108, 101, 3, 99, 111, 109, 0, 0, 1, 0, 1],
        ),
        encode_query(Query { id: 0xABCD, name: seq![97u8, 46], qtype: 28 }) == Some(
            seq![0xABu8, 0xCD, 0x01, 0x00, 0, 1, 0, 0, 0, 0, 0, 0, 1, 97, 0, 0, 28, 0, 1],
        ),
        encode_query(Query { id: 1, name: seq![46u8], qtype: 1 }) == Some(seq![0u8, 1, 0x01, 0x00, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1]),
        encode_query(Query { id: 1, name: seq![97u8, 46, 46, 98], qtype: 1 }) is None,
{
    assert(encode_query(Query { id: 0x1234, name: seq![101u8, 120, 97, 109, 112, 108, 101, 46, 99, 111, 109], qtype: 1 }) == Some(
        seq![0x12u8, 0x34, 0x01, 0x00, 0, 1, 0, 0, 0, 0, 0, 0, 7, 101, 120, 97, 109, 112, 108, 101, 3, 99, 111, 109, 0, 0, 1, 0, 1],
    )) by (compute_only);
    assert(encode_query(Query { id: 0xABCD, name: seq![97u8, 46], qtype: 28 }) == Some(
        seq![0xABu8, 0xCD, 0x01, 0x00, 0, 1, 0, 0, 0, 0, 0, 0, 1, 97, 0, 0, 28, 0, 1],
    )) by (compute_only);
    assert(encode_query(Query { id: 1, name: seq![46u8], qtype: 1 }) == Some(seq![0u8, 1, 0x01, 0x00, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1]))
        by (compute_only);
    assert(encode_query(Query { id: 1, name: seq![97u8, 46, 46, 98], qtype: 1 }) is None) by (compute_only);
}

/// A reply built from §4.1 and §3.4.1: the header (ID 7, flags 0x8180: QR,
/// RD, RA), one question "a" A IN, and one answer whose owner is a pointer
/// to the question's name at offset 12 (§4.1.4), type A, class IN, TTL
/// 300, RDLENGTH 4, address 1.2.3.4. It decodes to the message; with TC set
/// in the flags it decodes with TC set (§4.1.1).
pub proof fn lemma_reply_example()
    ensures
        decode_message(
            seq![0u8, 7, 0x81, 0x80, 0, 1, 0, 1, 0, 0, 0, 0, 1, 97, 0, 0, 1, 0, 1, 0xC0, 12, 0, 1, 0, 1, 0, 0, 1, 44, 0, 4, 1, 2, 3, 4],
        ) == Some(reply(na(), 1, false, 0, seq![a_rr(na(), 0x01020304)], seq![], seq![])),
        decode_message(
            seq![0u8, 7, 0x83, 0x80, 0, 1, 0, 1, 0, 0, 0, 0, 1, 97, 0, 0, 1, 0, 1, 0xC0, 12, 0, 1, 0, 1, 0, 0, 1, 44, 0, 4, 1, 2, 3, 4],
        ) == Some(reply(na(), 1, true, 0, seq![a_rr(na(), 0x01020304)], seq![], seq![])),
{
    assert(decode_message(
        seq![0u8, 7, 0x81, 0x80, 0, 1, 0, 1, 0, 0, 0, 0, 1, 97, 0, 0, 1, 0, 1, 0xC0, 12, 0, 1, 0, 1, 0, 0, 1, 44, 0, 4, 1, 2, 3, 4],
    ) == Some(reply(na(), 1, false, 0, seq![a_rr(na(), 0x01020304)], seq![], seq![]))) by (compute_only);
    assert(decode_message(
        seq![0u8, 7, 0x83, 0x80, 0, 1, 0, 1, 0, 0, 0, 0, 1, 97, 0, 0, 1, 0, 1, 0xC0, 12, 0, 1, 0, 1, 0, 0, 1, 44, 0, 4, 1, 2, 3, 4],
    ) == Some(reply(na(), 1, true, 0, seq![a_rr(na(), 0x01020304)], seq![], seq![]))) by (compute_only);
}

/// The record rules: RDLENGTH must be 4 for an A record and 16 for AAAA, a
/// CNAME's name must fill its RDATA, unknown types are kept as opaque
/// RDATA, a class other than IN is not interpreted, octets after the last
/// record are an error, and so is a count larger than what follows.
pub proof fn lemma_record_rules()
    ensures
        decode_message(seq![0u8, 7, 0x81, 0x80, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 1, 44, 0, 3, 1, 2, 3]) is None,
        decode_message(seq![0u8, 7, 0x81, 0x80, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 1, 44, 0, 5, 1, 2, 3, 4, 5]) is None,
        decode_message(seq![0u8, 7, 0x81, 0x80, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 28, 0, 1, 0, 0, 1, 44, 0, 4, 1, 2, 3, 4]) is None,
        decode_message(seq![0u8, 7, 0x81, 0x80, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 5, 0, 1, 0, 0, 1, 44, 0, 4, 1, 98, 0, 0]) is None,
        decode_message(seq![0u8, 7, 0x81, 0x80, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 16, 0, 1, 0, 0, 1, 44, 0, 2, 1, 9]) == Some(
            Message {
                header: reply_header(false, 0, 0, 1, 0, 0),
                questions: seq![],
                answers: seq![Rr { name: seq![0u8], rtype: 16, rclass: 1, ttl: 300, rdata: Rdata::Opaque(seq![1u8, 9]) }],
                authority: seq![],
                additional: seq![],
            },
        ),
        decode_message(seq![0u8, 7, 0x81, 0x80, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 3, 0, 0, 1, 44, 0, 1, 9]) == Some(
            Message {
                header: reply_header(false, 0, 0, 1, 0, 0),
                questions: seq![],
                answers: seq![Rr { name: seq![0u8], rtype: 1, rclass: 3, ttl: 300, rdata: Rdata::Opaque(seq![9u8]) }],
                authority: seq![],
                additional: seq![],
            },
        ),
        decode_message(seq![0u8, 7, 0x81, 0x80, 0, 0, 0, 0, 0, 0, 0, 0, 0]) is None,
        decode_message(seq![0u8, 7, 0x81, 0x80, 0, 0, 0, 1, 0, 0, 0, 0]) is None,
        decode_message(seq![0u8, 7, 0x81, 0x80, 0xFF, 0xFF, 0, 0, 0, 0, 0, 0]) is None,
        decode_message(seq![0u8, 7, 0x81, 0x80, 0, 0, 0, 0, 0, 0, 0]) is None,
{
    assert(decode_message(seq![0u8, 7, 0x81, 0x80, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 1, 44, 0, 3, 1, 2, 3]) is None) by (compute_only);
    assert(decode_message(seq![0u8, 7, 0x81, 0x80, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 1, 44, 0, 5, 1, 2, 3, 4, 5]) is None)
        by (compute_only);
    assert(decode_message(seq![0u8, 7, 0x81, 0x80, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 28, 0, 1, 0, 0, 1, 44, 0, 4, 1, 2, 3, 4]) is None)
        by (compute_only);
    assert(decode_message(seq![0u8, 7, 0x81, 0x80, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 5, 0, 1, 0, 0, 1, 44, 0, 4, 1, 98, 0, 0]) is None)
        by (compute_only);
    assert(decode_message(seq![0u8, 7, 0x81, 0x80, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 16, 0, 1, 0, 0, 1, 44, 0, 2, 1, 9]) == Some(
        Message {
            header: reply_header(false, 0, 0, 1, 0, 0),
            questions: seq![],
            answers: seq![Rr { name: seq![0u8], rtype: 16, rclass: 1, ttl: 300, rdata: Rdata::Opaque(seq![1u8, 9]) }],
            authority: seq![],
            additional: seq![],
        },
    )) by (compute_only);
    assert(decode_message(seq![0u8, 7, 0x81, 0x80, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 3, 0, 0, 1, 44, 0, 1, 9]) == Some(
        Message {
            header: reply_header(false, 0, 0, 1, 0, 0),
            questions: seq![],
            answers: seq![Rr { name: seq![0u8], rtype: 1, rclass: 3, ttl: 300, rdata: Rdata::Opaque(seq![9u8]) }],
            authority: seq![],
            additional: seq![],
        },
    )) by (compute_only);
    assert(decode_message(seq![0u8, 7, 0x81, 0x80, 0, 0, 0, 0, 0, 0, 0, 0, 0]) is None) by (compute_only);
    assert(decode_message(seq![0u8, 7, 0x81, 0x80, 0, 0, 0, 1, 0, 0, 0, 0]) is None) by (compute_only);
    assert(decode_message(seq![0u8, 7, 0x81, 0x80, 0xFF, 0xFF, 0, 0, 0, 0, 0, 0]) is None) by (compute_only);
    assert(decode_message(seq![0u8, 7, 0x81, 0x80, 0, 0, 0, 0, 0, 0, 0]) is None) by (compute_only);
}

/// §4.2.2 and §2.3.4: a two octet length, then the message; a UDP message
/// is 512 octets or less.
pub proof fn lemma_tcp_and_udp_limits()
    ensures
        tcp_frame(seq![9u8, 8, 7]) == Some(seq![0u8, 3, 9, 8, 7]),
        tcp_frame(fill(1, 300)) == Some(seq![1u8, 44] + fill(1, 300)),
        tcp_message_len(seq![0u8, 3, 9, 8, 7, 6]) == Some(3nat),
        tcp_message_len(seq![0u8, 3, 9, 8]) is None,
        tcp_message_len(seq![0u8]) is None,
        tcp_message_len(seq![1u8, 44] + fill(1, 300)) == Some(300nat),
        decode_udp(fill(0, 513)) is None,
{
    assert(tcp_frame(seq![9u8, 8, 7]) == Some(seq![0u8, 3, 9, 8, 7])) by (compute_only);
    assert(tcp_frame(fill(1, 300)) == Some(seq![1u8, 44] + fill(1, 300))) by (compute_only);
    assert(tcp_message_len(seq![0u8, 3, 9, 8, 7, 6]) == Some(3nat)) by (compute_only);
    assert(tcp_message_len(seq![0u8, 3, 9, 8]) is None) by (compute_only);
    assert(tcp_message_len(seq![0u8]) is None) by (compute_only);
    assert(tcp_message_len(seq![1u8, 44] + fill(1, 300)) == Some(300nat)) by (compute_only);
    assert(decode_udp(fill(0, 513)) is None) by (compute_only);
}

} // verus!
