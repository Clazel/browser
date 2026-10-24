//! The executable answer extraction, proven to meet [`super::contract`].
//! It follows `spec::answer_addresses` (RFC 1034 §3.6.2 and §5.3.3, RFC
//! 5452 §4 to §6; the quotes live there).

use super::decode::copy_range;
use super::encode::dotted_to_wire;
use super::spec;
use super::spec::Addr;
use super::types::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// §2.3.3: fold the ASCII letters A to Z to lower case.
fn lower(x: u8) -> (r: u8)
    ensures
        r == spec::lower(x),
{
    if x > 64 && x < 91 {
        // x <= 90, so this does not saturate.
        x.saturating_add(32)
    } else {
        x
    }
}

/// §2.3.3: whether `a` and `b` are equal up to case; see
/// `spec::bytes_eq_ci`.
pub(crate) fn names_eq(a: &[u8], b: &[u8]) -> (r: bool)
    ensures
        r == spec::bytes_eq_ci(a@, b@),
{
    if a.len() != b.len() {
        return false;
    }
    let mut i: usize = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            a@.len() == b@.len(),
            spec::eq_from(a@, b@, 0) == spec::eq_from(a@, b@, i as nat),
        decreases a.len() - i,
    {
        let x = match a.get(i) {
            Some(&x) => x,
            None => return false,
        };
        let y = match b.get(i) {
            Some(&y) => y,
            None => return false,
        };
        if lower(x) != lower(y) {
            return false;
        }
        // i < a.len(), so this does not saturate.
        i = i.saturating_add(1);
    }
    true
}

/// The address a record gives for a query of type `qtype`; see
/// `spec::rr_addr`.
fn rr_addr(rec: &Rec, qtype: u16) -> (r: Option<Addr>)
    ensures
        r == spec::rr_addr(rec@, qtype),
{
    match &rec.rdata {
        Rd::A(a) => {
            if qtype == spec::TYPE_A && rec.rtype == spec::TYPE_A && rec.rclass == spec::CLASS_IN {
                Some(Addr::V4(*a))
            } else {
                None
            }
        },
        Rd::Aaaa(a) => {
            if qtype == spec::TYPE_AAAA && rec.rtype == spec::TYPE_AAAA && rec.rclass == spec::CLASS_IN {
                Some(Addr::V6(*a))
            } else {
                None
            }
        },
        _ => None,
    }
}

/// The target of `rec` if it is a CNAME record (class IN, TYPE 5) whose
/// owner is `name`.
fn cname_target<'a>(rec: &'a Rec, name: &[u8]) -> (r: Option<&'a [u8]>)
    ensures
        match r {
            Some(t) => spec::rr_cname(rec@) == Some(t@) && spec::bytes_eq_ci(rec@.name, name@),
            None => !(spec::rr_cname(rec@) is Some && spec::bytes_eq_ci(rec@.name, name@)),
        },
{
    if rec.rtype != spec::TYPE_CNAME || rec.rclass != spec::CLASS_IN {
        return None;
    }
    match &rec.rdata {
        Rd::Cname(t) => {
            if names_eq(rec.name.as_slice(), name) {
                Some(t.as_slice())
            } else {
                None
            }
        },
        _ => None,
    }
}

/// The target of record `i` of `answers`, if it is a CNAME record whose
/// owner is `name`.
fn cname_at<'a>(answers: &'a [Rec], i: usize, name: &[u8]) -> (r: Option<&'a [u8]>)
    requires
        i < answers.len(),
    ensures
        match r {
            Some(t) => spec::rr_cname(answers@[i as int]@) == Some(t@) && spec::bytes_eq_ci(answers@[i as int]@.name, name@),
            None => !(spec::rr_cname(answers@[i as int]@) is Some && spec::bytes_eq_ci(answers@[i as int]@.name, name@)),
        },
{
    let rec = answers.get(i)?;
    cname_target(rec, name)
}

/// RFC 1034 §3.6.2: the target of the first CNAME record in `answers`
/// whose owner is `name`; see `spec::cname_next`.
fn cname_next<'a>(answers: &'a [Rec], name: &[u8]) -> (r: Option<&'a [u8]>)
    ensures
        match r {
            Some(t) => spec::cname_next(rec_views(answers@), name@) == Some(t@),
            None => spec::cname_next(rec_views(answers@), name@) is None,
        },
{
    let mut i: usize = 0;
    proof {
        assert(rec_views(answers@).skip(0) =~= rec_views(answers@));
    }
    while i < answers.len()
        invariant
            i <= answers.len(),
            spec::cname_next(rec_views(answers@), name@) == spec::cname_next(rec_views(answers@).skip(i as int), name@),
        decreases answers.len() - i,
    {
        proof {
            assert(rec_views(answers@).skip(i as int).drop_first() =~= rec_views(answers@).skip(i as int + 1));
        }
        if let Some(t) = cname_at(answers, i, name) {
            return Some(t);
        }
        // i < answers.len(), so this does not saturate.
        i = i.saturating_add(1);
    }
    None
}

/// RFC 1034 §5.3.3 step 3a: follow CNAME records from `start`; see
/// `spec::chain_end`. Returns the final name and the number of hops.
fn chain_end<'a>(answers: &'a [Rec], start: &'a [u8]) -> (r: Option<(&'a [u8], usize)>)
    ensures
        match r {
            Some((fin, hops)) => spec::chain_end(rec_views(answers@), start@, 0, answers@.len()) == Some((fin@, hops as nat)),
            None => spec::chain_end(rec_views(answers@), start@, 0, answers@.len()) is None,
        },
{
    let mut cur: &'a [u8] = start;
    let mut hops: usize = 0;
    let mut fuel: usize = answers.len();
    loop
        invariant
            hops + fuel == answers.len(),
            spec::chain_end(rec_views(answers@), cur@, hops as nat, fuel as nat) == spec::chain_end(
                rec_views(answers@),
                start@,
                0,
                answers@.len(),
            ),
        decreases fuel,
    {
        match cname_next(answers, cur) {
            None => return Some((cur, hops)),
            Some(t) => {
                if fuel == 0 {
                    return None;
                }
                cur = t;
                // hops + fuel == answers.len() and fuel > 0: neither
                // operation saturates.
                hops = hops.saturating_add(1);
                fuel = fuel.saturating_sub(1);
            },
        }
    }
}

/// The address of `rec` if it gives one for `qtype` and its owner is
/// `name`.
fn addr_for(rec: &Rec, name: &[u8], qtype: u16) -> (r: Option<Addr>)
    ensures
        match r {
            Some(a) => spec::rr_addr(rec@, qtype) == Some(a) && spec::bytes_eq_ci(rec@.name, name@),
            None => !(spec::rr_addr(rec@, qtype) is Some && spec::bytes_eq_ci(rec@.name, name@)),
        },
{
    let a = rr_addr(rec, qtype)?;
    if names_eq(rec.name.as_slice(), name) {
        Some(a)
    } else {
        None
    }
}

/// The address of record `i` of `answers`, if it gives one for `qtype` and
/// its owner is `name`.
fn addr_at(answers: &[Rec], i: usize, name: &[u8], qtype: u16) -> (r: Option<Addr>)
    requires
        i < answers.len(),
    ensures
        match r {
            Some(a) => spec::rr_addr(answers@[i as int]@, qtype) == Some(a) && spec::bytes_eq_ci(answers@[i as int]@.name, name@),
            None => !(spec::rr_addr(answers@[i as int]@, qtype) is Some && spec::bytes_eq_ci(answers@[i as int]@.name, name@)),
        },
{
    let rec = answers.get(i)?;
    addr_for(rec, name, qtype)
}

/// The addresses of the records of `answers` owned by `name`; see
/// `spec::collect`.
fn collect(answers: &[Rec], name: &[u8], qtype: u16) -> (out: Vec<Addr>)
    ensures
        out@ == spec::collect(rec_views(answers@), name@, qtype),
{
    let mut out: Vec<Addr> = Vec::new();
    let mut i: usize = 0;
    proof {
        assert(rec_views(answers@).skip(0) =~= rec_views(answers@));
        assert(out@ + spec::collect(rec_views(answers@), name@, qtype) =~= spec::collect(rec_views(answers@), name@, qtype));
    }
    while i < answers.len()
        invariant
            i <= answers.len(),
            out@ + spec::collect(rec_views(answers@).skip(i as int), name@, qtype) == spec::collect(rec_views(answers@), name@, qtype),
        decreases answers.len() - i,
    {
        proof {
            let views = rec_views(answers@);
            assert(views.skip(i as int).drop_first() =~= views.skip(i as int + 1));
            assert(views.skip(i as int)[0] == views[i as int]);
        }
        if let Some(a) = addr_at(answers, i, name, qtype) {
            let ghost before = out@;
            out.push(a);
            proof {
                let rest = spec::collect(rec_views(answers@).skip(i as int + 1), name@, qtype);
                assert(out@ =~= before.push(a));
                assert(before.push(a) + rest =~= before + (seq![a] + rest));
            }
        }
        // i < answers.len(), so this does not saturate.
        i = i.saturating_add(1);
    }
    proof {
        assert(rec_views(answers@).skip(answers@.len() as int) =~= Seq::<spec::Rr>::empty());
        assert(out@ + Seq::<Addr>::empty() =~= out@);
    }
    out
}

/// The addresses a reply gives for the query (`id`, `name`, `qtype`), or
/// `None` if it is not an acceptable answer to it; see
/// `spec::answer_addresses`. `name` is a dotted ASCII host name.
pub fn answer_addresses(id: u16, name: &[u8], qtype: u16, msg: &Msg) -> (output: Option<Resolved>)
    ensures
        super::contract::answer_addresses_ensures(id, name@, qtype, msg@, option_resolved(output)),
{
    let qname = dotted_to_wire(name)?;
    if qtype != spec::TYPE_A && qtype != spec::TYPE_AAAA {
        return None;
    }
    let h = msg.header;
    if !h.qr || h.opcode != 0 || h.tc || h.id != id {
        return None;
    }
    if msg.questions.len() != 1 {
        return None;
    }
    let q = msg.questions.first()?;
    proof {
        assert(msg@.questions[0] == q@);
    }
    if !(names_eq(q.name.as_slice(), qname.as_slice()) && q.qtype == qtype && q.qclass == spec::CLASS_IN) {
        return None;
    }
    if h.rcode == 3 {
        return Some(Resolved { addresses: Vec::new(), redirect: None });
    }
    if h.rcode != 0 {
        return None;
    }
    let (fin, hops) = chain_end(msg.answers.as_slice(), qname.as_slice())?;
    let addresses = collect(msg.answers.as_slice(), fin, qtype);
    if hops > 0 && addresses.is_empty() {
        let target = copy_range(fin, 0, fin.len());
        proof {
            assert(fin@.subrange(0, fin@.len() as int) =~= fin@);
        }
        Some(Resolved { addresses: Vec::new(), redirect: Some(target) })
    } else {
        Some(Resolved { addresses, redirect: None })
    }
}

} // verus!
