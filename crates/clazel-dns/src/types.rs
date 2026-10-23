//! The executable message types: the exec twins of the spec's [`Message`],
//! [`Question`], [`Rr`], [`Rdata`] and [`Resolution`], whose views they
//! are. [`Header`] and [`Addr`] are plain data and are shared with the spec.

use super::spec::{Addr, Header, Message, Question, Rdata, Resolution, Rr};
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The RDATA of a record; see [`Rdata`].
#[derive(Debug, PartialEq, Eq)]
pub enum Rd {
    /// An A record's address.
    A(u32),
    /// An AAAA record's address.
    Aaaa(u128),
    /// A CNAME record's target, in uncompressed wire format.
    Cname(Vec<u8>),
    /// The octets of any other record's RDATA.
    Opaque(Vec<u8>),
}

/// A question; see [`Question`]. `name` is in uncompressed wire format: the
/// labels, each after its length octet, and the final zero octet.
#[derive(Debug, PartialEq, Eq)]
pub struct Quest {
    /// QNAME.
    pub name: Vec<u8>,
    /// QTYPE.
    pub qtype: u16,
    /// QCLASS.
    pub qclass: u16,
}

/// A resource record; see [`Rr`].
#[derive(Debug, PartialEq, Eq)]
pub struct Rec {
    /// NAME, in uncompressed wire format.
    pub name: Vec<u8>,
    /// TYPE.
    pub rtype: u16,
    /// CLASS.
    pub rclass: u16,
    /// TTL, as sent.
    pub ttl: u32,
    /// RDATA.
    pub rdata: Rd,
}

/// A decoded message; see [`Message`].
#[derive(Debug, PartialEq, Eq)]
pub struct Msg {
    /// The header.
    pub header: Header,
    /// The question section.
    pub questions: Vec<Quest>,
    /// The answer section.
    pub answers: Vec<Rec>,
    /// The authority section.
    pub authority: Vec<Rec>,
    /// The additional section.
    pub additional: Vec<Rec>,
}

/// What a reply gives for a query; see [`Resolution`].
#[derive(Debug, PartialEq, Eq)]
pub struct Resolved {
    /// The addresses of the answer section's records at the final name.
    pub addresses: Vec<Addr>,
    /// A name to ask about instead (the last CNAME target).
    pub redirect: Option<Vec<u8>>,
}

impl View for Rd {
    type V = Rdata;

    open spec fn view(&self) -> Rdata {
        match self {
            Rd::A(a) => Rdata::A(*a),
            Rd::Aaaa(a) => Rdata::Aaaa(*a),
            Rd::Cname(n) => Rdata::Cname(n@),
            Rd::Opaque(o) => Rdata::Opaque(o@),
        }
    }
}

impl View for Quest {
    type V = Question;

    open spec fn view(&self) -> Question {
        Question { name: self.name@, qtype: self.qtype, qclass: self.qclass }
    }
}

impl View for Rec {
    type V = Rr;

    open spec fn view(&self) -> Rr {
        Rr { name: self.name@, rtype: self.rtype, rclass: self.rclass, ttl: self.ttl, rdata: self.rdata@ }
    }
}

impl View for Msg {
    type V = Message;

    open spec fn view(&self) -> Message {
        Message {
            header: self.header,
            questions: quest_views(self.questions@),
            answers: rec_views(self.answers@),
            authority: rec_views(self.authority@),
            additional: rec_views(self.additional@),
        }
    }
}

impl View for Resolved {
    type V = Resolution;

    open spec fn view(&self) -> Resolution {
        Resolution { addresses: self.addresses@, redirect: opt_bytes(self.redirect) }
    }
}

/// The spec view of a sequence of questions.
pub open spec fn quest_views(s: Seq<Quest>) -> Seq<Question> {
    s.map_values(|q: Quest| q@)
}

/// The spec view of a sequence of records.
pub open spec fn rec_views(s: Seq<Rec>) -> Seq<Rr> {
    s.map_values(|r: Rec| r@)
}

/// The view of an optional octet vector.
pub open spec fn opt_bytes(o: Option<Vec<u8>>) -> Option<Seq<u8>> {
    match o {
        Some(v) => Some(v@),
        None => None,
    }
}

/// The view of an optional message.
pub open spec fn option_msg(m: Option<Msg>) -> Option<Message> {
    match m {
        Some(m) => Some(m@),
        None => None,
    }
}

/// The view of an optional result.
pub open spec fn option_resolved(r: Option<Resolved>) -> Option<Resolution> {
    match r {
        Some(r) => Some(r@),
        None => None,
    }
}

/// Pushing a question pushes its view.
pub proof fn lemma_quest_views_push(s: Seq<Quest>, q: Quest)
    ensures
        quest_views(s.push(q)) =~= quest_views(s).push(q@),
{
    assert(quest_views(s.push(q)).len() == s.len() + 1);
    assert forall|i: int| 0 <= i < s.len() + 1 implies quest_views(s.push(q))[i] == quest_views(s).push(q@)[i] by {
        if i < s.len() {
            assert(s.push(q)[i] == s[i]);
        }
    }
}

/// Pushing a record pushes its view.
pub proof fn lemma_rec_views_push(s: Seq<Rec>, r: Rec)
    ensures
        rec_views(s.push(r)) =~= rec_views(s).push(r@),
{
    assert(rec_views(s.push(r)).len() == s.len() + 1);
    assert forall|i: int| 0 <= i < s.len() + 1 implies rec_views(s.push(r))[i] == rec_views(s).push(r@)[i] by {
        if i < s.len() {
            assert(s.push(r)[i] == s[i]);
        }
    }
}

} // verus!
