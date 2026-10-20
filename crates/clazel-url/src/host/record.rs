//! The executable host record, and the string helpers the other exec
//! modules share. Each helper is proven equal to its spec definition.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// A host (URL §3.1), viewed as [`Host`]. Strings are code points as
/// `u32`; an IPv4 address is a `u32` and an IPv6 address its eight pieces.
pub enum ParsedHost {
    /// A domain.
    Domain(Vec<u32>),
    /// An IPv4 address.
    Ipv4(u32),
    /// An IPv6 address.
    Ipv6([u16; 8]),
    /// An opaque host.
    Opaque(Vec<u32>),
    /// The empty host.
    Empty,
}

impl View for ParsedHost {
    type V = Host;

    open spec fn view(&self) -> Host {
        match self {
            ParsedHost::Domain(s) => Host::Domain(s@),
            ParsedHost::Ipv4(a) => Host::Ipv4(*a as nat),
            ParsedHost::Ipv6(a) => Host::Ipv6(super::contract::pieces_view(a@)),
            ParsedHost::Opaque(s) => Host::Opaque(s@),
            ParsedHost::Empty => Host::Empty,
        }
    }
}

/// The view of an optional host; `None` is failure.
pub open spec fn option_view(h: Option<ParsedHost>) -> Option<Host> {
    match h {
        Some(h) => Some(h@),
        None => None,
    }
}

/// The view of an optional string.
pub open spec fn opt_seq(o: Option<Vec<u32>>) -> Option<Seq<u32>> {
    match o {
        Some(v) => Some(v@),
        None => None,
    }
}

/// An optional index, as the spec's `Option<int>`.
pub open spec fn opt_int(o: Option<usize>) -> Option<int> {
    match o {
        Some(i) => Some(i as int),
        None => None,
    }
}

/// The spec view of a list of strings.
pub open spec fn parts_view(v: Seq<Vec<u32>>) -> Seq<Seq<u32>> {
    v.map_values(|t: Vec<u32>| t@)
}

/// A copy of `s`.
pub fn copy(s: &[u32]) -> (out: Vec<u32>)
    ensures
        out@ == s@,
{
    vstd::slice::slice_to_vec(s)
}

/// Append `s` to `out`.
pub fn append(out: &mut Vec<u32>, s: &[u32])
    ensures
        final(out)@ == old(out)@ + s@,
{
    let ghost start = out@;
    let mut i: usize = 0;
    while i < s.len()
        invariant
            i <= s.len(),
            out@ == start + s@.subrange(0, i as int),
        decreases s.len() - i,
    {
        if let Some(c) = s.get(i) {
            out.push(*c);
        }
        i = i.saturating_add(1);
        assert(out@ =~= start + s@.subrange(0, i as int));
    }
    assert(s@.subrange(0, s@.len() as int) =~= s@);
}

/// `v` with element `i` replaced by `x`.
pub fn updated(v: &[u16], i: usize, x: u16) -> (out: Vec<u16>)
    requires
        i < v.len(),
    ensures
        out@ == v@.update(i as int, x),
{
    let mut out: Vec<u16> = Vec::new();
    let mut k: usize = 0;
    while k < v.len()
        invariant
            k <= v.len(),
            i < v.len(),
            out@ == v@.update(i as int, x).subrange(0, k as int),
        decreases v.len() - k,
    {
        if let Some(e) = v.get(k) {
            if k == i {
                out.push(x);
            } else {
                out.push(*e);
            }
        }
        k = k.saturating_add(1);
        assert(out@ =~= v@.update(i as int, x).subrange(0, k as int));
    }
    assert(v@.update(i as int, x).subrange(0, v@.len() as int) =~= v@.update(i as int, x));
    out
}

/// Element `i` of `v`, which exists.
pub fn at32(v: &[u32], i: usize) -> (out: u32)
    requires
        i < v.len(),
    ensures
        out == v@[i as int],
{
    match v.get(i) {
        Some(e) => *e,
        // Unreachable: i < v.len().
        None => 0,
    }
}

/// Element `i` of `v`, which exists.
pub fn at16(v: &[u16], i: usize) -> (out: u16)
    requires
        i < v.len(),
    ensures
        out == v@[i as int],
{
    match v.get(i) {
        Some(e) => *e,
        // Unreachable: i < v.len().
        None => 0,
    }
}

} // verus!
