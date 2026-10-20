//! The executable IPv6 parser (URL §3.5), proven to meet
//! [`super::contract`]. Each loop mirrors its spec function; the step
//! comments live in [`super::spec`].

use super::ipv4::{hex_value, is_hex};
use super::record::{at16, at32, updated};
#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The spec view of the IPv6 main loop's result.
pub open spec fn main_view(r: Option<(Vec<u16>, usize, Option<usize>)>) -> Option<(Seq<nat>, int, Option<int>)> {
    match r {
        Some((a, p, c)) => Some((super::contract::pieces_view(a@), p as int, super::record::opt_int(c))),
        None => None,
    }
}

/// `pieces_view` after an update.
proof fn lemma_pieces_view_update(a: Seq<u16>, i: int, x: u16)
    requires
        0 <= i < a.len(),
    ensures
        super::contract::pieces_view(a.update(i, x)) == super::contract::pieces_view(a).update(i, x as nat),
{
    assert(super::contract::pieces_view(a.update(i, x)) =~= super::contract::pieces_view(a).update(i, x as nat));
}

/// Step 6.4: the value and length of up to four hex digits at `start`.
fn hex_digits(input: &[u32], start: usize) -> (r: (u32, usize))
    requires
        start <= input.len(),
    ensures
        ipv6_hex_digits(input@, start as int, 0, 0) == (r.0 as nat, r.1 as nat),
        r.1 <= 4,
        start + r.1 <= input.len(),
        r.0 < 0x1_0000,
{
    let mut value: u32 = 0;
    let mut length: usize = 0;
    // Never saturates: start + length <= input.len().
    while length < 4 && start.saturating_add(length) < input.len() && is_hex(at32(input, start.saturating_add(length)))
        invariant
            length <= 4,
            start + length <= input.len(),
            length == 0 ==> value == 0,
            length == 1 ==> value < 0x10,
            length == 2 ==> value < 0x100,
            length == 3 ==> value < 0x1000,
            length == 4 ==> value < 0x1_0000,
            ipv6_hex_digits(input@, start as int, 0, 0) == ipv6_hex_digits(input@, start as int, value as nat, length as nat),
        decreases 4 - length,
    {
        let d = hex_value(at32(input, start.saturating_add(length)));
        // Never saturate: value < 0x1000 here, d < 16.
        value = value.saturating_mul(16).saturating_add(d as u32);
        length = length.saturating_add(1);
    }
    (value, length)
}

/// IPv4-in-IPv6 step 6.5.5.4 after its first digit: the rest of the
/// digits of one decimal number, from `pointer`.
fn ipv4_piece_digits_exec(input: &[u32], pointer: usize, ipv4_piece: u32) -> (r: Option<(u32, usize)>)
    requires
        pointer <= input.len(),
        ipv4_piece <= 255,
    ensures
        match r {
            Some((p, q)) => ipv4_piece_digits(input@, pointer as int, ipv4_piece as nat) == Some((p as nat, q as int)) && p <= 255
                && pointer <= q <= input.len(),
            None => ipv4_piece_digits(input@, pointer as int, ipv4_piece as nat) is None,
        },
{
    let mut piece = ipv4_piece;
    let mut p = pointer;
    while p < input.len() && 0x30 <= at32(input, p) && at32(input, p) <= 0x39
        invariant
            pointer <= p <= input.len(),
            piece <= 255,
            ipv4_piece_digits(input@, pointer as int, ipv4_piece as nat) == ipv4_piece_digits(input@, p as int, piece as nat),
        decreases input.len() - p,
    {
        if piece == 0 {
            return None;
        }
        // Never saturate: piece <= 255, the digit is at most 9.
        piece = piece.saturating_mul(10).saturating_add(at32(input, p).saturating_sub(0x30));
        if piece > 255 {
            return None;
        }
        p = p.saturating_add(1);
    }
    Some((piece, p))
}

/// IPv6 parser step 6.5.5, from `pointer` with numbersSeen 0.
fn ipv4_in_ipv6_exec(input: &[u32], address: Vec<u16>, piece_index: usize, pointer: usize) -> (r: Option<(Vec<u16>, usize, usize)>)
    requires
        address.len() == 8,
        piece_index <= 6,
        pointer <= input.len(),
        forall|k: int| piece_index <= k < 8 ==> address@[k] == 0,
    ensures
        match r {
            Some((a, p, n)) => ipv4_in_ipv6(input@, super::contract::pieces_view(address@), piece_index as int, 0, pointer as int) == Some(
                (super::contract::pieces_view(a@), p as int, n as nat),
            ) && a.len() == 8 && piece_index <= p <= 8,
            None => ipv4_in_ipv6(input@, super::contract::pieces_view(address@), piece_index as int, 0, pointer as int) is None,
        },
{
    let ghost a0 = address@;
    let ghost expected = ipv4_in_ipv6(input@, super::contract::pieces_view(a0), piece_index as int, 0, pointer as int);
    let mut a = address;
    let mut pi = piece_index;
    let mut numbers_seen: usize = 0;
    let mut p = pointer;
    loop
        invariant
            a.len() == 8,
            p <= input.len(),
            numbers_seen <= 4,
            pi == piece_index + numbers_seen / 2,
            piece_index <= 6,
            numbers_seen % 2 == 0 && pi < 8 ==> a@[pi as int] == 0,
            numbers_seen % 2 == 1 ==> a@[pi as int] <= 255,
            forall|k: int| pi < k < 8 ==> a@[k] == 0,
            a0 == address@,
            expected == ipv4_in_ipv6(input@, super::contract::pieces_view(a0), piece_index as int, 0, pointer as int),
            expected == ipv4_in_ipv6(input@, super::contract::pieces_view(a@), pi as int, numbers_seen as nat, p as int),
        decreases 4 - numbers_seen,
    {
        if p >= input.len() {
            return Some((a, pi, numbers_seen));
        }
        let c = at32(input, p);
        if numbers_seen > 0 && !(c == 0x2E && numbers_seen < 4) {
            return None;
        }
        // Never saturates: p < input.len().
        let q = if numbers_seen > 0 {
            p.saturating_add(1)
        } else {
            p
        };
        if !(q < input.len() && 0x30 <= at32(input, q) && at32(input, q) <= 0x39) {
            return None;
        }
        let first = at32(input, q).saturating_sub(0x30);
        match ipv4_piece_digits_exec(input, q.saturating_add(1), first) {
            None => {
                return None;
            },
            Some((piece, next)) => {
                let current = at16(a.as_slice(), pi);
                // Never saturate: current <= 255 and piece <= 255.
                let value = (current as u32).saturating_mul(0x100).saturating_add(piece);
                assert(value <= 0xFFFF);
                proof {
                    lemma_pieces_view_update(a@, pi as int, value as u16);
                }
                a = updated(&a, pi, value as u16);
                numbers_seen = numbers_seen.saturating_add(1);
                if numbers_seen == 2 || numbers_seen == 4 {
                    pi = pi.saturating_add(1);
                }
                p = next;
            },
        }
    }
}

/// IPv6 parser step 6, the main loop.
fn main_loop(input: &[u32], address: Vec<u16>, piece_index: usize, compress: Option<usize>, pointer: usize) -> (r: Option<(Vec<u16>, usize, Option<usize>)>)
    requires
        address.len() == 8,
        piece_index <= 8,
        pointer <= input.len(),
        compress matches Some(c) ==> 1 <= c <= piece_index,
        forall|k: int| piece_index <= k < 8 ==> address@[k] == 0,
    ensures
        main_view(r) == ipv6_main_loop(input@, super::contract::pieces_view(address@), piece_index as int, super::record::opt_int(compress), pointer as int),
        r matches Some((a, p, c)) ==> a.len() == 8 && p <= 8 && (c matches Some(c) ==> 1 <= c <= p),
{
    let ghost a0 = address@;
    let ghost c0 = super::record::opt_int(compress);
    let ghost expected = ipv6_main_loop(input@, super::contract::pieces_view(a0), piece_index as int, c0, pointer as int);
    let mut a = address;
    let mut pi = piece_index;
    let mut comp = compress;
    let mut p = pointer;
    loop
        invariant
            a.len() == 8,
            pi <= 8,
            p <= input.len(),
            comp matches Some(c) ==> 1 <= c <= pi,
            forall|k: int| pi <= k < 8 ==> a@[k] == 0,
            a0 == address@,
            c0 == super::record::opt_int(compress),
            expected == ipv6_main_loop(input@, super::contract::pieces_view(a0), piece_index as int, c0, pointer as int),
            expected == ipv6_main_loop(input@, super::contract::pieces_view(a@), pi as int, super::record::opt_int(comp), p as int),
        decreases input.len() - p,
    {
        if p >= input.len() {
            return Some((a, pi, comp));
        }
        let c = at32(input, p);
        if pi == 8 {
            return None;
        }
        if c == 0x3A {
            if comp.is_some() {
                return None;
            }
            pi = pi.saturating_add(1);
            comp = Some(pi);
            p = p.saturating_add(1);
        } else {
            let (value, length) = hex_digits(input, p);
            // Never saturates: p + length <= input.len().
            let after = p.saturating_add(length);
            if after < input.len() && at32(input, after) == 0x2E {
                if length == 0 {
                    return None;
                }
                if pi > 6 {
                    return None;
                }
                match ipv4_in_ipv6_exec(input, a, pi, p) {
                    None => {
                        return None;
                    },
                    Some((a2, pi2, numbers_seen)) => {
                        if numbers_seen != 4 {
                            return None;
                        }
                        return Some((a2, pi2, comp));
                    },
                }
            } else if after < input.len() && at32(input, after) == 0x3A {
                if after.saturating_add(1) >= input.len() {
                    return None;
                }
                proof {
                    lemma_pieces_view_update(a@, pi as int, value as u16);
                }
                a = updated(&a, pi, value as u16);
                pi = pi.saturating_add(1);
                p = after.saturating_add(1);
            } else if after < input.len() {
                return None;
            } else {
                proof {
                    lemma_pieces_view_update(a@, pi as int, value as u16);
                }
                let a2 = updated(&a, pi, value as u16);
                return Some((a2, pi.saturating_add(1), comp));
            }
        }
    }
}

/// IPv6 parser step 7.3, from pieceIndex 7.
fn swaps_exec(address: Vec<u16>, compress: usize, swaps: usize) -> (out: Vec<u16>)
    requires
        address.len() == 8,
        compress + swaps <= 8,
    ensures
        super::contract::pieces_view(out@) == ipv6_swaps(super::contract::pieces_view(address@), 7, compress as int, swaps as int),
        out.len() == 8,
{
    let ghost a0 = address@;
    let ghost expected = ipv6_swaps(super::contract::pieces_view(a0), 7, compress as int, swaps as int);
    let mut a = address;
    let mut pi: usize = 7;
    let mut s = swaps;
    while pi != 0 && s > 0
        invariant
            a.len() == 8,
            pi <= 7,
            compress + s <= pi + 1,
            a0 == address@,
            expected == ipv6_swaps(super::contract::pieces_view(a0), 7, compress as int, swaps as int),
            expected == ipv6_swaps(super::contract::pieces_view(a@), pi as int, compress as int, s as int),
        decreases s,
    {
        // Never saturate: s > 0 and compress + s <= pi + 1 <= 8.
        let other = compress.saturating_add(s).saturating_sub(1);
        let x = at16(a.as_slice(), pi);
        let y = at16(a.as_slice(), other);
        proof {
            lemma_pieces_view_update(a@, pi as int, y);
            lemma_pieces_view_update(a@.update(pi as int, y), other as int, x);
        }
        let b = updated(&a, pi, y);
        a = updated(&b, other, x);
        pi = pi.saturating_sub(1);
        s = s.saturating_sub(1);
    }
    a
}

/// An eight-element vector as an array.
fn to_array(v: &Vec<u16>) -> (out: [u16; 8])
    requires
        v.len() == 8,
    ensures
        out@ == v@,
{
    let s = v.as_slice();
    let out = [at16(s, 0), at16(s, 1), at16(s, 2), at16(s, 3), at16(s, 4), at16(s, 5), at16(s, 6), at16(s, 7)];
    assert(out@ =~= v@);
    out
}

/// The IPv6 parser (URL §3.5).
pub fn ipv6_parser(input: &[u32]) -> (output: Option<[u16; 8]>)
    ensures
        super::contract::ipv6_parser_ensures(
            input@,
            match output {
                Some(a) => Some(a@),
                None => None,
            },
        ),
{
    let mut address: Vec<u16> = Vec::new();
    let mut k: usize = 0;
    while k < 8
        invariant
            k <= 8,
            address@ == Seq::new(k as nat, |_i: int| 0u16),
        decreases 8 - k,
    {
        address.push(0);
        k = k.saturating_add(1);
        assert(address@ =~= Seq::new(k as nat, |_i: int| 0u16));
    }
    assert(super::contract::pieces_view(address@) =~= seq![0nat, 0, 0, 0, 0, 0, 0, 0]);
    let looped = if !input.is_empty() && at32(input, 0) == 0x3A {
        if !(input.len() > 1 && at32(input, 1) == 0x3A) {
            return None;
        }
        main_loop(input, address, 1, Some(1), 2)
    } else {
        main_loop(input, address, 0, None, 0)
    };
    match looped {
        None => None,
        Some((a, pi, compress)) => match compress {
            Some(c) => {
                // Never saturates: c <= pi.
                let out = swaps_exec(a, c, pi.saturating_sub(c));
                Some(to_array(&out))
            },
            None => if pi != 8 {
                None
            } else {
                Some(to_array(&a))
            },
        },
    }
}

} // verus!
