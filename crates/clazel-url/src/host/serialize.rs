//! The executable host serializers (URL §3.6), proven to meet
//! [`super::contract`]. Each loop mirrors its spec function; the step
//! comments live in [`super::spec`].

use super::record::ParsedHost;
#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Appends `n`, serialized (URL §1 "serialize an integer"), to `out`.
pub fn push_decimal(n: u32, out: &mut Vec<u32>)
    ensures
        final(out)@ == old(out)@ + serialize_integer(n as nat),
    decreases n,
{
    let ghost start = out@;
    if n < 10 {
        // Never saturates: n < 10.
        out.push(n.saturating_add(0x30));
        assert(out@ =~= start + serialize_integer(n as nat));
    } else {
        push_decimal(n / 10, out);
        // Never saturates: n % 10 < 10.
        out.push((n % 10).saturating_add(0x30));
        assert(out@ =~= start + serialize_integer(n as nat));
    }
}

/// Appends `n` as the shortest possible lowercase hexadecimal number to
/// `out`.
fn push_lowercase_hex(n: u16, out: &mut Vec<u32>)
    ensures
        final(out)@ == old(out)@ + shortest_lowercase_hex(n as nat),
    decreases n,
{
    let ghost start = out@;
    let low = n % 16;
    // Never saturates: low < 16.
    let digit = if low < 10 {
        (low as u32).saturating_add(0x30)
    } else {
        (low as u32).saturating_add(0x57)
    };
    if n < 16 {
        out.push(digit);
        assert(out@ =~= start + shortest_lowercase_hex(n as nat));
    } else {
        push_lowercase_hex(n / 16, out);
        out.push(digit);
        assert(out@ =~= start + shortest_lowercase_hex(n as nat));
    }
}

/// The IPv4 serializer (URL §3.6).
pub fn ipv4_serializer(address: u32) -> (output: Vec<u32>)
    ensures
        super::contract::ipv4_serializer_ensures(address, output@),
{
    let mut output: Vec<u32> = Vec::new();
    let mut n: u32 = address;
    let mut i: u32 = 1;
    assert(output@ =~= seq![]);
    while i <= 4
        invariant
            1 <= i <= 5,
            super::spec::ipv4_serializer(address as nat) == ipv4_serializer_loop(output@, n as nat, i as nat),
        decreases 5 - i,
    {
        let ghost before = output@;
        let mut next: Vec<u32> = Vec::new();
        if i != 4 {
            next.push(0x2E);
        }
        let ghost dot = next@;
        push_decimal(n % 256, &mut next);
        super::record::append(&mut next, output.as_slice());
        assert(next@ =~= if i != 4 {
            seq![0x2Eu32] + (serialize_integer((n % 256) as nat) + before)
        } else {
            serialize_integer((n % 256) as nat) + before
        });
        output = next;
        n /= 256;
        // Never saturates: i <= 4.
        i = i.saturating_add(1);
    }
    output
}

/// "Find the IPv6 address compressed piece index" (URL §3.6).
fn find_compressed_piece_index(address: &[u16; 8]) -> (r: Option<usize>)
    ensures
        match (r, find_ipv6_compressed_piece_index(super::contract::pieces_view(address@))) {
            (Some(i), Some(j)) => i as int == j,
            (None, None) => true,
            _ => false,
        },
{
    let ghost a = super::contract::pieces_view(address@);
    let mut longest_index: Option<usize> = None;
    let mut longest_size: usize = 1;
    let mut found_index: Option<usize> = None;
    let mut found_size: usize = 0;
    let mut piece_index: usize = 0;
    while piece_index < 8
        invariant
            piece_index <= 8,
            a.len() == 8,
            a == super::contract::pieces_view(address@),
            longest_size <= piece_index + 1,
            found_size <= piece_index,
            find_ipv6_compressed_piece_index(a) == find_compressed_loop(
                a,
                piece_index as nat,
                super::record::opt_int(longest_index),
                longest_size as nat,
                super::record::opt_int(found_index),
                found_size as nat,
            ),
        decreases 8 - piece_index,
    {
        let piece = super::record::at16(address.as_slice(), piece_index);
        if piece != 0 {
            if found_size > longest_size {
                longest_index = found_index;
                longest_size = found_size;
            }
            found_index = None;
            found_size = 0;
        } else {
            if found_index.is_none() {
                found_index = Some(piece_index);
            }
            // Never saturates: found_size <= piece_index < 8.
            found_size = found_size.saturating_add(1);
        }
        piece_index = piece_index.saturating_add(1);
    }
    if found_size > longest_size {
        found_index
    } else {
        longest_index
    }
}

/// The IPv6 serializer (URL §3.6).
pub fn ipv6_serializer(address: &[u16; 8]) -> (output: Vec<u32>)
    ensures
        super::contract::ipv6_serializer_ensures(address@, output@),
{
    let ghost a = super::contract::pieces_view(address@);
    let compress = find_compressed_piece_index(address);
    let ghost compress_view = super::record::opt_int(compress);
    assert(compress_view == find_ipv6_compressed_piece_index(a));
    let mut output: Vec<u32> = Vec::new();
    let mut ignore0 = false;
    let mut piece_index: usize = 0;
    while piece_index < 8
        invariant
            piece_index <= 8,
            a.len() == 8,
            a == super::contract::pieces_view(address@),
            compress_view == super::record::opt_int(compress),
            super::spec::ipv6_serializer(a) == ipv6_serializer_loop(a, compress_view, ignore0, piece_index as nat, output@),
        decreases 8 - piece_index,
    {
        let ghost before = output@;
        let piece = super::record::at16(address.as_slice(), piece_index);
        assert(a[piece_index as int] == piece as nat);
        let is_compress = match compress {
            Some(c) => c == piece_index,
            None => false,
        };
        if ignore0 && piece == 0 {
        } else if is_compress {
            if piece_index == 0 {
                output.push(0x3A);
            }
            output.push(0x3A);
            assert(output@ =~= before + if piece_index == 0 {
                seq![0x3Au32, 0x3A]
            } else {
                seq![0x3Au32]
            });
            ignore0 = true;
        } else {
            push_lowercase_hex(piece, &mut output);
            let ghost hex = output@;
            if piece_index != 7 {
                output.push(0x3A);
            }
            assert(output@ =~= if piece_index != 7 {
                hex + seq![0x3Au32]
            } else {
                hex
            });
            ignore0 = false;
        }
        piece_index = piece_index.saturating_add(1);
    }
    output
}

impl ParsedHost {
    /// The host serializer (URL §3.6).
    pub fn serialize(&self) -> (output: Vec<u32>)
        ensures
            super::contract::host_serializer_ensures(self@, output@),
    {
        match self {
            ParsedHost::Ipv4(address) => ipv4_serializer(*address),
            ParsedHost::Ipv6(address) => {
                let mut output: Vec<u32> = Vec::new();
                output.push(0x5B);
                let inner = ipv6_serializer(address);
                super::record::append(&mut output, inner.as_slice());
                output.push(0x5D);
                assert(output@ =~= seq![0x5Bu32] + inner@ + seq![0x5Du32]);
                output
            },
            ParsedHost::Domain(s) => super::record::copy(s.as_slice()),
            ParsedHost::Opaque(s) => super::record::copy(s.as_slice()),
            ParsedHost::Empty => {
                let output: Vec<u32> = Vec::new();
                assert(output@ =~= seq![]);
                output
            },
        }
    }
}

} // verus!
