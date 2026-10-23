//! The executable resolv.conf parser, proven to meet
//! [`super::contract`]. It follows [`super::spec`] function by function.

use crate::spec::Addr;
#[allow(unused_imports)]
use vstd::prelude::*;
use vstd::slice::slice_subrange;

verus! {

/// White space: space, horizontal tab, carriage return.
fn is_ws(c: u8) -> (r: bool)
    ensures
        r == crate::resolv::spec::is_ws(c),
{
    c == 32 || c == 9 || c == 13
}

/// The first index at or after `i` that is not white space.
fn skip_ws(s: &[u8], i: usize) -> (r: usize)
    requires
        i <= s.len(),
    ensures
        r as nat == crate::resolv::spec::skip_ws(s@, i as nat),
        i <= r <= s.len(),
{
    let mut j: usize = i;
    while j < s.len()
        invariant
            i <= j <= s.len(),
            crate::resolv::spec::skip_ws(s@, i as nat) == crate::resolv::spec::skip_ws(s@, j as nat),
        decreases s.len() - j,
    {
        match s.get(j) {
            Some(&c) => {
                if !is_ws(c) {
                    return j;
                }
            },
            None => return j,
        }
        // j < s.len(), so this does not saturate.
        j = j.saturating_add(1);
    }
    j
}

/// The end of the token that starts at `i`.
fn token_end(s: &[u8], i: usize) -> (r: usize)
    requires
        i <= s.len(),
    ensures
        r as nat == crate::resolv::spec::token_end(s@, i as nat),
        i <= r <= s.len(),
{
    let mut j: usize = i;
    while j < s.len()
        invariant
            i <= j <= s.len(),
            crate::resolv::spec::token_end(s@, i as nat) == crate::resolv::spec::token_end(s@, j as nat),
        decreases s.len() - j,
    {
        match s.get(j) {
            Some(&c) => {
                if is_ws(c) {
                    return j;
                }
            },
            None => return j,
        }
        // j < s.len(), so this does not saturate.
        j = j.saturating_add(1);
    }
    j
}

/// The first index at or after `i` that is a `.`, or the end of `s`.
fn dot_at(s: &[u8], i: usize) -> (r: usize)
    requires
        i <= s.len(),
    ensures
        r as nat == crate::resolv::spec::dot_at(s@, i as nat),
        i <= r <= s.len(),
{
    let mut j: usize = i;
    while j < s.len()
        invariant
            i <= j <= s.len(),
            crate::resolv::spec::dot_at(s@, i as nat) == crate::resolv::spec::dot_at(s@, j as nat),
        decreases s.len() - j,
    {
        match s.get(j) {
            Some(&c) => {
                if c == 46 {
                    return j;
                }
            },
            None => return j,
        }
        // j < s.len(), so this does not saturate.
        j = j.saturating_add(1);
    }
    j
}

/// The first line feed at or after `i`, or the end of `s`.
fn line_end(s: &[u8], i: usize) -> (r: usize)
    requires
        i <= s.len(),
    ensures
        r as nat == crate::resolv::spec::line_end(s@, i as nat),
        i <= r <= s.len(),
{
    let mut j: usize = i;
    while j < s.len()
        invariant
            i <= j <= s.len(),
            crate::resolv::spec::line_end(s@, i as nat) == crate::resolv::spec::line_end(s@, j as nat),
        decreases s.len() - j,
    {
        match s.get(j) {
            Some(&c) => {
                if c == 10 {
                    return j;
                }
            },
            None => return j,
        }
        // j < s.len(), so this does not saturate.
        j = j.saturating_add(1);
    }
    j
}

/// One part of a dotted quad; see `crate::resolv::spec::ipv4_part`.
fn ipv4_part(s: &[u8]) -> (r: Option<u32>)
    ensures
        match r {
            Some(v) => crate::resolv::spec::ipv4_part(s@) == Some(v as nat),
            None => crate::resolv::spec::ipv4_part(s@) is None,
        },
{
    if s.is_empty() || s.len() > 3 {
        return None;
    }
    let mut j: usize = 0;
    let mut value: u32 = 0;
    while j < s.len()
        invariant
            j <= s.len(),
            s.len() <= 3,
            crate::resolv::spec::all_digits(s@.subrange(0, j as int)),
            value as nat == crate::resolv::spec::dec_value(s@.subrange(0, j as int)),
            j <= 0 ==> value <= 0,
            j <= 1 ==> value <= 9,
            j <= 2 ==> value <= 99,
            value <= 999,
        decreases s.len() - j,
    {
        let c = match s.get(j) {
            Some(&c) => c,
            None => return None,
        };
        if !(c > 47 && c < 58) {
            proof {
                // The prefix that ends with this octet is not all digits, so
                // neither is `s`.
                let k = j as int + 1;
                assert(s@.subrange(0, k).last() == c);
                assert(!crate::resolv::spec::all_digits(s@.subrange(0, k)));
                if crate::resolv::spec::all_digits(s@) {
                    super::lemmas::lemma_all_digits_prefix(s@, k);
                }
            }
            return None;
        }
        proof {
            let k = j as int + 1;
            assert(s@.subrange(0, k).drop_last() =~= s@.subrange(0, j as int));
            assert(s@.subrange(0, k).last() == c);
        }
        // value <= 999 and c is a digit: neither operation saturates.
        value = value.saturating_mul(10).saturating_add((c.saturating_sub(48)) as u32);
        j = j.saturating_add(1);
    }
    proof {
        assert(s@.subrange(0, s@.len() as int) =~= s@);
    }
    // No leading zero unless the part is a single digit.
    let first_is_zero = match s.first() {
        Some(&c) => c == 48,
        None => false,
    };
    if first_is_zero && s.len() > 1 {
        return None;
    }
    if value > 255 {
        return None;
    }
    Some(value)
}

/// An IPv4 address in strict dotted decimal; see `crate::resolv::spec::parse_ipv4`.
fn parse_ipv4(s: &[u8]) -> (r: Option<u32>)
    ensures
        match r {
            Some(v) => crate::resolv::spec::parse_ipv4(s@) == Some(v as nat),
            None => crate::resolv::spec::parse_ipv4(s@) is None,
        },
{
    let d1 = dot_at(s, 0);
    if d1 >= s.len() {
        return None;
    }
    // d1 < s.len(), so this does not saturate.
    let d2 = dot_at(s, d1.saturating_add(1));
    if d2 >= s.len() {
        return None;
    }
    let d3 = dot_at(s, d2.saturating_add(1));
    if d3 >= s.len() {
        return None;
    }
    if dot_at(s, d3.saturating_add(1)) < s.len() {
        return None;
    }
    let a = ipv4_part(slice_subrange(s, 0, d1))?;
    let b = ipv4_part(slice_subrange(s, d1.saturating_add(1), d2))?;
    let c = ipv4_part(slice_subrange(s, d2.saturating_add(1), d3))?;
    let d = ipv4_part(slice_subrange(s, d3.saturating_add(1), s.len()))?;
    // Each part is at most 255, so the value is at most 2^32 - 1.
    Some(
        a.saturating_mul(256).saturating_add(b).saturating_mul(256).saturating_add(c).saturating_mul(256).saturating_add(d),
    )
}

/// An IPv6 address by the URL Standard's IPv6 parser, as a number.
fn parse_ipv6(s: &[u8]) -> (r: Option<u128>)
    ensures
        match r {
            Some(v) => match clazel_url::host::spec::ipv6_parser(crate::resolv::spec::code_points(s@)) {
                Some(p) => crate::resolv::spec::pieces_value(p) == v as nat,
                None => false,
            },
            None => clazel_url::host::spec::ipv6_parser(crate::resolv::spec::code_points(s@)) is None,
        },
{
    let mut cps: Vec<u32> = Vec::new();
    let mut j: usize = 0;
    while j < s.len()
        invariant
            j <= s.len(),
            cps@ =~= crate::resolv::spec::code_points(s@.subrange(0, j as int)),
        decreases s.len() - j,
    {
        let c = match s.get(j) {
            Some(&c) => c,
            None => return None,
        };
        cps.push(c as u32);
        j = j.saturating_add(1);
        proof {
            assert(cps@ =~= crate::resolv::spec::code_points(s@.subrange(0, j as int)));
        }
    }
    proof {
        assert(s@.subrange(0, s@.len() as int) =~= s@);
    }
    let pieces = clazel_url::host::ipv6::ipv6_parser(cps.as_slice())?;
    let p = pieces.as_slice();
    let mut k: usize = 0;
    let mut acc: u128 = 0;
    let ghost view = clazel_url::host::contract::pieces_view(p@);
    while k < 8
        invariant
            k <= 8,
            p@.len() == 8,
            view == clazel_url::host::contract::pieces_view(p@),
            view.len() == 8,
            acc as nat == crate::resolv::spec::pieces_value(view.subrange(0, k as int)),
        decreases 8 - k,
    {
        let piece = match p.get(k) {
            Some(&x) => x,
            None => return None,
        };
        proof {
            let sub = view.subrange(0, k as int + 1);
            assert(sub.drop_last() =~= view.subrange(0, k as int));
            assert(sub.last() == piece as nat);
            let init = view.subrange(0, k as int);
            assert forall|i: int| 0 <= i < init.len() implies #[trigger] init[i] < 65536 by {
                assert(init[i] == view[i]);
                assert(view[i] == p@[i] as nat);
            }
            super::lemmas::lemma_pieces_value_bound(init);
            super::lemmas::lemma_pow65536_up_to_8(k as nat + 1);
            assert(super::lemmas::pow65536(k as nat + 1) == 65536 * super::lemmas::pow65536(k as nat));
            assert(acc as nat * 65536 + 65535 <= 0xFFFF_FFFF_FFFF_FFFF_FFFF_FFFF_FFFF_FFFF);
        }
        // acc * 65536 + piece <= 2^128 - 1 (shown above): neither saturates.
        acc = acc.saturating_mul(65536).saturating_add(piece as u128);
        k = k.saturating_add(1);
    }
    proof {
        assert(view.subrange(0, 8) =~= view);
    }
    Some(acc)
}

/// An address literal; see `crate::resolv::spec::parse_address`.
fn parse_address(s: &[u8]) -> (r: Option<Addr>)
    ensures
        r == crate::resolv::spec::parse_address(s@),
{
    if let Some(a) = parse_ipv4(s) {
        return Some(Addr::V4(a));
    }
    let a = parse_ipv6(s)?;
    Some(Addr::V6(a))
}

/// Whether `tok` is the keyword `nameserver`.
fn is_keyword(tok: &[u8]) -> (r: bool)
    ensures
        r == (tok@ == crate::resolv::spec::keyword()),
{
    if tok.len() != 10 {
        return false;
    }
    let ok = byte_is(tok, 0, 110) && byte_is(tok, 1, 97) && byte_is(tok, 2, 109) && byte_is(tok, 3, 101) && byte_is(
        tok,
        4,
        115,
    ) && byte_is(tok, 5, 101) && byte_is(tok, 6, 114) && byte_is(tok, 7, 118) && byte_is(tok, 8, 101) && byte_is(
        tok,
        9,
        114,
    );
    proof {
        if ok {
            assert(tok@ =~= crate::resolv::spec::keyword());
        }
    }
    ok
}

/// Whether octet `i` of `s` is `v`.
fn byte_is(s: &[u8], i: usize, v: u8) -> (r: bool)
    ensures
        r == (i < s@.len() && s@[i as int] == v),
{
    match s.get(i) {
        Some(&c) => c == v,
        None => false,
    }
}

/// The address of one line, if it is a `nameserver` line with one; see
/// `crate::resolv::spec::parse_line`.
fn parse_line(line: &[u8]) -> (r: Option<Addr>)
    ensures
        r == crate::resolv::spec::parse_line(line@),
{
    let a = skip_ws(line, 0);
    let b = token_end(line, a);
    if !is_keyword(slice_subrange(line, a, b)) {
        return None;
    }
    let c = skip_ws(line, b);
    let d = token_end(line, c);
    if d == c {
        return None;
    }
    parse_address(slice_subrange(line, c, d))
}

/// The addresses of the `nameserver` lines of a resolv.conf, in file
/// order; see `crate::resolv::spec::nameservers`.
pub fn nameservers(input: &[u8]) -> (output: Vec<Addr>)
    ensures
        super::contract::nameservers_ensures(input@, output@),
{
    let mut out: Vec<Addr> = Vec::new();
    let mut pos: usize = 0;
    while pos < input.len()
        invariant
            pos <= input.len(),
            crate::resolv::spec::parse_lines(input@, pos as nat, out@) == crate::resolv::spec::nameservers(input@),
        decreases input.len() - pos,
    {
        let e = line_end(input, pos);
        if let Some(a) = parse_line(slice_subrange(input, pos, e)) {
            out.push(a);
        }
        // After the line feed, or at the end if the last line has none.
        pos = if e < input.len() {
            e.saturating_add(1)
        } else {
            input.len()
        };
    }
    out
}

} // verus!
