//! Executable-style specification of the `nameserver` lines of
//! `/etc/resolv.conf`, which the network shell (phase-3.md item 3.8) reads
//! to find the resolver.
//!
//! No standard defines this file: resolv.conf(5) is documented by each C
//! library, and they differ. The grammar here is ours, and is the only
//! thing in `clazel-dns` that does not transcribe an RFC. It is small on
//! purpose: a line the grammar does not understand is ignored, so the shell
//! uses only addresses that were written in the simplest accepted form.
//!
//! ## The grammar
//!
//! ```text
//! file       = *( line LF ) [ line ]
//! line       = *WS "nameserver" 1*WS address *( WS / other )   ; used
//!            / any other octets                                ; ignored
//! WS         = SP / HTAB / CR
//! address    = ipv4 / ipv6
//! ```
//!
//! A line is the octets up to a line feed. Its octets are split into tokens
//! separated by runs of white space (space, tab and carriage return, so a
//! line ending CR LF is read like one ending LF). The line gives an address
//! if and only if its first token is exactly `nameserver` (lower case) and
//! its second token is an address literal; every later token is ignored (a
//! trailing comment, for example). Any other line gives nothing: a comment,
//! a different keyword, a `nameserver` line with no address or with a token
//! that is not an address.
//!
//! ## Modelling choices
//!
//! - **IPv4 is strict dotted decimal**: four parts separated by `.`, each of
//!   one to three decimal digits, no leading zero unless the part is `0`,
//!   each at most 255. The URL Standard's IPv4 parser (`clazel-url`) is not
//!   used for it because it accepts forms (`1`, `0x7f.1`, `010.1.1.1`,
//!   `1.2.3.4.`) that mean different things to different C libraries; here
//!   the line is ignored instead.
//! - **IPv6 is the URL Standard's IPv6 parser** (URL §3.5 "IPv6 parser"),
//!   applied to the token without brackets, and proven in `clazel-url`.
//!   A zone identifier (`fe80::1%eth0`) is not part of that grammar, so a
//!   line with one is ignored.
//! - **Every line is considered**, in file order, with no limit on the
//!   number of addresses returned (the shell chooses how many to use).
//! - **Addresses are numbers**, as in `spec.rs`: an IPv4 address is the
//!   `u32` of its four octets, an IPv6 address the `u128` its eight 16-bit
//!   pieces spell.

use super::super::spec::Addr;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// White space: space, horizontal tab, carriage return.
pub open spec fn is_ws(c: u8) -> bool {
    c == 32 || c == 9 || c == 13
}

/// The first index at or after `i` that is not white space.
pub open spec fn skip_ws(s: Seq<u8>, i: nat) -> nat
    decreases s.len() - i
{
    if i < s.len() && is_ws(s[i as int]) {
        skip_ws(s, i + 1)
    } else {
        i
    }
}

/// The end of the token that starts at `i`: the first white space at or
/// after `i`, or the end of `s`.
pub open spec fn token_end(s: Seq<u8>, i: nat) -> nat
    decreases s.len() - i
{
    if i < s.len() && !is_ws(s[i as int]) {
        token_end(s, i + 1)
    } else {
        i
    }
}

/// The keyword of a nameserver line.
pub open spec fn keyword() -> Seq<u8> {
    seq![110u8, 97, 109, 101, 115, 101, 114, 118, 101, 114]  // "nameserver"
}

/// The first index at or after `i` that is a `.`, or the end of `s`.
pub open spec fn dot_at(s: Seq<u8>, i: nat) -> nat
    decreases s.len() - i
{
    if i < s.len() && s[i as int] != 46 {
        dot_at(s, i + 1)
    } else {
        i
    }
}

/// `s` holds decimal digits only.
pub open spec fn all_digits(s: Seq<u8>) -> bool
    decreases s.len()
{
    if s.len() == 0 {
        true
    } else {
        48 <= s.last() && s.last() <= 57 && all_digits(s.drop_last())
    }
}

/// The number the decimal digits of `s` spell.
pub open spec fn dec_value(s: Seq<u8>) -> nat
    decreases s.len()
{
    if s.len() == 0 {
        0
    } else {
        dec_value(s.drop_last()) * 10 + (s.last() - 48) as nat
    }
}

/// One part of a dotted quad: one to three digits, no leading zero unless
/// the part is a single `0`, at most 255.
pub open spec fn ipv4_part(s: Seq<u8>) -> Option<nat> {
    if 1 <= s.len() && s.len() <= 3 && all_digits(s) && !(s.len() > 1 && s[0] == 48) && dec_value(s) <= 255 {
        Some(dec_value(s))
    } else {
        None
    }
}

/// An IPv4 address in dotted decimal: four parts, three dots.
pub open spec fn parse_ipv4(s: Seq<u8>) -> Option<nat> {
    let d1 = dot_at(s, 0);
    let d2 = dot_at(s, d1 + 1);
    let d3 = dot_at(s, d2 + 1);
    if d1 >= s.len() || d2 >= s.len() || d3 >= s.len() || dot_at(s, d3 + 1) < s.len() {
        // Fewer than three dots, or more.
        None
    } else {
        match (
            ipv4_part(s.subrange(0, d1 as int)),
            ipv4_part(s.subrange(d1 as int + 1, d2 as int)),
            ipv4_part(s.subrange(d2 as int + 1, d3 as int)),
            ipv4_part(s.subrange(d3 as int + 1, s.len() as int)),
        ) {
            (Some(a), Some(b), Some(c), Some(d)) => Some(((a * 256 + b) * 256 + c) * 256 + d),
            _ => None,
        }
    }
}

/// The number that eight 16-bit pieces spell, first piece most significant.
pub open spec fn pieces_value(p: Seq<nat>) -> nat
    decreases p.len()
{
    if p.len() == 0 {
        0
    } else {
        pieces_value(p.drop_last()) * 65536 + p.last()
    }
}

/// The octets as code points (the URL parser's input type).
pub open spec fn code_points(s: Seq<u8>) -> Seq<u32> {
    s.map_values(|c: u8| c as u32)
}

/// An address literal: IPv4 in strict dotted decimal, else IPv6 by the URL
/// Standard's IPv6 parser.
pub open spec fn parse_address(s: Seq<u8>) -> Option<Addr> {
    match parse_ipv4(s) {
        Some(a) => Some(Addr::V4(a as u32)),
        None => match clazel_url::host::spec::ipv6_parser(code_points(s)) {
            Some(p) => Some(Addr::V6(pieces_value(p) as u128)),
            None => None,
        },
    }
}

/// The address of one line (without its line feed), if it is a
/// `nameserver` line with an address.
pub open spec fn parse_line(line: Seq<u8>) -> Option<Addr> {
    let a = skip_ws(line, 0);
    let b = token_end(line, a);
    if line.subrange(a as int, b as int) != keyword() {
        // Not a nameserver line.
        None
    } else {
        let c = skip_ws(line, b);
        let d = token_end(line, c);
        if d == c {
            // `nameserver` with nothing after it.
            None
        } else {
            parse_address(line.subrange(c as int, d as int))
        }
    }
}

/// The first line feed at or after `i`, or the end of `s`.
pub open spec fn line_end(s: Seq<u8>, i: nat) -> nat
    decreases s.len() - i
{
    if i < s.len() && s[i as int] != 10 {
        line_end(s, i + 1)
    } else {
        i
    }
}

/// The addresses of the lines of `s` from `pos`, appended to `acc`.
pub open spec fn parse_lines(s: Seq<u8>, pos: nat, acc: Seq<Addr>) -> Seq<Addr>
    decreases s.len() - pos via parse_lines_decreases
{
    if pos >= s.len() {
        acc
    } else {
        let e = line_end(s, pos);
        // After the line feed, or at the end if the last line has none.
        let next = if e < s.len() {
            e + 1
        } else {
            s.len()
        };
        parse_lines(s, next, match parse_line(s.subrange(pos as int, e as int)) {
            Some(a) => acc.push(a),
            None => acc,
        })
    }
}

/// Termination of [`parse_lines`] (see `termination.rs`).
#[via_fn]
pub proof fn parse_lines_decreases(s: Seq<u8>, pos: nat, acc: Seq<Addr>) {
    super::termination::lemma_line_end_progress(s, pos);
}

/// The addresses of the `nameserver` lines of a resolv.conf, in order.
pub open spec fn nameservers(file: Seq<u8>) -> Seq<Addr> {
    parse_lines(file, 0, seq![])
}

} // verus!
