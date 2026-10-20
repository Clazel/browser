//! A second transcription of the text forms of IP addresses, from the IETF
//! standards instead of the URL Standard:
//!
//! - RFC 3986 §3.2.2 (January 2005), the `IP-literal`, `IPvFuture`,
//!   `IPv6address`, `h16`, `ls32`, `IPv4address` and `dec-octet` rules,
//!   with the RFC 5234 Appendix B.1 core rules `DIGIT`, `HEXDIG` and
//!   `ALPHA`;
//! - RFC 4291 §2.2 (February 2006), for what an IPv6 text form *means*:
//!   the value of each piece, what "::" stands for, and the IPv4 tail;
//! - RFC 5952 §4 (August 2010), the recommended (canonical) IPv6 text
//!   form.
//!
//! These definitions were written from the RFCs alone, before
//! `spec.rs` (the URL Standard transcription) existed, and committed
//! first. The theorems relating them to `spec.rs` are added later, at the
//! end of this file.
//!
//! Modelling choices (each a deviation in form, not in meaning):
//! - A string is a `Seq<u32>` of code points. An address is a `nat` (IPv4)
//!   or a `Seq<nat>` of eight 16-bit pieces, most significant first
//!   (IPv6), so that the values can be compared with `spec.rs` directly.
//! - Each ABNF rule that matches a whole string is a function returning
//!   `None` (no match) or `Some` of the value the text denotes. Rules are
//!   matched against a whole string, never a prefix.
//! - ABNF quoted strings and `HEXDIG` are case-insensitive (RFC 5234
//!   §2.3), so `HEXDIG` includes "a" to "f", and the version flag "v"
//!   includes "V".
//! - Where a rule is a concatenation, the split points are found by
//!   searching for the separator (`find`): each part that a separator
//!   follows (`dec-octet`, `h16`) cannot itself contain that separator, so
//!   the first occurrence is the only possible split. In `IPv6address`,
//!   every alternative but the first contains "::" exactly once, preceded
//!   by nothing or by text ending in a `HEXDIG` (`[ *N( h16 ":" ) h16 ]`)
//!   that contains no "::"; so the first "::" in the string is the one the
//!   grammar means, and a string without "::" can only match the first
//!   alternative.
//! - In `ls32 = ( h16 ":" h16 ) / IPv4address`, the first alternative
//!   contains ":" and the second does not, so the presence of ":" chooses.
//! - The alternatives of `IPv6address` are numbered 1 to 9 in the order the
//!   RFC lists them; alternatives 2 to 9 are tried in that order
//!   ([`compressed_from`]). At most one can match a given string, because
//!   their right-hand sides take different numbers of ":"-separated parts.
//! - RFC 4291 §2.2 item 2: "::" stands for "one or more groups of 16 bits
//!   of zeros", as many as make eight pieces in all. Item 3: an IPv4 tail
//!   gives the two least significant pieces, "the decimal values of the
//!   four low-order 8-bit pieces of the address". An IPv4 address's value
//!   is its four octets, most significant first (RFC 791 §3.2 orders an
//!   address's octets the same way).
//! - RFC 5952 §5 (mixed notation for addresses with an embedded IPv4
//!   address) is a recommendation that depends on knowing the address's
//!   prefix; it is not transcribed. [`rfc5952_text`] is §4 alone.

#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------
// RFC 5234 Appendix B.1 core rules.
// ---------------------------------------------------------------------

/// `DIGIT = %x30-39 ; 0-9`
pub open spec fn is_digit(c: u32) -> bool {
    0x30 <= c <= 0x39
}

/// `HEXDIG = DIGIT / "A" / "B" / "C" / "D" / "E" / "F"`, matched
/// case-insensitively (RFC 5234 §2.3).
pub open spec fn is_hexdig(c: u32) -> bool {
    is_digit(c) || (0x41 <= c <= 0x46) || (0x61 <= c <= 0x66)
}

/// `ALPHA = %x41-5A / %x61-7A ; A-Z / a-z`
pub open spec fn is_alpha(c: u32) -> bool {
    (0x41 <= c <= 0x5A) || (0x61 <= c <= 0x7A)
}

/// The value of a `DIGIT`.
pub open spec fn digit_value(c: u32) -> nat {
    (c - 0x30) as nat
}

/// The value of a `HEXDIG` (A and a are 10, ..., F and f are 15).
pub open spec fn hexdig_value(c: u32) -> nat {
    if is_digit(c) {
        (c - 0x30) as nat
    } else if 0x41 <= c <= 0x46 {
        (c - 0x41 + 10) as nat
    } else {
        (c - 0x61 + 10) as nat
    }
}

// ---------------------------------------------------------------------
// Helpers for matching whole strings.
// ---------------------------------------------------------------------

/// The index of the first `c` in `s` at or after `from`, or `s.len()` if
/// there is none.
pub open spec fn find(s: Seq<u32>, c: u32, from: nat) -> nat
    decreases s.len() - from
{
    if from >= s.len() {
        s.len()
    } else if s[from as int] == c {
        from
    } else {
        find(s, c, from + 1)
    }
}

/// The index of the first "::" in `s` at or after `from`, or `s.len()` if
/// there is none.
pub open spec fn find_double_colon(s: Seq<u32>, from: nat) -> nat
    decreases s.len() - from
{
    if from + 1 >= s.len() {
        s.len()
    } else if s[from as int] == 0x3A && s[from + 1int] == 0x3A {
        from
    } else {
        find_double_colon(s, from + 1)
    }
}

/// Every code point of `t` is a `HEXDIG`.
pub open spec fn all_hexdig(t: Seq<u32>) -> bool
    decreases t.len()
{
    t.len() == 0 || (is_hexdig(t.last()) && all_hexdig(t.drop_last()))
}

/// The number `t` denotes in hexadecimal, most significant digit first.
pub open spec fn hex_number(t: Seq<u32>) -> nat
    decreases t.len()
{
    if t.len() == 0 {
        0
    } else {
        hex_number(t.drop_last()) * 16 + hexdig_value(t.last())
    }
}

// ---------------------------------------------------------------------
// RFC 3986 §3.2.2: IPv4address.
// ---------------------------------------------------------------------

/// ```text
/// dec-octet   = DIGIT                 ; 0-9
///             / %x31-39 DIGIT         ; 10-99
///             / "1" 2DIGIT            ; 100-199
///             / "2" %x30-34 DIGIT     ; 200-249
///             / "25" %x30-35          ; 250-255
/// ```
/// `Some` of the octet's value if all of `t` matches.
pub open spec fn dec_octet(t: Seq<u32>) -> Option<nat> {
    if t.len() == 1 && is_digit(t[0]) {
        Some(digit_value(t[0]))
    } else if t.len() == 2 && (0x31 <= t[0] <= 0x39) && is_digit(t[1]) {
        Some(10 * digit_value(t[0]) + digit_value(t[1]))
    } else if t.len() == 3 && t[0] == 0x31 && is_digit(t[1]) && is_digit(t[2]) {
        Some(100 + 10 * digit_value(t[1]) + digit_value(t[2]))
    } else if t.len() == 3 && t[0] == 0x32 && (0x30 <= t[1] <= 0x34) && is_digit(t[2]) {
        Some(200 + 10 * digit_value(t[1]) + digit_value(t[2]))
    } else if t.len() == 3 && t[0] == 0x32 && t[1] == 0x35 && (0x30 <= t[2] <= 0x35) {
        Some(250 + digit_value(t[2]))
    } else {
        None
    }
}

/// `IPv4address = dec-octet "." dec-octet "." dec-octet "." dec-octet`:
/// `Some` of its four octets, in order, if all of `s` matches.
pub open spec fn ipv4address_octets(s: Seq<u32>) -> Option<Seq<nat>> {
    let d1 = find(s, 0x2E, 0);
    let d2 = find(s, 0x2E, d1 + 1);
    let d3 = find(s, 0x2E, d2 + 1);
    if d3 >= s.len() || find(s, 0x2E, d3 + 1) != s.len() {
        // Not exactly three ".".
        None
    } else {
        match (
            dec_octet(s.subrange(0, d1 as int)),
            dec_octet(s.subrange(d1 + 1int, d2 as int)),
            dec_octet(s.subrange(d2 + 1int, d3 as int)),
            dec_octet(s.subrange(d3 + 1int, s.len() as int)),
        ) {
            (Some(a), Some(b), Some(c), Some(d)) => Some(seq![a, b, c, d]),
            _ => None,
        }
    }
}

/// The 32-bit value of the address `s` denotes, if it matches
/// `IPv4address`: its octets, most significant first.
pub open spec fn ipv4address(s: Seq<u32>) -> Option<nat> {
    match ipv4address_octets(s) {
        Some(o) => Some(((o[0] * 256 + o[1]) * 256 + o[2]) * 256 + o[3]),
        None => None,
    }
}

// ---------------------------------------------------------------------
// RFC 3986 §3.2.2 and RFC 4291 §2.2: IPv6address.
// ---------------------------------------------------------------------

/// `h16 = 1*4HEXDIG ; 16 bits of address represented in hexadecimal`
/// ("using one to four hexadecimal digits (leading zeroes are
/// permitted)").
pub open spec fn h16(t: Seq<u32>) -> Option<nat> {
    if 1 <= t.len() <= 4 && all_hexdig(t) {
        Some(hex_number(t))
    } else {
        None
    }
}

/// `ls32 = ( h16 ":" h16 ) / IPv4address ; least-significant 32 bits of
/// address`: `Some` of the two pieces it denotes (RFC 4291 §2.2 item 3 for
/// the IPv4 form).
pub open spec fn ls32(t: Seq<u32>) -> Option<Seq<nat>> {
    let i = find(t, 0x3A, 0);
    if i < t.len() {
        match (h16(t.subrange(0, i as int)), h16(t.subrange(i + 1int, t.len() as int))) {
            (Some(a), Some(b)) => Some(seq![a, b]),
            _ => None,
        }
    } else {
        match ipv4address_octets(t) {
            Some(o) => Some(seq![o[0] * 256 + o[1], o[2] * 256 + o[3]]),
            None => None,
        }
    }
}

/// `j( h16 ":" ) ls32`: `Some` of the pieces, if all of `t` matches.
pub open spec fn h16_colons_ls32(t: Seq<u32>, j: nat) -> Option<Seq<nat>>
    decreases j
{
    if j == 0 {
        ls32(t)
    } else {
        let i = find(t, 0x3A, 0);
        if i >= t.len() {
            None
        } else {
            match h16(t.subrange(0, i as int)) {
                Some(v) => match h16_colons_ls32(t.subrange(i + 1int, t.len() as int), (j - 1) as nat) {
                    Some(rest) => Some(seq![v] + rest),
                    None => None,
                },
                None => None,
            }
        }
    }
}

/// `h16 *( ":" h16 )`, one or more `h16` separated by ":": `Some` of their
/// values, if all of `t` matches.
pub open spec fn h16_list(t: Seq<u32>) -> Option<Seq<nat>>
    decreases t.len()
{
    let i = find(t, 0x3A, 0);
    match h16(t.subrange(0, i as int)) {
        None => None,
        Some(v) => if i >= t.len() {
            Some(seq![v])
        } else {
            match h16_list(t.subrange(i + 1int, t.len() as int)) {
                Some(rest) => Some(seq![v] + rest),
                None => None,
            }
        },
    }
}

/// The optional part before "::" in alternatives 3 to 9,
/// `[ *m( h16 ":" ) h16 ]`, with at most `max` pieces (`max` is `m + 1`;
/// alternative 2 has no such part, which is `max` 0): `Some` of its
/// values.
pub open spec fn before_double_colon(t: Seq<u32>, max: nat) -> Option<Seq<nat>> {
    if t.len() == 0 {
        Some(seq![])
    } else {
        match h16_list(t) {
            Some(l) => if l.len() <= max {
                Some(l)
            } else {
                None
            },
            None => None,
        }
    }
}

/// The part after "::" in alternative `n` (2 to 9): `(7 - n)( h16 ":" )
/// ls32` for 2 to 7, `h16` for 8, and nothing for 9.
pub open spec fn after_double_colon(t: Seq<u32>, n: nat) -> Option<Seq<nat>> {
    if 2 <= n <= 7 {
        h16_colons_ls32(t, (7 - n) as nat)
    } else if n == 8 {
        match h16(t) {
            Some(v) => Some(seq![v]),
            None => None,
        }
    } else if n == 9 && t.len() == 0 {
        Some(seq![])
    } else {
        None
    }
}

/// `count` zero pieces.
pub open spec fn zeros(count: nat) -> Seq<nat> {
    Seq::new(count, |_i: int| 0nat)
}

/// Alternative `n` (2 to 9) of `IPv6address`, given the text before and
/// after its "::": `Some` of the eight pieces. The "::" stands for as many
/// zero pieces as make eight in all (RFC 4291 §2.2 item 2: "one or more
/// groups of 16 bits of zeros").
pub open spec fn compressed(n: nat, before: Seq<u32>, after: Seq<u32>) -> Option<Seq<nat>> {
    match (before_double_colon(before, (n - 2) as nat), after_double_colon(after, n)) {
        (Some(l), Some(r)) => Some(l + zeros((8 - l.len() - r.len()) as nat) + r),
        _ => None,
    }
}

/// Alternatives `n` to 9 of `IPv6address`, tried in order.
pub open spec fn compressed_from(n: nat, before: Seq<u32>, after: Seq<u32>) -> Option<Seq<nat>>
    decreases 10 - n
{
    if n > 9 {
        None
    } else {
        match compressed(n, before, after) {
            Some(a) => Some(a),
            None => compressed_from(n + 1, before, after),
        }
    }
}

/// ```text
/// IPv6address =                            6( h16 ":" ) ls32
///             /                       "::" 5( h16 ":" ) ls32
///             / [               h16 ] "::" 4( h16 ":" ) ls32
///             / [ *1( h16 ":" ) h16 ] "::" 3( h16 ":" ) ls32
///             / [ *2( h16 ":" ) h16 ] "::" 2( h16 ":" ) ls32
///             / [ *3( h16 ":" ) h16 ] "::"    h16 ":"   ls32
///             / [ *4( h16 ":" ) h16 ] "::"              ls32
///             / [ *5( h16 ":" ) h16 ] "::"              h16
///             / [ *6( h16 ":" ) h16 ] "::"
/// ```
/// `Some` of the address's eight pieces, if all of `s` matches.
pub open spec fn ipv6address(s: Seq<u32>) -> Option<Seq<nat>> {
    let k = find_double_colon(s, 0);
    if k >= s.len() {
        // Alternative 1.
        h16_colons_ls32(s, 6)
    } else {
        compressed_from(2, s.subrange(0, k as int), s.subrange(k + 2int, s.len() as int))
    }
}

/// `unreserved / sub-delims / ":"`, the code points after the "." of
/// `IPvFuture`: `unreserved = ALPHA / DIGIT / "-" / "." / "_" / "~"` and
/// `sub-delims = "!" / "$" / "&" / "'" / "(" / ")" / "*" / "+" / "," / ";"
/// / "="`.
pub open spec fn is_ipvfuture_tail_code_point(c: u32) -> bool {
    is_alpha(c) || is_digit(c) || c == 0x2D || c == 0x2E || c == 0x5F || c == 0x7E
        || c == 0x21 || c == 0x24 || c == 0x26 || c == 0x27 || c == 0x28 || c == 0x29
        || c == 0x2A || c == 0x2B || c == 0x2C || c == 0x3B || c == 0x3D || c == 0x3A
}

/// Every code point of `t` at or after `from` is in
/// [`is_ipvfuture_tail_code_point`].
pub open spec fn ipvfuture_tail_from(t: Seq<u32>, from: nat) -> bool
    decreases t.len() - from
{
    from >= t.len() || (is_ipvfuture_tail_code_point(t[from as int]) && ipvfuture_tail_from(t, from + 1))
}

/// Every code point of `t` from `from` up to `to` is a `HEXDIG`.
pub open spec fn hexdigs_between(t: Seq<u32>, from: nat, to: nat) -> bool
    decreases to - from
{
    from >= to || (from < t.len() && is_hexdig(t[from as int]) && hexdigs_between(t, from + 1, to))
}

/// `IPvFuture = "v" 1*HEXDIG "." 1*( unreserved / sub-delims / ":" )`,
/// matched against all of `t`.
pub open spec fn is_ipvfuture(t: Seq<u32>) -> bool {
    let dot = find(t, 0x2E, 1);
    t.len() >= 1 && (t[0] == 0x76 || t[0] == 0x56) && dot >= 2 && dot + 1 < t.len()
        && hexdigs_between(t, 1, dot) && ipvfuture_tail_from(t, dot + 1)
}

/// What `IP-literal = "[" ( IPv6address / IPvFuture ) "]"` matched
/// against all of a string gives.
pub enum IpLiteral {
    /// An `IPv6address` in brackets, with its eight pieces.
    Ipv6(Seq<nat>),
    /// An `IPvFuture` in brackets.
    Future,
}

/// `IP-literal = "[" ( IPv6address / IPvFuture ) "]"`, matched against
/// all of `s`. (The two alternatives are disjoint: `IPvFuture` starts with
/// "v", which is not a `HEXDIG` or ":".)
pub open spec fn ip_literal(s: Seq<u32>) -> Option<IpLiteral> {
    if s.len() >= 2 && s[0] == 0x5B && s.last() == 0x5D {
        let inner = s.subrange(1, s.len() - 1);
        match ipv6address(inner) {
            Some(a) => Some(IpLiteral::Ipv6(a)),
            None => if is_ipvfuture(inner) {
                Some(IpLiteral::Future)
            } else {
                None
            },
        }
    } else {
        None
    }
}

// ---------------------------------------------------------------------
// RFC 3986 §3.2.2: the dotted-decimal text of an IPv4 address.
// ---------------------------------------------------------------------

/// The `dec-octet` text of `n` < 256: the one alternative of the rule that
/// denotes `n` (so no leading zeros).
pub open spec fn dec_octet_text(n: nat) -> Seq<u32> {
    if n < 10 {
        seq![(0x30 + n) as u32]
    } else if n < 100 {
        seq![(0x30 + n / 10) as u32, (0x30 + n % 10) as u32]
    } else {
        seq![(0x30 + n / 100) as u32, (0x30 + (n / 10) % 10) as u32, (0x30 + n % 10) as u32]
    }
}

/// The `IPv4address` text of the 32-bit address `a`: its four octets, most
/// significant first, as `dec-octet`s separated by ".".
pub open spec fn ipv4address_text(a: nat) -> Seq<u32> {
    dec_octet_text((a / 0x1000000) % 256) + seq![0x2Eu32] + dec_octet_text((a / 0x10000) % 256)
        + seq![0x2Eu32] + dec_octet_text((a / 0x100) % 256) + seq![0x2Eu32] + dec_octet_text(a % 256)
}

// ---------------------------------------------------------------------
// RFC 5952 §4: the recommended text form of an IPv6 address.
// ---------------------------------------------------------------------

/// The lowercase hexadecimal digit for `n` < 16 (§4.3 "The characters
/// "a", "b", "c", "d", "e", and "f" in an IPv6 address MUST be represented
/// in lowercase.").
pub open spec fn lower_hexdig(n: nat) -> u32 {
    if n < 10 {
        (0x30 + n) as u32
    } else {
        (0x61 + n - 10) as u32
    }
}

/// A 16-bit field in hexadecimal with leading zeros suppressed (§4.1
/// "Leading zeros MUST be suppressed. [...] A single 16-bit 0000 field
/// MUST be represented as 0.").
pub open spec fn field_text(n: nat) -> Seq<u32>
    decreases n
{
    if n < 16 {
        seq![lower_hexdig(n)]
    } else {
        field_text(n / 16) + seq![lower_hexdig(n % 16)]
    }
}

/// Fields `from` to `to` (exclusive) of `a`, separated by ":".
pub open spec fn fields_text(a: Seq<nat>, from: nat, to: nat) -> Seq<u32>
    decreases to - from
{
    if from >= to {
        seq![]
    } else if from + 1 == to {
        field_text(a[from as int])
    } else {
        field_text(a[from as int]) + seq![0x3Au32] + fields_text(a, from + 1, to)
    }
}

/// The number of consecutive zero fields of `a` starting at field `i`.
pub open spec fn zero_run(a: Seq<nat>, i: nat) -> nat
    decreases 8 - i
{
    if i < 8 && a[i as int] == 0 {
        1 + zero_run(a, i + 1)
    } else {
        0
    }
}

/// The first longest run of zero fields starting at field `i` or later,
/// given the best (start, length) found before `i`: a later run replaces
/// it only if it is strictly longer (§4.2.3 "When the length of the
/// consecutive 16-bit 0 fields are equal [...], the first sequence of zero
/// bits MUST be shortened.").
pub open spec fn longest_zero_run_from(a: Seq<nat>, i: nat, start: nat, len: nat) -> (nat, nat)
    decreases 8 - i
{
    if i >= 8 {
        (start, len)
    } else if zero_run(a, i) > len {
        longest_zero_run_from(a, i + 1, i, zero_run(a, i))
    } else {
        longest_zero_run_from(a, i + 1, start, len)
    }
}

/// The run of zero fields "::" replaces, as (start, length), if any: the
/// first longest one (§4.2.3 "the longest run of consecutive 16-bit 0
/// fields MUST be shortened"), all of it (§4.2.1 "The use of the symbol
/// "::" MUST be used to its maximum capability."), and only if it is at
/// least two fields long (§4.2.2 "The symbol "::" MUST NOT be used to
/// shorten just one 16-bit 0 field.").
pub open spec fn compressed_run(a: Seq<nat>) -> Option<(nat, nat)> {
    let (start, len) = longest_zero_run_from(a, 0, 0, 0);
    if len >= 2 {
        Some((start, len))
    } else {
        None
    }
}

/// The RFC 5952 §4 text of the IPv6 address with pieces `a`.
pub open spec fn rfc5952_text(a: Seq<nat>) -> Seq<u32> {
    match compressed_run(a) {
        None => fields_text(a, 0, 8),
        Some((start, len)) => fields_text(a, 0, start) + seq![0x3Au32, 0x3Au32] + fields_text(a, start + len, 8),
    }
}

} // verus!
