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
//! first (`reg-name` was added later, also from RFC 3986 alone). The
//! theorems relating them to `spec.rs` are at the end of this file.
//!
//! **What is proven** (for every input in the stated class):
//! - [`lemma_ipv4address_parses`]: a string matching `IPv4address` gets the
//!   same address from the URL Standard's IPv4 parser. Outside that class
//!   the URL Standard accepts more (fewer than four parts, octal and hex
//!   parts, a trailing "."), which RFC 3986 §7.4 calls "other forms of
//!   dotted notation".
//! - [`lemma_ipv4_serializer_rfc3986`]: the IPv4 serializer writes the
//!   `IPv4address` text of every address.
//! - [`lemma_ipv6address_parses`]: a string matching `IPv6address` gets the
//!   address RFC 4291 §2.2 gives it from the URL Standard's IPv6 parser.
//!   The converse (the URL Standard's IPv6 parser accepts nothing else) is
//!   **not proven**; `tests/conformance_hosts.rs` checks it against
//!   `std::net::Ipv6Addr` on 500,000 strings and finds no exception.
//! - [`lemma_ipv6_serializer_rfc5952`]: the IPv6 serializer writes RFC 5952
//!   §4's text of every address (§5's mixed notation is not used by the
//!   URL Standard, and not transcribed).
//! - [`lemma_ip_literal_host`]: the host parser gives a bracketed
//!   `IPv6address` its address, and fails on `IPvFuture` (a difference:
//!   the URL Standard has no IPvFuture hosts).
//! - [`lemma_reg_name_opaque_host`]: every `reg-name` is accepted by the
//!   opaque-host parser, unchanged. The URL Standard accepts more (any
//!   code point but the forbidden host code points).
//!
//! Not related here: domains, which go through the domain parser (URL
//! §3.3, `clazel-idna`).
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


// ---------------------------------------------------------------------
// RFC 3986 §3.2.2: reg-name. (Added after `spec.rs` existed, transcribed
// from RFC 3986 alone.)
// ---------------------------------------------------------------------

/// `unreserved = ALPHA / DIGIT / "-" / "." / "_" / "~"` and `sub-delims =
/// "!" / "$" / "&" / "'" / "(" / ")" / "*" / "+" / "," / ";" / "="`
/// (RFC 3986 §2.3, §2.2).
pub open spec fn is_unreserved_or_sub_delim(c: u32) -> bool {
    is_alpha(c) || is_digit(c) || c == 0x2D || c == 0x2E || c == 0x5F || c == 0x7E || c == 0x21
        || c == 0x24 || c == 0x26 || c == 0x27 || c == 0x28 || c == 0x29 || c == 0x2A || c == 0x2B
        || c == 0x2C || c == 0x3B || c == 0x3D
}

/// `reg-name = *( unreserved / pct-encoded / sub-delims )`, with
/// `pct-encoded = "%" HEXDIG HEXDIG` (§2.1), matched against `s` from
/// index `i` to the end.
pub open spec fn reg_name_from(s: Seq<u32>, i: nat) -> bool
    decreases s.len() - i
{
    if i >= s.len() {
        true
    } else if is_unreserved_or_sub_delim(s[i as int]) {
        reg_name_from(s, i + 1)
    } else {
        s[i as int] == 0x25 && i + 2 < s.len() && is_hexdig(s[i + 1int]) && is_hexdig(s[i + 2int])
            && reg_name_from(s, i + 3)
    }
}

/// `s` matches `reg-name`.
pub open spec fn reg_name(s: Seq<u32>) -> bool {
    reg_name_from(s, 0)
}

// =====================================================================
// Theorems: what the RFC transcription and the URL Standard
// transcription (`spec.rs`) are proven to agree on. Everything above was
// written before `spec.rs`; everything below relates the two.
// =====================================================================

// ---------------------------------------------------------------------
// Code points and hex numbers.
// ---------------------------------------------------------------------

/// `HEXDIG` is the URL Standard's ASCII hex digit, with the same value.
pub proof fn lemma_hexdig(c: u32)
    ensures
        is_hexdig(c) == super::spec::is_ascii_hex_digit(c),
        is_digit(c) == super::spec::is_ascii_digit(c),
        is_hexdig(c) ==> hexdig_value(c) == super::spec::hex_digit_value(c),
{
}

/// An `h16`'s digits and value, in the URL Standard's terms.
pub proof fn lemma_h16(t: Seq<u32>)
    requires
        h16(t) is Some,
    ensures
        1 <= t.len() <= 4,
        super::ipv6_text::all_hex(t),
        h16(t) == Some(super::spec::radix_value(t, 16)),
        h16(t).unwrap() < 0x1_0000,
{
    lemma_hex_number(t);
    reveal_with_fuel(super::spec::radix_value, 5);
}

/// `all_hexdig` and `hex_number` are the URL Standard's hex digits and
/// radix-16 value.
pub proof fn lemma_hex_number(t: Seq<u32>)
    requires
        all_hexdig(t),
    ensures
        super::ipv6_text::all_hex(t),
        hex_number(t) == super::spec::radix_value(t, 16),
        t.len() <= 4 ==> hex_number(t) < 0x1_0000,
    decreases t.len()
{
    if t.len() > 0 {
        lemma_hex_number(t.drop_last());
        lemma_hexdig(t.last());
        assert forall|k: int| 0 <= k < t.len() implies super::spec::is_ascii_hex_digit(#[trigger] t[k]) by {
            if k < t.len() - 1 {
                assert(t.drop_last()[k] == t[k]);
            }
        }
        if t.len() <= 4 {
            let m = t.drop_last();
            if m.len() == 0 {
                assert(hex_number(m) == 0);
            } else if m.len() == 1 {
                lemma_hex_number_bound(m);
            } else if m.len() == 2 {
                lemma_hex_number_bound(m);
            } else {
                lemma_hex_number_bound(m);
            }
        }
    }
}

/// `hex_number(t) < 16^|t|`, for up to three digits.
pub proof fn lemma_hex_number_bound(t: Seq<u32>)
    requires
        all_hexdig(t),
        t.len() <= 3,
    ensures
        t.len() == 0 ==> hex_number(t) == 0,
        t.len() == 1 ==> hex_number(t) < 16,
        t.len() == 2 ==> hex_number(t) < 256,
        t.len() == 3 ==> hex_number(t) < 0x1000,
    decreases t.len()
{
    if t.len() > 0 {
        lemma_hex_number_bound(t.drop_last());
    }
}

// ---------------------------------------------------------------------
// The URL Standard's IPv6 parser on RFC text: one piece.
// ---------------------------------------------------------------------

/// The IPv6 main loop reads an `h16` followed by ":" and more text.
pub proof fn lemma_main_loop_h16_colon(input: Seq<u32>, address: Seq<nat>, pi: int, compress: Option<int>, p: int, t: Seq<u32>)
    requires
        super::ipv6_text::text_at(input, p, t),
        h16(t) is Some,
        p + t.len() + 1 < input.len(),
        input[p + t.len()] == 0x3A,
        0 <= pi < 8,
    ensures
        super::spec::ipv6_main_loop(input, address, pi, compress, p) == super::spec::ipv6_main_loop(
            input,
            address.update(pi, h16(t).unwrap()),
            pi + 1,
            compress,
            p + t.len() + 1,
        ),
{
    lemma_h16(t);
    assert(input[p] == t[0]);
    super::ipv6_text::lemma_hex_digits_read(input, p, t, 0);
    assert(t.subrange(0, 0) =~= Seq::<u32>::empty());
}

/// The IPv6 main loop reads a final `h16`, up to the end.
pub proof fn lemma_main_loop_h16_end(input: Seq<u32>, address: Seq<nat>, pi: int, compress: Option<int>, p: int, t: Seq<u32>)
    requires
        super::ipv6_text::text_at(input, p, t),
        h16(t) is Some,
        p + t.len() == input.len(),
        0 <= pi < 8,
    ensures
        super::spec::ipv6_main_loop(input, address, pi, compress, p) == Some((address.update(pi, h16(t).unwrap()), pi + 1, compress)),
{
    lemma_h16(t);
    assert(input[p] == t[0]);
    super::ipv6_text::lemma_hex_digits_read(input, p, t, 0);
    assert(t.subrange(0, 0) =~= Seq::<u32>::empty());
}

// ---------------------------------------------------------------------
// The URL Standard's IPv6 parser on RFC text: an IPv4 tail.
// ---------------------------------------------------------------------

/// A `dec-octet`'s shape.
pub proof fn lemma_dec_octet(e: Seq<u32>)
    requires
        dec_octet(e) is Some,
    ensures
        1 <= e.len() <= 3,
        forall|k: int| 0 <= k < e.len() ==> is_digit(#[trigger] e[k]),
        e.len() >= 2 ==> e[0] != 0x30,
        dec_octet(e).unwrap() <= 255,
{
}

/// IPv4-in-IPv6 step 6.5.5.4 reads the rest of a `dec-octet` after its
/// first digit, and gives its value.
pub proof fn lemma_piece_digits_dec_octet(input: Seq<u32>, q: int, e: Seq<u32>)
    requires
        super::ipv6_text::text_at(input, q, e),
        dec_octet(e) is Some,
        q + e.len() == input.len() || !is_digit(input[q + e.len()]),
    ensures
        super::spec::ipv4_piece_digits(input, q + 1, digit_value(e[0])) == Some((dec_octet(e).unwrap(), q + e.len())),
{
    lemma_dec_octet(e);
    reveal_with_fuel(super::spec::ipv4_piece_digits, 4);
    assert(input[q] == e[0]);
    if e.len() >= 2 {
        assert(input[q + 1] == e[1]);
    }
    if e.len() == 3 {
        assert(input[q + 2] == e[2]);
    }
}

/// One round of IPv6 parser step 6.5.5: a `dec-octet` (after "." unless it
/// is the first).
pub proof fn lemma_ipv4_in_ipv6_step(input: Seq<u32>, address: Seq<nat>, pi: int, ns: nat, p: int, e: Seq<u32>)
    requires
        ns < 4,
        0 <= p < input.len(),
        ns > 0 ==> input[p] == 0x2E,
        super::ipv6_text::text_at(input, if ns > 0 {
            p + 1
        } else {
            p
        }, e),
        dec_octet(e) is Some,
        (if ns > 0 {
            p + 1
        } else {
            p
        }) + e.len() == input.len() || !is_digit(input[(if ns > 0 {
            p + 1
        } else {
            p
        }) + e.len()]),
    ensures
        super::spec::ipv4_in_ipv6(input, address, pi, ns, p) == super::spec::ipv4_in_ipv6(
            input,
            address.update(pi, address[pi] * 0x100 + dec_octet(e).unwrap()),
            if ns + 1 == 2 || ns + 1 == 4 {
                pi + 1
            } else {
                pi
            },
            ns + 1,
            (if ns > 0 {
                p + 1
            } else {
                p
            }) + e.len(),
        ),
{
    let q = if ns > 0 {
        p + 1
    } else {
        p
    };
    lemma_dec_octet(e);
    assert(input[q] == e[0]);
    lemma_piece_digits_dec_octet(input, q, e);
}

/// The IPv6 main loop reads an `IPv4address` tail, up to the end, into two
/// pieces (RFC 4291 §2.2 item 3).
pub proof fn lemma_main_loop_ipv4_tail(input: Seq<u32>, address: Seq<nat>, pi: int, compress: Option<int>, p: int)
    requires
        0 <= p <= input.len(),
        ipv4address_octets(input.subrange(p, input.len() as int)) is Some,
        address.len() == 8,
        0 <= pi <= 6,
        address[pi] == 0,
        address[pi + 1] == 0,
    ensures
        ({
            let o = ipv4address_octets(input.subrange(p, input.len() as int)).unwrap();
            super::spec::ipv6_main_loop(input, address, pi, compress, p) == Some(
                (address.update(pi, o[0] * 256 + o[1]).update(pi + 1, o[2] * 256 + o[3]), pi + 2, compress),
            )
        }),
{
    let t = input.subrange(p, input.len() as int);
    let o = ipv4address_octets(t).unwrap();
    let d1 = find(t, 0x2E, 0);
    let d2 = find(t, 0x2E, d1 + 1);
    let d3 = find(t, 0x2E, d2 + 1);
    lemma_find(t, 0x2E, 0);
    lemma_find(t, 0x2E, d1 + 1);
    lemma_find(t, 0x2E, d2 + 1);
    lemma_find(t, 0x2E, d3 + 1);
    let e1 = t.subrange(0, d1 as int);
    let e2 = t.subrange(d1 + 1int, d2 as int);
    let e3 = t.subrange(d2 + 1int, d3 as int);
    let e4 = t.subrange(d3 + 1int, t.len() as int);
    lemma_dec_octet(e1);
    lemma_dec_octet(e2);
    lemma_dec_octet(e3);
    lemma_dec_octet(e4);
    assert(super::ipv6_text::text_at(input, p, e1)) by {
        assert(input.subrange(p, p + e1.len()) =~= e1);
    }
    assert(super::ipv6_text::text_at(input, p + d1 + 1, e2)) by {
        assert(input.subrange(p + d1 + 1, p + d1 + 1 + e2.len()) =~= e2);
    }
    assert(super::ipv6_text::text_at(input, p + d2 + 1, e3)) by {
        assert(input.subrange(p + d2 + 1, p + d2 + 1 + e3.len()) =~= e3);
    }
    assert(super::ipv6_text::text_at(input, p + d3 + 1, e4)) by {
        assert(input.subrange(p + d3 + 1, p + d3 + 1 + e4.len()) =~= e4);
    }
    assert(input[p + d1] == 0x2E && input[p + d2] == 0x2E && input[p + d3] == 0x2E) by {
        assert(t[d1 as int] == input[p + d1]);
        assert(t[d2 as int] == input[p + d2]);
        assert(t[d3 as int] == input[p + d3]);
    }
    // Main loop: the hex digits of e1 stop at the first ".".
    assert(input[p] == e1[0]);
    assert(super::spec::is_ascii_hex_digit(e1[0]));
    let a0 = address;
    lemma_hex_digits_prefix(input, p, e1);
    lemma_ipv4_in_ipv6_step(input, a0, pi, 0, p, e1);
    let a1 = a0.update(pi, o[0]);
    lemma_ipv4_in_ipv6_step(input, a1, pi, 1, p + d1, e2);
    let a2 = a1.update(pi, o[0] * 256 + o[1]);
    lemma_ipv4_in_ipv6_step(input, a2, pi + 1, 2, p + d2, e3);
    let a3 = a2.update(pi + 1, o[2]);
    lemma_ipv4_in_ipv6_step(input, a3, pi + 1, 3, p + d3, e4);
    assert(p + d3 + 1 + e4.len() == input.len());
}

/// `find`'s result.
pub proof fn lemma_find(s: Seq<u32>, c: u32, from: nat)
    ensures
        from <= s.len() ==> from <= find(s, c, from) <= s.len(),
        from > s.len() ==> find(s, c, from) == s.len(),
        find(s, c, from) < s.len() ==> s[find(s, c, from) as int] == c,
        forall|k: int| from <= k < find(s, c, from) ==> s[k] != c,
    decreases s.len() - from
{
    if from < s.len() && s[from as int] != c {
        lemma_find(s, c, from + 1);
    }
}

/// IPv6 parser step 6.4 on decimal digits followed by "." : it reads them
/// all (at most three), and step 6.5 then starts the IPv4 loop at the same
/// pointer.
pub proof fn lemma_hex_digits_prefix(input: Seq<u32>, p: int, e: Seq<u32>)
    requires
        super::ipv6_text::text_at(input, p, e),
        dec_octet(e) is Some,
        p + e.len() < input.len(),
        input[p + e.len()] == 0x2E,
    ensures
        super::spec::ipv6_hex_digits(input, p, 0, 0).1 == e.len(),
{
    lemma_dec_octet(e);
    assert forall|k: int| 0 <= k < e.len() implies super::spec::is_ascii_hex_digit(#[trigger] e[k]) by {}
    super::ipv6_text::lemma_hex_digits_read(input, p, e, 0);
    assert(e.subrange(0, 0) =~= Seq::<u32>::empty());
}

// ---------------------------------------------------------------------
// The URL Standard's IPv6 parser on RFC text: lists of pieces.
// ---------------------------------------------------------------------

/// `ls32` and `j( h16 ":" ) ls32` match only non-empty text, and give
/// `j + 2` pieces.
pub proof fn lemma_h16_colons_ls32_shape(t: Seq<u32>, j: nat)
    requires
        h16_colons_ls32(t, j) is Some,
    ensures
        t.len() > 0,
        h16_colons_ls32(t, j).unwrap().len() == j + 2,
    decreases j
{
    let i = find(t, 0x3A, 0);
    lemma_find(t, 0x3A, 0);
    if j == 0 {
        if i < t.len() {
            lemma_h16(t.subrange(i + 1int, t.len() as int));
        } else {
            lemma_find(t, 0x2E, 0);
        }
    } else {
        lemma_h16_colons_ls32_shape(t.subrange(i + 1int, t.len() as int), (j - 1) as nat);
    }
}

/// The IPv6 main loop reads `ls32`, up to the end.
pub proof fn lemma_main_loop_ls32(input: Seq<u32>, address: Seq<nat>, pi: int, compress: Option<int>, p: int)
    requires
        0 <= p <= input.len(),
        ls32(input.subrange(p, input.len() as int)) is Some,
        address.len() == 8,
        0 <= pi <= 6,
        forall|k: int| pi <= k < 8 ==> address[k] == 0,
    ensures
        super::spec::ipv6_main_loop(input, address, pi, compress, p) == Some(
            (super::ipv6_text::write(address, pi, ls32(input.subrange(p, input.len() as int)).unwrap()), pi + 2, compress),
        ),
{
    let t = input.subrange(p, input.len() as int);
    let vals = ls32(t).unwrap();
    let i = find(t, 0x3A, 0);
    lemma_find(t, 0x3A, 0);
    reveal_with_fuel(super::ipv6_text::write, 3);
    if i < t.len() {
        let token = t.subrange(0, i as int);
        let rest = t.subrange(i + 1int, t.len() as int);
        assert(super::ipv6_text::text_at(input, p, token)) by {
            assert(input.subrange(p, p + token.len()) =~= token);
        }
        assert(input[p + i] == t[i as int]);
        lemma_h16(rest);
        lemma_main_loop_h16_colon(input, address, pi, compress, p, token);
        assert(super::ipv6_text::text_at(input, p + i + 1, rest)) by {
            assert(input.subrange(p + i + 1, p + i + 1 + rest.len()) =~= rest);
        }
        lemma_main_loop_h16_end(input, address.update(pi, h16(token).unwrap()), pi + 1, compress, p + i + 1, rest);
        assert(vals =~= seq![h16(token).unwrap(), h16(rest).unwrap()]);
        assert(vals.drop_first() =~= seq![h16(rest).unwrap()]);
        assert(vals.drop_first().drop_first() =~= Seq::<nat>::empty());
    } else {
        lemma_main_loop_ipv4_tail(input, address, pi, compress, p);
        let o = ipv4address_octets(t).unwrap();
        assert(vals =~= seq![o[0] * 256 + o[1], o[2] * 256 + o[3]]);
        assert(vals.drop_first() =~= seq![o[2] * 256 + o[3]]);
        assert(vals.drop_first().drop_first() =~= Seq::<nat>::empty());
    }
}

/// The IPv6 main loop reads `j( h16 ":" ) ls32`, up to the end.
pub proof fn lemma_main_loop_h16_colons_ls32(input: Seq<u32>, address: Seq<nat>, pi: int, compress: Option<int>, p: int, j: nat)
    requires
        0 <= p <= input.len(),
        h16_colons_ls32(input.subrange(p, input.len() as int), j) is Some,
        address.len() == 8,
        0 <= pi,
        pi + j <= 6,
        forall|k: int| pi <= k < 8 ==> address[k] == 0,
    ensures
        super::spec::ipv6_main_loop(input, address, pi, compress, p) == Some(
            (
                super::ipv6_text::write(address, pi, h16_colons_ls32(input.subrange(p, input.len() as int), j).unwrap()),
                pi + j + 2,
                compress,
            ),
        ),
    decreases j
{
    let t = input.subrange(p, input.len() as int);
    let vals = h16_colons_ls32(t, j).unwrap();
    let i = find(t, 0x3A, 0);
    lemma_find(t, 0x3A, 0);
    let token = t.subrange(0, i as int);
    let rest = t.subrange(i + 1int, t.len() as int);
    if j == 0 {
        lemma_main_loop_ls32(input, address, pi, compress, p);
    } else {
        assert(super::ipv6_text::text_at(input, p, token)) by {
            assert(input.subrange(p, p + token.len()) =~= token);
        }
        assert(input[p + i] == t[i as int]);
        assert(rest =~= input.subrange(p + i + 1, input.len() as int));
        lemma_h16_colons_ls32_shape(rest, (j - 1) as nat);
        lemma_main_loop_h16_colon(input, address, pi, compress, p, token);
        let v = h16(token).unwrap();
        lemma_main_loop_h16_colons_ls32(input, address.update(pi, v), pi + 1, compress, p + i + 1, (j - 1) as nat);
        assert(vals[0] == v);
        assert(vals.drop_first() =~= h16_colons_ls32(rest, (j - 1) as nat).unwrap());
    }
}

/// `h16_list` gives at least one piece.
pub proof fn lemma_h16_list_shape(t: Seq<u32>)
    requires
        h16_list(t) is Some,
    ensures
        h16_list(t).unwrap().len() >= 1,
        t.len() >= 1,
        super::spec::is_ascii_hex_digit(t[0]),
    decreases t.len()
{
    let i = find(t, 0x3A, 0);
    lemma_find(t, 0x3A, 0);
    lemma_h16(t.subrange(0, i as int));
    assert(t.subrange(0, i as int)[0] == t[0]);
}

/// The IPv6 main loop reads `h16 *( ":" h16 )` from `p` to `k`, where
/// ":" and more text follow.
pub proof fn lemma_main_loop_h16_list_colon(input: Seq<u32>, address: Seq<nat>, pi: int, compress: Option<int>, p: int, k: int)
    requires
        0 <= p <= k,
        k + 1 < input.len(),
        input[k] == 0x3A,
        h16_list(input.subrange(p, k)) is Some,
        address.len() == 8,
        0 <= pi,
        pi + h16_list(input.subrange(p, k)).unwrap().len() <= 8,
    ensures
        super::spec::ipv6_main_loop(input, address, pi, compress, p) == super::spec::ipv6_main_loop(
            input,
            super::ipv6_text::write(address, pi, h16_list(input.subrange(p, k)).unwrap()),
            pi + h16_list(input.subrange(p, k)).unwrap().len(),
            compress,
            k + 1,
        ),
    decreases k - p
{
    let t = input.subrange(p, k);
    let vals = h16_list(t).unwrap();
    let i = find(t, 0x3A, 0);
    lemma_find(t, 0x3A, 0);
    lemma_h16_list_shape(t);
    reveal_with_fuel(super::ipv6_text::write, 2);
    let token = t.subrange(0, i as int);
    assert(super::ipv6_text::text_at(input, p, token)) by {
        assert(input.subrange(p, p + token.len()) =~= token);
    }
    let v = h16(token).unwrap();
    if i >= t.len() {
        lemma_main_loop_h16_colon(input, address, pi, compress, p, token);
        assert(vals =~= seq![v]);
        assert(vals.drop_first() =~= Seq::<nat>::empty());
    } else {
        assert(input[p + i] == t[i as int]);
        let rest = t.subrange(i + 1int, t.len() as int);
        assert(rest =~= input.subrange(p + i + 1, k));
        lemma_h16_list_shape(rest);
        lemma_main_loop_h16_colon(input, address, pi, compress, p, token);
        lemma_main_loop_h16_list_colon(input, address.update(pi, v), pi + 1, compress, p + i + 1, k);
        assert(vals[0] == v);
        assert(vals.drop_first() =~= h16_list(rest).unwrap());
    }
}

/// `find_double_colon`'s result.
pub proof fn lemma_find_double_colon(s: Seq<u32>, from: nat)
    ensures
        find_double_colon(s, from) >= from || find_double_colon(s, from) == s.len(),
        find_double_colon(s, from) < s.len() ==> find_double_colon(s, from) + 1 < s.len()
            && s[find_double_colon(s, from) as int] == 0x3A && s[find_double_colon(s, from) + 1int] == 0x3A,
    decreases s.len() - from
{
    if from + 1 < s.len() && !(s[from as int] == 0x3A && s[from + 1int] == 0x3A) {
        lemma_find_double_colon(s, from + 1);
    }
}

/// After the "::" of alternative `m`, the IPv6 main loop reads the rest.
pub proof fn lemma_after_double_colon_parses(s: Seq<u32>, w1: Seq<nat>, pi: int, k: int, m: nat)
    requires
        0 <= k,
        k + 2 <= s.len(),
        2 <= m <= 9,
        after_double_colon(s.subrange(k + 2, s.len() as int), m) is Some,
        w1.len() == 8,
        1 <= pi,
        pi + 9 - m <= 8,
        m == 9 ==> pi <= 8,
        m == 8 ==> pi <= 7,
        forall|q: int| pi <= q < 8 ==> w1[q] == 0,
    ensures
        ({
            let r = after_double_colon(s.subrange(k + 2, s.len() as int), m).unwrap();
            super::spec::ipv6_main_loop(s, w1, pi, Some(pi), k + 2) == Some(
                (super::ipv6_text::write(w1, pi, r), pi + r.len(), Some(pi)),
            ) && r.len() == if m <= 7 {
                9 - m
            } else {
                9 - m
            }
        }),
{
    let after = s.subrange(k + 2, s.len() as int);
    let r = after_double_colon(after, m).unwrap();
    reveal_with_fuel(super::ipv6_text::write, 2);
    if 2 <= m <= 7 {
        lemma_h16_colons_ls32_shape(after, (7 - m) as nat);
        lemma_main_loop_h16_colons_ls32(s, w1, pi, Some(pi), k + 2, (7 - m) as nat);
    } else if m == 8 {
        lemma_h16(after);
        assert(super::ipv6_text::text_at(s, k + 2, after)) by {
            assert(s.subrange(k + 2, k + 2 + after.len()) =~= after);
        }
        lemma_main_loop_h16_end(s, w1, pi, Some(pi), k + 2, after);
        assert(r =~= seq![h16(after).unwrap()]);
        assert(r.drop_first() =~= Seq::<nat>::empty());
    } else {
        assert(r =~= Seq::<nat>::empty());
        assert(after.len() == 0);
        assert(k + 2 == s.len());
    }
}

/// The IPv6 parser's step 7 after "::": the pieces before it, zeros, and
/// the pieces after it.
pub proof fn lemma_finish_compressed(l: Seq<nat>, r: Seq<nat>)
    requires
        l.len() + r.len() <= 7,
    ensures
        ({
            let zeros8 = seq![0nat, 0, 0, 0, 0, 0, 0, 0];
            let w2 = super::ipv6_text::write(super::ipv6_text::write(zeros8, 0, l), l.len() + 1int, r);
            super::lemmas::ipv6_parser_after(Some((w2, l.len() + 1int + r.len(), Some(l.len() + 1int))))
                == Some(l + zeros((8 - l.len() - r.len()) as nat) + r)
        }),
{
    use super::ipv6_text::*;
    let zeros8 = seq![0nat, 0, 0, 0, 0, 0, 0, 0];
    let w1 = write(zeros8, 0, l);
    lemma_write(zeros8, 0, l);
    let pi = l.len() + 1int;
    let w2 = write(w1, pi, r);
    lemma_write(w1, pi, r);
    lemma_ipv6_swaps(w2, 7, pi, r.len() as int, r);
    let result = w2.subrange(0, pi) + Seq::new((8 - r.len() - pi) as nat, |_i: int| 0nat) + r;
    let expected = l + zeros((8 - l.len() - r.len()) as nat) + r;
    assert(result =~= expected) by {
        assert forall|q: int| 0 <= q < 8 implies #[trigger] result[q] == expected[q] by {
            if q < l.len() {
                assert(result[q] == w2[q]);
            }
        }
    }
}

/// Alternative `m` of `IPv6address` (2 to 9), with its "::" at `k`: the URL
/// Standard's IPv6 parser gives the same address.
pub proof fn lemma_compressed_parses(s: Seq<u32>, k: int, m: nat)
    requires
        0 <= k,
        k + 1 < s.len(),
        s[k] == 0x3A,
        s[k + 1] == 0x3A,
        2 <= m <= 9,
        compressed(m, s.subrange(0, k), s.subrange(k + 2, s.len() as int)) is Some,
    ensures
        super::spec::ipv6_parser(s) == compressed(m, s.subrange(0, k), s.subrange(k + 2, s.len() as int)),
{
    use super::ipv6_text::*;
    let zeros8 = seq![0nat, 0, 0, 0, 0, 0, 0, 0];
    let before = s.subrange(0, k);
    let after = s.subrange(k + 2, s.len() as int);
    let l = before_double_colon(before, (m - 2) as nat).unwrap();
    let r = after_double_colon(after, m).unwrap();
    let w1 = write(zeros8, 0, l);
    // The parser reaches the state after "::".
    if before.len() == 0 {
        assert(l =~= Seq::<nat>::empty());
        assert(w1 == zeros8);
        assert(super::spec::ipv6_parser(s) == super::lemmas::ipv6_parser_after(
            super::spec::ipv6_main_loop(s, w1, 1, Some(1), 2),
        ));
    } else {
        lemma_h16_list_shape(before);
        assert(s[0] == before[0]);
        lemma_main_loop_h16_list_colon(s, zeros8, 0, None, 0, k);
        lemma_write(zeros8, 0, l);
        assert(super::spec::ipv6_parser(s) == super::lemmas::ipv6_parser_after(
            super::spec::ipv6_main_loop(s, w1, l.len() + 1int, Some(l.len() + 1int), k + 2),
        ));
    }
    lemma_write(zeros8, 0, l);
    let pi = l.len() + 1int;
    // The pieces after "::".
    lemma_after_double_colon_parses(s, w1, pi, k, m);
    lemma_finish_compressed(l, r);
}

/// Alternatives `n` to 9: whichever matches first, the URL Standard's
/// IPv6 parser agrees.
pub proof fn lemma_compressed_from_parses(s: Seq<u32>, k: int, n: nat)
    requires
        0 <= k,
        k + 1 < s.len(),
        s[k] == 0x3A,
        s[k + 1] == 0x3A,
        2 <= n,
        compressed_from(n, s.subrange(0, k), s.subrange(k + 2, s.len() as int)) is Some,
    ensures
        super::spec::ipv6_parser(s) == compressed_from(n, s.subrange(0, k), s.subrange(k + 2, s.len() as int)),
    decreases 10 - n
{
    if compressed(n, s.subrange(0, k), s.subrange(k + 2, s.len() as int)) is Some {
        lemma_compressed_parses(s, k, n);
    } else {
        lemma_compressed_from_parses(s, k, n + 1);
    }
}

/// **RFC 3986 §3.2.2 `IPv6address` agrees with the URL Standard's IPv6
/// parser:** every string matching `IPv6address` parses to the address
/// RFC 4291 §2.2 gives it.
pub proof fn lemma_ipv6address_parses(s: Seq<u32>)
    requires
        ipv6address(s) is Some,
    ensures
        super::spec::ipv6_parser(s) == ipv6address(s),
{
    use super::ipv6_text::*;
    let k = find_double_colon(s, 0);
    lemma_find_double_colon(s, 0);
    if k >= s.len() {
        let zeros8 = seq![0nat, 0, 0, 0, 0, 0, 0, 0];
        let v = h16_colons_ls32(s, 6).unwrap();
        lemma_h16_colons_ls32_shape(s, 6);
        assert(s.subrange(0, s.len() as int) =~= s);
        let i = find(s, 0x3A, 0);
        lemma_find(s, 0x3A, 0);
        lemma_h16(s.subrange(0, i as int));
        assert(s.subrange(0, i as int)[0] == s[0]);
        lemma_main_loop_h16_colons_ls32(s, zeros8, 0, None, 0, 6);
        lemma_write(zeros8, 0, v);
        assert(write(zeros8, 0, v) =~= v);
    } else {
        lemma_compressed_from_parses(s, k as int, 2);
    }
}

// ---------------------------------------------------------------------
// IPv4: RFC 3986 IPv4address and the URL Standard's IPv4 parser and
// serializer.
// ---------------------------------------------------------------------

/// The IPv4 number parser reads a `dec-octet` as its decimal value.
pub proof fn lemma_ipv4_number_parser_dec_octet(e: Seq<u32>)
    requires
        dec_octet(e) is Some,
    ensures
        super::spec::ipv4_number_parser(e) == Some((dec_octet(e).unwrap(), false)),
{
    lemma_dec_octet(e);
    reveal_with_fuel(super::spec::all_radix_digits, 4);
    reveal_with_fuel(super::spec::radix_value, 4);
    if e.len() == 1 {
        assert(e.drop_last() =~= Seq::<u32>::empty());
    } else if e.len() == 2 {
        assert(e.drop_last() =~= seq![e[0]]);
        assert(e.drop_last().drop_last() =~= Seq::<u32>::empty());
    } else {
        assert(e.drop_last() =~= seq![e[0], e[1]]);
        assert(e.drop_last().drop_last() =~= seq![e[0]]);
        assert(e.drop_last().drop_last().drop_last() =~= Seq::<u32>::empty());
    }
}

/// An `IPv4address`, split at its dots.
pub proof fn lemma_ipv4address_split(s: Seq<u32>)
    requires
        ipv4address_octets(s) is Some,
    ensures
        ({
            let d1 = find(s, 0x2E, 0);
            let d2 = find(s, 0x2E, d1 + 1);
            let d3 = find(s, 0x2E, d2 + 1);
            let parts = seq![
                s.subrange(0, d1 as int),
                s.subrange(d1 + 1int, d2 as int),
                s.subrange(d2 + 1int, d3 as int),
                s.subrange(d3 + 1int, s.len() as int),
            ];
            &&& s == super::lemmas::split_join(parts, 0x2E)
            &&& forall|k: int| 0 <= k < 4 ==> super::lemmas::free_of(#[trigger] parts[k], 0x2E)
            &&& forall|k: int| 0 <= k < 4 ==> dec_octet(#[trigger] parts[k]) is Some
        }),
{
    let d1 = find(s, 0x2E, 0);
    let d2 = find(s, 0x2E, d1 + 1);
    let d3 = find(s, 0x2E, d2 + 1);
    lemma_find(s, 0x2E, 0);
    lemma_find(s, 0x2E, d1 + 1);
    lemma_find(s, 0x2E, d2 + 1);
    lemma_find(s, 0x2E, d3 + 1);
    let e1 = s.subrange(0, d1 as int);
    let e2 = s.subrange(d1 + 1int, d2 as int);
    let e3 = s.subrange(d2 + 1int, d3 as int);
    let e4 = s.subrange(d3 + 1int, s.len() as int);
    let parts = seq![e1, e2, e3, e4];
    reveal_with_fuel(super::lemmas::split_tail, 4);
    assert(parts.drop_first() =~= seq![e2, e3, e4]);
    assert(parts.drop_first().drop_first() =~= seq![e3, e4]);
    assert(parts.drop_first().drop_first().drop_first() =~= seq![e4]);
    assert(parts.drop_first().drop_first().drop_first().drop_first() =~= Seq::<Seq<u32>>::empty());
    let dot = seq![0x2Eu32];
    assert(s =~= e1 + (dot + e2 + (dot + e3 + (dot + e4 + Seq::<u32>::empty()))));
    assert forall|k: int| 0 <= k < 4 implies super::lemmas::free_of(#[trigger] parts[k], 0x2E) by {
        if k == 0 {
            assert forall|q: int| 0 <= q < e1.len() implies e1[q] != 0x2E by {
                assert(e1[q] == s[q]);
            }
        } else if k == 1 {
            assert forall|q: int| 0 <= q < e2.len() implies e2[q] != 0x2E by {
                assert(e2[q] == s[d1 + 1 + q]);
            }
        } else if k == 2 {
            assert forall|q: int| 0 <= q < e3.len() implies e3[q] != 0x2E by {
                assert(e3[q] == s[d2 + 1 + q]);
            }
        } else {
            assert forall|q: int| 0 <= q < e4.len() implies e4[q] != 0x2E by {
                assert(e4[q] == s[d3 + 1 + q]);
            }
        }
    }
}

/// The IPv4 parser's steps 5 to 14 on four `dec-octet` parts.
pub proof fn lemma_ipv4_parser_four_parts(parts: Seq<Seq<u32>>)
    requires
        parts.len() == 4,
        forall|k: int| 0 <= k < 4 ==> dec_octet(#[trigger] parts[k]) is Some,
    ensures
        ({
            let o0 = dec_octet(parts[0]).unwrap();
            let o1 = dec_octet(parts[1]).unwrap();
            let o2 = dec_octet(parts[2]).unwrap();
            let o3 = dec_octet(parts[3]).unwrap();
            let numbers = seq![o0, o1, o2, o3];
            &&& super::spec::ipv4_parse_parts(parts, 0, seq![]) == Some(numbers)
            &&& !super::spec::any_greater_than_255(numbers, 0, 3)
            &&& numbers.last() < super::spec::pow256(1)
            &&& super::spec::ipv4_sum(numbers.drop_last(), 0, numbers.last()) == ((o0 * 256 + o1) * 256 + o2) * 256 + o3
        }),
{
    let o0 = dec_octet(parts[0]).unwrap();
    let o1 = dec_octet(parts[1]).unwrap();
    let o2 = dec_octet(parts[2]).unwrap();
    let o3 = dec_octet(parts[3]).unwrap();
    assert(dec_octet(parts[0]) is Some && dec_octet(parts[1]) is Some && dec_octet(parts[2]) is Some && dec_octet(parts[3]) is Some);
    lemma_ipv4_number_parser_dec_octet(parts[0]);
    lemma_ipv4_number_parser_dec_octet(parts[1]);
    lemma_ipv4_number_parser_dec_octet(parts[2]);
    lemma_ipv4_number_parser_dec_octet(parts[3]);
    lemma_dec_octet(parts[0]);
    lemma_dec_octet(parts[1]);
    lemma_dec_octet(parts[2]);
    lemma_dec_octet(parts[3]);
    let numbers = seq![o0, o1, o2, o3];
    reveal_with_fuel(super::spec::ipv4_parse_parts, 5);
    assert(seq![o0] =~= Seq::<nat>::empty().push(o0));
    assert(seq![o0, o1] =~= seq![o0].push(o1));
    assert(seq![o0, o1, o2] =~= seq![o0, o1].push(o2));
    assert(numbers =~= seq![o0, o1, o2].push(o3));
    reveal_with_fuel(super::spec::any_greater_than_255, 4);
    reveal_with_fuel(super::spec::pow256, 5);
    assert(super::spec::pow256(1) == 256);
    assert(super::spec::pow256(2) == 0x1_0000);
    assert(super::spec::pow256(3) == 0x100_0000);
    let rest = numbers.drop_last();
    assert(rest =~= seq![o0, o1, o2]);
    reveal_with_fuel(super::spec::ipv4_sum, 4);
    let total = o3 + o0 * 0x100_0000 + o1 * 0x1_0000 + o2 * 0x100;
    assert(super::spec::ipv4_sum(rest, 3, total) == total);
}

/// **RFC 3986 §3.2.2 `IPv4address` agrees with the URL Standard's IPv4
/// parser:** every dotted-decimal string of four `dec-octet`s parses to the
/// same address. (The URL Standard's parser accepts more: fewer parts,
/// octal and hex parts, a trailing dot. Those strings are not
/// `IPv4address`es.)
pub proof fn lemma_ipv4address_parses(s: Seq<u32>)
    requires
        ipv4address(s) is Some,
    ensures
        super::spec::ipv4_parser(s) == ipv4address(s),
{
    lemma_ipv4address_split(s);
    let d1 = find(s, 0x2E, 0);
    let d2 = find(s, 0x2E, d1 + 1);
    let d3 = find(s, 0x2E, d2 + 1);
    let parts = seq![
        s.subrange(0, d1 as int),
        s.subrange(d1 + 1int, d2 as int),
        s.subrange(d2 + 1int, d3 as int),
        s.subrange(d3 + 1int, s.len() as int),
    ];
    super::lemmas::lemma_strictly_split_join(parts, 0x2E);
    lemma_ipv4_parser_four_parts(parts);
    lemma_dec_octet(parts[3]);
    assert(parts.last().len() > 0);
}

/// "Serialize an integer" writes a byte as its `dec-octet` text.
pub proof fn lemma_serialize_integer_dec_octet(n: nat)
    requires
        n < 256,
    ensures
        super::spec::serialize_integer(n) == dec_octet_text(n),
{
    super::lemmas::lemma_serialize_byte(n);
}

/// **The URL Standard's IPv4 serializer writes RFC 3986's dotted-decimal
/// form**, for every 32-bit address.
pub proof fn lemma_ipv4_serializer_rfc3986(a: nat)
    requires
        a < 0x1_0000_0000,
    ensures
        super::spec::ipv4_serializer(a) == ipv4address_text(a),
{
    super::lemmas::lemma_ipv4_serializer_join(a);
    assert(a / 256 / 256 / 256 == a / 0x100_0000 && a / 256 / 256 == a / 0x1_0000) by (nonlinear_arith)
        requires
            a < 0x1_0000_0000,
    ;
    lemma_serialize_integer_dec_octet(a % 256);
    lemma_serialize_integer_dec_octet((a / 256) % 256);
    lemma_serialize_integer_dec_octet((a / 256 / 256) % 256);
    lemma_serialize_integer_dec_octet((a / 256 / 256 / 256) % 256);
    let t0 = dec_octet_text(a % 256);
    let t1 = dec_octet_text((a / 0x100) % 256);
    let t2 = dec_octet_text((a / 0x1_0000) % 256);
    let t3 = dec_octet_text((a / 0x100_0000) % 256);
    let parts = seq![t3, t2, t1, t0];
    reveal_with_fuel(super::lemmas::split_tail, 4);
    assert(parts.drop_first() =~= seq![t2, t1, t0]);
    assert(parts.drop_first().drop_first() =~= seq![t1, t0]);
    assert(parts.drop_first().drop_first().drop_first() =~= seq![t0]);
    assert(parts.drop_first().drop_first().drop_first().drop_first() =~= Seq::<Seq<u32>>::empty());
    let dot = seq![0x2Eu32];
    assert(super::lemmas::split_join(parts, 0x2E) =~= ipv4address_text(a));
}

// ---------------------------------------------------------------------
// IP-literal and the host parser.
// ---------------------------------------------------------------------

/// **RFC 3986 `IP-literal` and the URL Standard's host parser:** an
/// `IPv6address` in brackets parses to its address, whatever isOpaque and
/// the domain parser; an `IPvFuture` in brackets is failure (a stated
/// difference: the URL Standard has no IPvFuture hosts).
pub proof fn lemma_ip_literal_host(s: Seq<u32>, is_opaque: bool, domain_parser: super::spec::DomainParser)
    requires
        ip_literal(s) is Some,
    ensures
        ip_literal(s) matches Some(IpLiteral::Ipv6(a)) ==> super::spec::host_parser(s, is_opaque, domain_parser) == Some(
            super::spec::Host::Ipv6(a),
        ),
        ip_literal(s) matches Some(IpLiteral::Future) ==> super::spec::host_parser(s, is_opaque, domain_parser) is None,
{
    let inner = s.subrange(1, s.len() - 1);
    match ipv6address(inner) {
        Some(a) => {
            lemma_ipv6address_parses(inner);
        },
        None => {
            // IPv6 parser step 5 is not taken ("v" is not ":"); in step 6
            // "v" is not a hex digit, ".", ":" or the end: 6.7 fails.
            assert(inner[0] == 0x76 || inner[0] == 0x56);
            assert(super::spec::ipv6_hex_digits(inner, 0, 0, 0) == (0nat, 0nat));
        },
    }
}

// ---------------------------------------------------------------------
// RFC 5952 §4 and the URL Standard's IPv6 serializer.
// ---------------------------------------------------------------------

/// RFC 5952's field text is the URL Standard's "shortest possible
/// lowercase hexadecimal number".
pub proof fn lemma_field_text(n: nat)
    ensures
        field_text(n) == super::spec::shortest_lowercase_hex(n),
    decreases n
{
    if n >= 16 {
        lemma_field_text(n / 16);
    }
}

/// Fields `i` to `j`, separated by ":", then one more ":".
pub proof fn lemma_fields_text_colons(a: Seq<nat>, i: nat, j: nat)
    requires
        i < j <= a.len(),
    ensures
        fields_text(a, i, j) + seq![0x3Au32] == super::ipv6_text::hex_text_colons(a.subrange(i as int, j as int)),
    decreases j - i
{
    lemma_field_text(a[i as int]);
    let sub = a.subrange(i as int, j as int);
    assert(sub.drop_first() =~= a.subrange(i + 1int, j as int));
    if i + 1 == j {
        assert(sub.drop_first() =~= Seq::<nat>::empty());
        assert(super::ipv6_text::hex_text_colons(sub.drop_first()) =~= Seq::<u32>::empty());
        assert(fields_text(a, i, j) + seq![0x3Au32] =~= super::ipv6_text::hex_text_colons(sub));
    } else {
        lemma_fields_text_colons(a, i + 1, j);
        assert(fields_text(a, i, j) + seq![0x3Au32] =~= super::ipv6_text::hex_text_colons(sub));
    }
}

/// Fields `i` to the end, separated by ":".
pub proof fn lemma_fields_text_list(a: Seq<nat>, i: nat)
    requires
        i <= a.len(),
    ensures
        fields_text(a, i, a.len()) == super::ipv6_text::hex_text(a.subrange(i as int, a.len() as int)),
    decreases a.len() - i
{
    let sub = a.subrange(i as int, a.len() as int);
    if i < a.len() {
        lemma_field_text(a[i as int]);
        assert(sub.drop_first() =~= a.subrange(i + 1int, a.len() as int));
        lemma_fields_text_list(a, i + 1);
    } else {
        assert(sub =~= Seq::<nat>::empty());
    }
}

/// RFC 5952's zero run is the one the serializer skips.
pub proof fn lemma_zero_run_same(a: Seq<nat>, i: nat)
    requires
        a.len() == 8,
    ensures
        zero_run(a, i) == super::ipv6_text::zero_run_len(a, i as int),
    decreases 8 - i
{
    if i < 8 && a[i as int] == 0 {
        lemma_zero_run_same(a, i + 1);
    }
}

/// RFC 5952 §4.2's choice of run is the URL Standard's "compressed piece
/// index": the first of the longest runs of at least two zero pieces.
pub proof fn lemma_compressed_run_same(a: Seq<nat>)
    requires
        a.len() == 8,
    ensures
        super::spec::find_ipv6_compressed_piece_index(a) == match compressed_run(a) {
            Some((start, _len)) => Some(start as int),
            None => None,
        },
        compressed_run(a) matches Some((start, len)) ==> len == zero_run(a, start) && start < 8,
{
    reveal_with_fuel(super::spec::find_compressed_loop, 10);
    reveal_with_fuel(longest_zero_run_from, 10);
    reveal_with_fuel(zero_run, 10);
}

/// **The URL Standard's IPv6 serializer writes RFC 5952 §4's recommended
/// text**, for every address.
pub proof fn lemma_ipv6_serializer_rfc5952(a: Seq<nat>)
    requires
        a.len() == 8,
    ensures
        super::spec::ipv6_serializer(a) == rfc5952_text(a),
{
    super::ipv6_text::lemma_ipv6_serializer_text(a);
    lemma_compressed_run_same(a);
    match compressed_run(a) {
        None => {
            lemma_fields_text_list(a, 0);
            assert(a.subrange(0, 8) =~= a);
        },
        Some((c, l)) => {
            lemma_zero_run_same(a, c);
            super::ipv6_text::lemma_zero_run(a, c as int);
            lemma_fields_text_list(a, c + l);
            let right = fields_text(a, c + l, 8);
            if c == 0 {
                assert(fields_text(a, 0, 0) =~= Seq::<u32>::empty());
                assert(a.subrange(0, 0) =~= Seq::<nat>::empty());
                assert(super::ipv6_text::hex_text_colons(a.subrange(0, 0)) =~= Seq::<u32>::empty());
                assert(rfc5952_text(a) =~= super::spec::ipv6_serializer(a));
            } else {
                lemma_fields_text_colons(a, 0, c);
                assert(rfc5952_text(a) =~= (fields_text(a, 0, c) + seq![0x3Au32]) + seq![0x3Au32] + right);
            }
        },
    }
}

// ---------------------------------------------------------------------
// reg-name and the opaque-host parser.
// ---------------------------------------------------------------------

/// A `reg-name`'s code points are printable ASCII, and none is a
/// forbidden host code point.
pub proof fn lemma_reg_name_code_points(s: Seq<u32>, i: nat)
    requires
        reg_name_from(s, i),
    ensures
        forall|k: int| i <= k < s.len() ==> 0x21 <= #[trigger] s[k] <= 0x7E && !super::spec::is_forbidden_host_code_point(s[k]),
    decreases s.len() - i
{
    if i < s.len() {
        if is_unreserved_or_sub_delim(s[i as int]) {
            lemma_reg_name_code_points(s, i + 1);
        } else {
            lemma_reg_name_code_points(s, i + 3);
        }
    }
}

/// No forbidden host code point from `i` on.
proof fn lemma_no_forbidden_from(s: Seq<u32>, i: nat)
    requires
        forall|k: int| 0 <= k < s.len() ==> !super::spec::is_forbidden_host_code_point(#[trigger] s[k]),
    ensures
        !super::spec::contains_forbidden_host_code_point_from(s, i),
    decreases s.len() - i
{
    if i < s.len() {
        lemma_no_forbidden_from(s, i + 1);
    }
}

/// Percent-encode after encoding's step 7.3 leaves printable ASCII bytes
/// alone with the C0 control percent-encode set.
proof fn lemma_c0_output_bytes_identity(bytes: Seq<u8>, i: nat)
    requires
        i <= bytes.len(),
        forall|k: int| 0 <= k < bytes.len() ==> 0x21 <= #[trigger] bytes[k] <= 0x7E,
    ensures
        clazel_percent::spec::encode_output_bytes(clazel_percent::spec::PercentEncodeSet::C0Control, false, bytes, i)
            == bytes.subrange(i as int, bytes.len() as int).map_values(|b: u8| b as u32),
    decreases bytes.len() - i
{
    if i < bytes.len() {
        lemma_c0_output_bytes_identity(bytes, i + 1);
        assert(bytes.subrange(i as int, bytes.len() as int).map_values(|b: u8| b as u32) =~= seq![bytes[i as int] as u32]
            + bytes.subrange(i + 1int, bytes.len() as int).map_values(|b: u8| b as u32));
    } else {
        assert(bytes.subrange(i as int, bytes.len() as int).map_values(|b: u8| b as u32) =~= Seq::<u32>::empty());
    }
}

/// **RFC 3986 `reg-name` and the URL Standard's opaque-host parser:**
/// every `reg-name` is accepted, unchanged. (The URL Standard accepts more:
/// any code point but the forbidden host code points, percent-encoding the
/// C0 controls and non-ASCII ones.)
pub proof fn lemma_reg_name_opaque_host(s: Seq<u32>)
    requires
        reg_name(s),
    ensures
        super::spec::opaque_host_parser(s) == Some(s),
{
    lemma_reg_name_code_points(s, 0);
    lemma_no_forbidden_from(s, 0);
    assert(clazel_percent::lemmas::all_ascii(s));
    clazel_percent::lemmas::lemma_utf8_encode_ascii(s);
    let bytes = s.map_values(|c: u32| c as u8);
    lemma_c0_output_bytes_identity(bytes, 0);
    assert(bytes.subrange(0, bytes.len() as int).map_values(|b: u8| b as u32) =~= s);
}

} // verus!
