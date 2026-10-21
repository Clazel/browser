//! Facts proven about the spec. Some are evidence that the transcription
//! is right (the parsers only return values that fit the standard's
//! types; serializing then parsing an address gives it back); the rest are
//! working facts the implementation's proof uses.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------
// Working facts: strings.
// ---------------------------------------------------------------------

/// A string with a code point that is not a radix-`r` digit does not
/// consist of radix-`r` digits.
pub proof fn lemma_all_radix_digits_index(s: Seq<u32>, r: nat, k: int)
    requires
        0 <= k < s.len(),
        !is_radix_digit(s[k], r),
    ensures
        !all_radix_digits(s, r),
    decreases s.len()
{
    if k < s.len() - 1 {
        assert(s.drop_last()[k] == s[k]);
        lemma_all_radix_digits_index(s.drop_last(), r, k);
    }
}

/// A string with a code point that is not an ASCII digit does not contain
/// only ASCII digits.
pub proof fn lemma_contains_only_ascii_digits_index(s: Seq<u32>, k: int)
    requires
        0 <= k < s.len(),
        !is_ascii_digit(s[k]),
    ensures
        !contains_only_ascii_digits(s),
    decreases s.len()
{
    if k < s.len() - 1 {
        assert(s.drop_last()[k] == s[k]);
        lemma_contains_only_ascii_digits_index(s.drop_last(), k);
    }
}

/// Saturating at 2^32 before or after a radix step gives the same result.
pub proof fn lemma_saturate_step(x: nat, r: nat, d: nat)
    requires
        r >= 1,
    ensures
        super::contract::saturate_u32(super::contract::saturate_u32(x) * r + d) == super::contract::saturate_u32(x * r + d),
{
    if x > 0xFFFF_FFFF {
        assert(x * r >= x) by (nonlinear_arith)
            requires
                r >= 1,
        ;
        assert(0x1_0000_0000 * r >= 0x1_0000_0000) by (nonlinear_arith)
            requires
                r >= 1,
        ;
    }
}

/// The strictly split loop keeps the tokens it has, and adds one more if
/// the input is not used up.
pub proof fn lemma_strictly_split_loop_shape(input: Seq<u32>, delimiter: u32, position: nat, tokens: Seq<Seq<u32>>)
    ensures
        strictly_split_loop(input, delimiter, position, tokens).len() >= tokens.len(),
        position < input.len() ==> strictly_split_loop(input, delimiter, position, tokens).len() > tokens.len(),
        forall|k: int| 0 <= k < tokens.len() ==> #[trigger] strictly_split_loop(input, delimiter, position, tokens)[k] == tokens[k],
    decreases input.len() - position
{
    if position < input.len() {
        let token = collect_not_equal(input, delimiter, position + 1);
        super::termination::lemma_collect_not_equal_len(input, delimiter, position + 1);
        lemma_strictly_split_loop_shape(input, delimiter, position + 1 + token.len(), tokens.push(token));
        let result = strictly_split_loop(input, delimiter, position, tokens);
        assert forall|k: int| 0 <= k < tokens.len() implies #[trigger] result[k] == tokens[k] by {
            assert(tokens.push(token)[k] == tokens[k]);
        }
    }
}

/// Strictly splitting gives at least one token, and if it gives exactly
/// one, that token is the whole input.
pub proof fn lemma_strictly_split_shape(input: Seq<u32>, delimiter: u32)
    ensures
        strictly_split(input, delimiter).len() >= 1,
        strictly_split(input, delimiter).len() == 1 ==> strictly_split(input, delimiter)[0].len() == input.len(),
{
    let token = collect_not_equal(input, delimiter, 0);
    super::termination::lemma_collect_not_equal_len(input, delimiter, 0);
    lemma_strictly_split_loop_shape(input, delimiter, token.len(), seq![token]);
}

// ---------------------------------------------------------------------
// The IPv4 parser returns a 32-bit address.
// ---------------------------------------------------------------------

/// The parts the IPv4 parser has after its step 2.
pub open spec fn ipv4_parser_parts(input: Seq<u32>) -> Seq<Seq<u32>> {
    let parts = strictly_split(input, 0x2E);
    if parts.last().len() == 0 && parts.len() > 1 {
        parts.drop_last()
    } else {
        parts
    }
}

/// The IPv4 parser's step 6 loop, once every part is parsed.
pub proof fn lemma_ipv4_parse_parts_done(parts: Seq<Seq<u32>>, numbers: Seq<nat>)
    requires
        numbers.len() == parts.len(),
    ensures
        ipv4_parse_parts(parts, parts.len(), numbers) == Some(numbers),
{
}

/// The IPv4 parser's step 6 loop appends one number per part.
pub proof fn lemma_ipv4_parse_parts_len(parts: Seq<Seq<u32>>, i: nat, numbers: Seq<nat>)
    requires
        i <= parts.len(),
    ensures
        ipv4_parse_parts(parts, i, numbers) matches Some(r) ==> r.len() == numbers.len() + parts.len() - i,
    decreases parts.len() - i
{
    if i < parts.len() {
        if let Some(result) = ipv4_number_parser(parts[i as int]) {
            lemma_ipv4_parse_parts_len(parts, i + 1, numbers.push(result.0));
        }
    }
}

/// No item from `i` to `end` is greater than 255.
pub proof fn lemma_not_any_greater_than_255(numbers: Seq<nat>, i: nat, end: nat)
    requires
        !any_greater_than_255(numbers, i, end),
    ensures
        forall|k: int| i <= k < end ==> #[trigger] numbers[k] <= 255,
    decreases end - i
{
    if i < end {
        lemma_not_any_greater_than_255(numbers, i + 1, end);
    }
}

/// The IPv4 parser only returns 32-bit addresses (§3.1: "An IPv4 address
/// is a 32-bit unsigned integer").
pub proof fn lemma_ipv4_parser_32_bit(input: Seq<u32>)
    ensures
        ipv4_parser(input) matches Some(a) ==> a < 0x1_0000_0000,
{
    let parts0 = strictly_split(input, 0x2E);
    lemma_strictly_split_shape(input, 0x2E);
    let parts = if parts0.last().len() == 0 && parts0.len() > 1 {
        parts0.drop_last()
    } else {
        parts0
    };
    if parts.len() <= 4 {
        lemma_ipv4_parse_parts_len(parts, 0, seq![]);
        if let Some(numbers) = ipv4_parse_parts(parts, 0, seq![]) {
            let m = numbers.len();
            if !any_greater_than_255(numbers, 0, (m - 1) as nat) && numbers.last() < pow256((5 - m) as nat) {
                lemma_not_any_greater_than_255(numbers, 0, (m - 1) as nat);
                let rest = numbers.drop_last();
                let last = numbers.last();
                reveal_with_fuel(pow256, 5);
                assert(pow256(1) == 0x100);
                assert(pow256(2) == 0x1_0000);
                assert(pow256(3) == 0x100_0000);
                assert(pow256(4) == 0x1_0000_0000);
                assert(1 <= m <= 4);
                if m == 1 {
                    assert(ipv4_sum(rest, 0, last) == last);
                } else if m == 2 {
                    assert(rest[0] == numbers[0]);
                    assert(ipv4_sum(rest, 1, last + rest[0] * 0x100_0000) == last + rest[0] * 0x100_0000);
                } else if m == 3 {
                    assert(rest[0] == numbers[0] && rest[1] == numbers[1]);
                    let s1 = last + rest[0] * 0x100_0000;
                    let s2 = s1 + rest[1] * 0x1_0000;
                    assert(ipv4_sum(rest, 2, s2) == s2);
                    assert(ipv4_sum(rest, 1, s1) == s2);
                } else {
                    assert(rest[0] == numbers[0] && rest[1] == numbers[1] && rest[2] == numbers[2]);
                    let s1 = last + rest[0] * 0x100_0000;
                    let s2 = s1 + rest[1] * 0x1_0000;
                    let s3 = s2 + rest[2] * 0x100;
                    assert(ipv4_sum(rest, 3, s3) == s3);
                    assert(ipv4_sum(rest, 2, s2) == s3);
                    assert(ipv4_sum(rest, 1, s1) == s3);
                }
                assert(ipv4_sum(rest, 0, last) < 0x1_0000_0000);
            }
        }
    }
}

// ---------------------------------------------------------------------
// Strictly splitting a joined list.
// ---------------------------------------------------------------------

/// `[d] + t1 + [d] + t2 + ...`: what follows the first token of a list
/// joined with `d`.
pub open spec fn split_tail(rest: Seq<Seq<u32>>, d: u32) -> Seq<u32>
    decreases rest.len()
{
    if rest.len() == 0 {
        seq![]
    } else {
        seq![d] + rest[0] + split_tail(rest.drop_first(), d)
    }
}

/// `tokens` joined with `d` (at least one token).
pub open spec fn split_join(tokens: Seq<Seq<u32>>, d: u32) -> Seq<u32> {
    tokens[0] + split_tail(tokens.drop_first(), d)
}

/// `t` does not contain `d`.
pub open spec fn free_of(t: Seq<u32>, d: u32) -> bool {
    forall|k: int| 0 <= k < t.len() ==> t[k] != d
}

/// Collecting from `p` gives `t` when `t` is there, free of the
/// delimiter, and followed by the delimiter or the end.
pub proof fn lemma_collect_token(s: Seq<u32>, d: u32, p: int, t: Seq<u32>)
    requires
        0 <= p,
        p + t.len() <= s.len(),
        s.subrange(p, p + t.len()) == t,
        free_of(t, d),
        p + t.len() == s.len() || s[p + t.len()] == d,
    ensures
        collect_not_equal(s, d, p as nat) == t,
    decreases t.len()
{
    if t.len() == 0 {
        assert(collect_not_equal(s, d, p as nat) == Seq::<u32>::empty());
    } else {
        assert(s[p] == t[0]);
        let t1 = t.drop_first();
        assert(s.subrange(p + 1, p + 1 + t1.len()) =~= t1);
        lemma_collect_token(s, d, p + 1, t1);
        assert(seq![t[0]] + t1 =~= t);
    }
}

/// The strictly split loop on a joined tail.
pub proof fn lemma_split_loop_tail(s: Seq<u32>, d: u32, pos: int, acc: Seq<Seq<u32>>, rest: Seq<Seq<u32>>)
    requires
        0 <= pos <= s.len(),
        s.subrange(pos, s.len() as int) == split_tail(rest, d),
        forall|k: int| 0 <= k < rest.len() ==> free_of(#[trigger] rest[k], d),
    ensures
        strictly_split_loop(s, d, pos as nat, acc) == acc + rest,
    decreases rest.len()
{
    if rest.len() == 0 {
        assert(acc + rest =~= acc);
    } else {
        let t = rest[0];
        let r = rest.drop_first();
        let tail = split_tail(rest, d);
        assert(tail =~= seq![d] + t + split_tail(r, d));
        assert(s[pos] == tail[0]);
        assert(s.subrange(pos + 1, pos + 1 + t.len()) =~= t) by {
            assert forall|k: int| 0 <= k < t.len() implies s.subrange(pos + 1, pos + 1 + t.len())[k] == t[k] by {
                assert(s[pos + 1 + k] == tail[1 + k]);
            }
        }
        if pos + 1 + t.len() < s.len() {
            assert(s[pos + 1 + t.len()] == tail[1 + t.len() as int]);
            assert(split_tail(r, d).len() > 0);
            assert(tail[1 + t.len() as int] == split_tail(r, d)[0]);
        }
        lemma_collect_token(s, d, pos + 1, t);
        assert forall|k: int| 0 <= k < r.len() implies free_of(#[trigger] r[k], d) by {
            assert(r[k] == rest[k + 1]);
        }
        assert(s.subrange(pos + 1 + t.len(), s.len() as int) =~= split_tail(r, d)) by {
            assert forall|k: int| 0 <= k < split_tail(r, d).len() implies s.subrange(pos + 1 + t.len(), s.len() as int)[k] == split_tail(r, d)[k] by {
                assert(s[pos + 1 + t.len() + k] == tail[1 + t.len() + k]);
            }
        }
        lemma_split_loop_tail(s, d, pos + 1 + t.len(), acc.push(t), r);
        assert(acc.push(t) + r =~= acc + rest);
    }
}

/// Strictly splitting a joined list gives the list back.
pub proof fn lemma_strictly_split_join(tokens: Seq<Seq<u32>>, d: u32)
    requires
        tokens.len() >= 1,
        forall|k: int| 0 <= k < tokens.len() ==> free_of(#[trigger] tokens[k], d),
    ensures
        strictly_split(split_join(tokens, d), d) == tokens,
{
    let s = split_join(tokens, d);
    let t0 = tokens[0];
    let r = tokens.drop_first();
    assert(free_of(t0, d));
    assert(s.subrange(0, t0.len() as int) =~= t0);
    if t0.len() < s.len() {
        assert(split_tail(r, d).len() > 0);
        assert(s[t0.len() as int] == split_tail(r, d)[0]);
    }
    lemma_collect_token(s, d, 0, t0);
    assert(s.subrange(t0.len() as int, s.len() as int) =~= split_tail(r, d));
    assert forall|k: int| 0 <= k < r.len() implies free_of(#[trigger] r[k], d) by {
        assert(r[k] == tokens[k + 1]);
    }
    lemma_split_loop_tail(s, d, t0.len() as int, seq![t0], r);
    assert(seq![t0] + r =~= tokens);
}

// ---------------------------------------------------------------------
// Decimal numbers below 256.
// ---------------------------------------------------------------------

/// The digits "serialize an integer" gives for `n` < 256.
pub proof fn lemma_serialize_byte(n: nat)
    requires
        n < 256,
    ensures
        n < 10 ==> serialize_integer(n) == seq![(0x30 + n) as u32],
        10 <= n < 100 ==> serialize_integer(n) == seq![(0x30 + n / 10) as u32, (0x30 + n % 10) as u32],
        100 <= n ==> serialize_integer(n) == seq![(0x30 + n / 100) as u32, (0x30 + (n / 10) % 10) as u32, (0x30 + n % 10) as u32],
{
    reveal_with_fuel(serialize_integer, 3);
    if n >= 10 {
        assert(n / 10 / 10 == n / 100);
        if n >= 100 {
            assert(serialize_integer(n / 10) =~= serialize_integer(n / 10 / 10) + seq![(0x30 + (n / 10) % 10) as u32]);
            assert(serialize_integer(n) =~= seq![(0x30 + n / 100) as u32, (0x30 + (n / 10) % 10) as u32, (0x30 + n % 10) as u32]);
        } else {
            assert(serialize_integer(n) =~= seq![(0x30 + n / 10) as u32, (0x30 + n % 10) as u32]);
        }
    }
}

/// The IPv4 number parser reads back a serialized byte, as decimal.
pub proof fn lemma_ipv4_number_parser_byte(n: nat)
    requires
        n < 256,
    ensures
        ipv4_number_parser(serialize_integer(n)) == Some((n, false)),
        free_of(serialize_integer(n), 0x2E),
        serialize_integer(n).len() > 0,
{
    lemma_serialize_byte(n);
    let s = serialize_integer(n);
    reveal_with_fuel(all_radix_digits, 4);
    reveal_with_fuel(radix_value, 4);
    if n < 10 {
        assert(s.drop_last() =~= Seq::<u32>::empty());
    } else if n < 100 {
        assert(s.drop_last() =~= seq![(0x30 + n / 10) as u32]);
        assert(s.drop_last().drop_last() =~= Seq::<u32>::empty());
    } else {
        assert(s.drop_last() =~= seq![(0x30 + n / 100) as u32, (0x30 + (n / 10) % 10) as u32]);
        assert(s.drop_last().drop_last() =~= seq![(0x30 + n / 100) as u32]);
        assert(s.drop_last().drop_last().drop_last() =~= Seq::<u32>::empty());
        assert((n / 100) * 10 + (n / 10) % 10 == n / 10);
    }
}

// ---------------------------------------------------------------------
// Serialize then parse is the identity on IPv4 addresses.
// ---------------------------------------------------------------------

/// The IPv4 serializer's output, as its four bytes' decimal forms joined
/// with ".".
pub proof fn lemma_ipv4_serializer_join(a: nat)
    ensures
        ipv4_serializer(a) == split_join(
            seq![
                serialize_integer((a / 256 / 256 / 256) % 256),
                serialize_integer((a / 256 / 256) % 256),
                serialize_integer((a / 256) % 256),
                serialize_integer(a % 256),
            ],
            0x2E,
        ),
{
    reveal_with_fuel(ipv4_serializer_loop, 5);
    reveal_with_fuel(split_tail, 4);
    let t0 = serialize_integer(a % 256);
    let t1 = serialize_integer((a / 256) % 256);
    let t2 = serialize_integer((a / 256 / 256) % 256);
    let t3 = serialize_integer((a / 256 / 256 / 256) % 256);
    let tokens = seq![t3, t2, t1, t0];
    assert(tokens.drop_first() =~= seq![t2, t1, t0]);
    assert(tokens.drop_first().drop_first() =~= seq![t1, t0]);
    assert(tokens.drop_first().drop_first().drop_first() =~= seq![t0]);
    assert(tokens.drop_first().drop_first().drop_first().drop_first() =~= Seq::<Seq<u32>>::empty());
    let dot = seq![0x2Eu32];
    assert(ipv4_serializer(a) =~= t3 + (dot + (t2 + (dot + (t1 + (dot + (t0 + seq![])))))));
    assert(split_join(tokens, 0x2E) =~= t3 + (dot + t2 + (dot + t1 + (dot + t0 + seq![]))));
}

/// URL §3 ("If that string is then parsed, the result will equal the host
/// that was serialized"), for IPv4 addresses: the IPv4 parser reads back
/// what the IPv4 serializer writes.
pub proof fn lemma_ipv4_serialize_parse(a: nat)
    requires
        a < 0x1_0000_0000,
    ensures
        ipv4_parser(ipv4_serializer(a)) == Some(a),
{
    let o0 = a % 256;
    let o1 = (a / 256) % 256;
    let o2 = (a / 256 / 256) % 256;
    let o3 = (a / 256 / 256 / 256) % 256;
    let tokens = seq![serialize_integer(o3), serialize_integer(o2), serialize_integer(o1), serialize_integer(o0)];
    lemma_ipv4_serializer_join(a);
    lemma_ipv4_number_parser_byte(o0);
    lemma_ipv4_number_parser_byte(o1);
    lemma_ipv4_number_parser_byte(o2);
    lemma_ipv4_number_parser_byte(o3);
    assert forall|k: int| 0 <= k < tokens.len() implies free_of(#[trigger] tokens[k], 0x2E) by {}
    lemma_strictly_split_join(tokens, 0x2E);
    let s = ipv4_serializer(a);
    assert(strictly_split(s, 0x2E) == tokens);
    reveal_with_fuel(ipv4_parse_parts, 5);
    assert(ipv4_parse_parts(tokens, 0, seq![]) == Some(seq![o3, o2, o1, o0])) by {
        assert(seq![o3] =~= Seq::<nat>::empty().push(o3));
        assert(seq![o3, o2] =~= seq![o3].push(o2));
        assert(seq![o3, o2, o1] =~= seq![o3, o2].push(o1));
        assert(seq![o3, o2, o1, o0] =~= seq![o3, o2, o1].push(o0));
    }
    let numbers = seq![o3, o2, o1, o0];
    reveal_with_fuel(any_greater_than_255, 4);
    reveal_with_fuel(pow256, 5);
    assert(pow256(1) == 256);
    assert(pow256(2) == 0x1_0000);
    assert(pow256(3) == 0x100_0000);
    let rest = numbers.drop_last();
    assert(rest =~= seq![o3, o2, o1]);
    reveal_with_fuel(ipv4_sum, 4);
    assert(ipv4_sum(rest, 3, o0 + o3 * 0x100_0000 + o2 * 0x1_0000 + o1 * 0x100) == o0 + o3 * 0x100_0000 + o2 * 0x1_0000 + o1 * 0x100);
    assert(o0 + o3 * 0x100_0000 + o2 * 0x1_0000 + o1 * 0x100 == a) by (nonlinear_arith)
        requires
            a < 0x1_0000_0000,
            o0 == a % 256,
            o1 == (a / 256) % 256,
            o2 == (a / 256 / 256) % 256,
            o3 == (a / 256 / 256 / 256) % 256,
    ;
}

// ---------------------------------------------------------------------
// Serialize then parse is the identity on IPv6 addresses.
// ---------------------------------------------------------------------

/// The IPv6 parser on step 7's input: what is left once the main loop has
/// run.
pub open spec fn ipv6_parser_after(looped: Option<(Seq<nat>, int, Option<int>)>) -> Option<Seq<nat>> {
    match looped {
        None => None,
        Some((address, piece_index, compress)) => match compress {
            Some(compress) => Some(ipv6_swaps(address, 7, compress, piece_index - compress)),
            None => if piece_index != 8 {
                None
            } else {
                Some(address)
            },
        },
    }
}

/// The text the IPv6 serializer writes for a compressed address.
pub open spec fn compressed_text(a: Seq<nat>, c: int) -> Seq<u32> {
    super::ipv6_text::hex_text_colons(a.subrange(0, c)) + (if c == 0 {
        seq![0x3Au32, 0x3A]
    } else {
        seq![0x3Au32]
    }) + super::ipv6_text::hex_text(a.subrange(c + super::ipv6_text::zero_run_len(a, c), 8))
}

/// On a compressed address's text, the IPv6 parser reaches the state just
/// after "::": the pieces before it written, pieceIndex and compress
/// `c + 1`.
pub proof fn lemma_ipv6_parse_reaches_compress(a: Seq<nat>, c: int)
    requires
        a.len() == 8,
        super::ipv6_text::all_pieces(a),
        0 <= c < 8,
    ensures
        ipv6_parser(compressed_text(a, c)) == ipv6_parser_after(
            ipv6_main_loop(
                compressed_text(a, c),
                super::ipv6_text::write(seq![0nat, 0, 0, 0, 0, 0, 0, 0], 0, a.subrange(0, c)),
                c + 1,
                Some(c + 1),
                compressed_text(a, c).len() - super::ipv6_text::hex_text(a.subrange(c + super::ipv6_text::zero_run_len(a, c), 8)).len(),
            ),
        ),
{
    use super::ipv6_text::*;
    let zeros8 = seq![0nat, 0, 0, 0, 0, 0, 0, 0];
    let s = compressed_text(a, c);
    let left = a.subrange(0, c);
    let colons = hex_text_colons(left);
    assert(all_pieces(left)) by {
        assert forall|k: int| 0 <= k < left.len() implies #[trigger] left[k] < 0x1_0000 by {
            assert(left[k] == a[k]);
        }
    }
    if c == 0 {
        assert(left =~= Seq::<nat>::empty());
        assert(colons =~= Seq::<u32>::empty());
        assert(s[0] == 0x3A && s[1] == 0x3A);
    } else {
        lemma_shortest_hex(a[0]);
        assert(colons =~= shortest_lowercase_hex(a[0]) + seq![0x3Au32] + hex_text_colons(left.drop_first()));
        assert(s[0] == shortest_lowercase_hex(a[0])[0]);
        assert(s.subrange(0, colons.len() as int) =~= colons);
        lemma_main_loop_colons(s, zeros8, 0, None, 0, left);
        assert(s[colons.len() as int] == 0x3A);
    }
}

/// The round trip for an address the serializer compresses at `c`.
pub proof fn lemma_ipv6_serialize_parse_compressed(a: Seq<nat>, c: int)
    requires
        a.len() == 8,
        super::ipv6_text::all_pieces(a),
        0 <= c < 8,
        a[c] == 0,
    ensures
        ipv6_parser(compressed_text(a, c)) == Some(a),
{
    use super::ipv6_text::*;
    let zeros8 = seq![0nat, 0, 0, 0, 0, 0, 0, 0];
    let s = compressed_text(a, c);
    let len = zero_run_len(a, c);
    lemma_zero_run(a, c);
    let left = a.subrange(0, c);
    let right = a.subrange(c + len, 8);
    let r = right.len() as int;
    let tail = hex_text(right);
    assert(all_pieces(right)) by {
        assert forall|k: int| 0 <= k < right.len() implies #[trigger] right[k] < 0x1_0000 by {
            assert(right[k] == a[c + len + k]);
        }
    }
    let w1 = write(zeros8, 0, left);
    lemma_write(zeros8, 0, left);
    let q = s.len() - tail.len();
    lemma_ipv6_parse_reaches_compress(a, c);
    let w2 = write(w1, c + 1, right);
    lemma_write(w1, c + 1, right);
    if r == 0 {
        assert(tail =~= Seq::<u32>::empty());
        assert(w2 == w1);
    } else {
        assert(s.subrange(q, q + tail.len()) =~= tail);
        lemma_main_loop_list(s, w1, c + 1, Some(c + 1), q, right);
    }
    assert(ipv6_parser(s) == Some(ipv6_swaps(w2, 7, c + 1, r)));
    lemma_ipv6_swaps(w2, 7, c + 1, r, right);
    let result = w2.subrange(0, c + 1) + Seq::new((8 - r - (c + 1)) as nat, |_i: int| 0nat) + right;
    assert(result =~= a) by {
        assert forall|k: int| 0 <= k < 8 implies #[trigger] result[k] == a[k] by {
            if k < c {
                assert(result[k] == w2[k]);
            } else if k < c + len {
                assert(a[k] == 0);
            } else {
                assert(right[k - (c + len)] == a[k]);
            }
        }
    }
}

/// URL §3 ("If that string is then parsed, the result will equal the host
/// that was serialized"), for IPv6 addresses: the IPv6 parser reads back
/// what the IPv6 serializer writes, for every address (eight pieces below
/// 2^16).
pub proof fn lemma_ipv6_serialize_parse(a: Seq<nat>)
    requires
        a.len() == 8,
        super::ipv6_text::all_pieces(a),
    ensures
        ipv6_parser(ipv6_serializer(a)) == Some(a),
{
    use super::ipv6_text::*;
    let zeros8 = seq![0nat, 0, 0, 0, 0, 0, 0, 0];
    let s = ipv6_serializer(a);
    lemma_ipv6_serializer_text(a);
    match find_ipv6_compressed_piece_index(a) {
        None => {
            lemma_shortest_hex(a[0]);
            assert(s == hex_text(a));
            assert(s[0] == shortest_lowercase_hex(a[0])[0]);
            assert(s.subrange(0, s.len() as int) =~= s);
            lemma_main_loop_list(s, zeros8, 0, None, 0, a);
            lemma_write(zeros8, 0, a);
            assert(write(zeros8, 0, a) =~= a);
        },
        Some(c) => {
            assert(s == compressed_text(a, c));
            lemma_ipv6_serialize_parse_compressed(a, c);
        },
    }
}

// ---------------------------------------------------------------------
// Serialize then parse, for hosts.
// ---------------------------------------------------------------------

/// URL §3's round trip for IP address hosts. An IPv6 host comes back for
/// every domain parser and either isOpaque. An IPv4 host's serialization
/// goes through the domain parser (host parser step 6), which
/// `clazel-idna` provides; for every domain parser that returns that serialization
/// unchanged (as URL §3.3 step 5 does for an ASCII string with no upper
/// case), the host comes back.
pub proof fn lemma_host_serialize_parse(host: Host, is_opaque: bool, domain_parser: DomainParser)
    requires
        host matches Host::Ipv6(a) ==> a.len() == 8 && super::ipv6_text::all_pieces(a),
        host matches Host::Ipv4(a) ==> a < 0x1_0000_0000 && !is_opaque && domain_parser(
            super::contract::host_parser_domain(host_serializer(host)),
            false,
        ) == Some(host_serializer(host)),
    ensures
        (host is Ipv6 || host is Ipv4) ==> host_parser(host_serializer(host), is_opaque, domain_parser) == Some(host),
{
    match host {
        Host::Ipv6(a) => {
            let s = host_serializer(host);
            let inner = ipv6_serializer(a);
            assert(s.subrange(1, s.len() - 1) =~= inner);
            assert(s[0] == 0x5B && s.last() == 0x5D);
            lemma_ipv6_serialize_parse(a);
        },
        Host::Ipv4(a) => {
            let s = ipv4_serializer(a);
            lemma_ipv4_serialize_parse(a);
            // s ends in a number: its last part is a decimal byte.
            let o0 = a % 256;
            let o1 = (a / 256) % 256;
            let o2 = (a / 256 / 256) % 256;
            let o3 = (a / 256 / 256 / 256) % 256;
            let tokens = seq![serialize_integer(o3), serialize_integer(o2), serialize_integer(o1), serialize_integer(o0)];
            lemma_ipv4_serializer_join(a);
            lemma_ipv4_number_parser_byte(o0);
            lemma_ipv4_number_parser_byte(o1);
            lemma_ipv4_number_parser_byte(o2);
            lemma_ipv4_number_parser_byte(o3);
            assert forall|k: int| 0 <= k < tokens.len() implies free_of(#[trigger] tokens[k], 0x2E) by {}
            lemma_strictly_split_join(tokens, 0x2E);
            lemma_serialize_byte(o0);
            reveal_with_fuel(contains_only_ascii_digits, 4);
            let t = serialize_integer(o0);
            if o0 < 10 {
                assert(t.drop_last() =~= Seq::<u32>::empty());
            } else if o0 < 100 {
                assert(t.drop_last().drop_last() =~= Seq::<u32>::empty());
            } else {
                assert(t.drop_last().drop_last().drop_last() =~= Seq::<u32>::empty());
            }
            assert(contains_only_ascii_digits(t));
            assert(ends_in_a_number(s));
            lemma_serialize_byte(o3);
            assert(s[0] == serialize_integer(o3)[0]);
            assert(s.len() > 0 && s[0] != 0x5B);
        },
        _ => {},
    }
}

// ---------------------------------------------------------------------
// The IPv6 parser returns eight 16-bit pieces.
// ---------------------------------------------------------------------

/// The bound on step 6.4's value after `length` hex digits.
pub open spec fn hex_bound(value: nat, length: nat) -> bool {
    &&& length <= 4
    &&& length == 0 ==> value == 0
    &&& length == 1 ==> value < 0x10
    &&& length == 2 ==> value < 0x100
    &&& length == 3 ==> value < 0x1000
    &&& length == 4 ==> value < 0x1_0000
}

/// Step 6.4 reads at most four hex digits, so its value is below 2^16.
pub proof fn lemma_ipv6_hex_digits_bound(input: Seq<u32>, start: int, value: nat, length: nat)
    requires
        hex_bound(value, length),
    ensures
        hex_bound(ipv6_hex_digits(input, start, value, length).0, ipv6_hex_digits(input, start, value, length).1),
        ipv6_hex_digits(input, start, value, length).0 < 0x1_0000,
        ipv6_hex_digits(input, start, value, length).1 >= length,
    decreases 4 - length
{
    if length < 4 {
        if let Some(c) = c_at(input, start + length) {
            if is_ascii_hex_digit(c) {
                lemma_ipv6_hex_digits_bound(input, start, value * 0x10 + hex_digit_value(c), length + 1);
            }
        }
    }
}

/// Step 6.5.5.4 keeps ipv4Piece at most 255.
pub proof fn lemma_ipv4_piece_digits_bound(input: Seq<u32>, pointer: int, piece: nat)
    requires
        piece <= 255,
    ensures
        ipv4_piece_digits(input, pointer, piece) matches Some((p, _q)) ==> p <= 255,
    decreases input.len() - pointer
{
    if let Some(c) = c_at(input, pointer) {
        if is_ascii_digit(c) && piece != 0 && piece * 10 + (c - 0x30) as nat <= 255 {
            lemma_ipv4_piece_digits_bound(input, pointer + 1, piece * 10 + (c - 0x30) as nat);
        }
    }
}

/// Eight pieces, each below 2^16.
pub open spec fn eight_pieces(a: Seq<nat>) -> bool {
    a.len() == 8 && super::ipv6_text::all_pieces(a)
}

/// Step 6.5.5 keeps eight 16-bit pieces, with zeros after pieceIndex.
pub proof fn lemma_ipv4_in_ipv6_bound(input: Seq<u32>, address: Seq<nat>, pi0: int, pi: int, ns: nat, pointer: int)
    requires
        eight_pieces(address),
        0 <= pi0 <= 6,
        ns <= 4,
        pi == pi0 + ns / 2,
        ns % 2 == 0 && pi < 8 ==> address[pi] == 0,
        ns % 2 == 1 ==> address[pi] <= 255,
        forall|k: int| pi < k < 8 ==> address[k] == 0,
    ensures
        ipv4_in_ipv6(input, address, pi, ns, pointer) matches Some((a, p, n)) ==> eight_pieces(a) && pi0 <= p <= 8
            && (n == 4 ==> forall|k: int| p <= k < 8 ==> a[k] == 0),
    decreases 4 - ns
{
    if let Some(c) = c_at(input, pointer) {
        if !(ns > 0 && !(c == 0x2E && ns < 4)) {
            let q = if ns > 0 {
                pointer + 1
            } else {
                pointer
            };
            if let Some(d) = c_at(input, q) {
                if is_ascii_digit(d) {
                    lemma_ipv4_piece_digits_bound(input, q + 1, (d - 0x30) as nat);
                    if let Some((piece, next)) = ipv4_piece_digits(input, q + 1, (d - 0x30) as nat) {
                        let value = address[pi] * 0x100 + piece;
                        assert(value < 0x1_0000);
                        let a2 = address.update(pi, value);
                        let ns2 = ns + 1;
                        let pi2 = if ns2 == 2 || ns2 == 4 {
                            pi + 1
                        } else {
                            pi
                        };
                        assert(super::ipv6_text::all_pieces(a2)) by {
                            assert forall|k: int| 0 <= k < a2.len() implies #[trigger] a2[k] < 0x1_0000 by {
                                if k != pi {
                                    assert(a2[k] == address[k]);
                                }
                            }
                        }
                        lemma_ipv4_in_ipv6_bound(input, a2, pi0, pi2, ns2, next);
                    }
                }
            }
        }
    }
}

/// The main loop keeps eight 16-bit pieces, with zeros after pieceIndex
/// and compress at most pieceIndex.
pub proof fn lemma_ipv6_main_loop_bound(input: Seq<u32>, address: Seq<nat>, pi: int, compress: Option<int>, pointer: int)
    requires
        eight_pieces(address),
        0 <= pi <= 8,
        forall|k: int| pi <= k < 8 ==> address[k] == 0,
        compress matches Some(c) ==> 0 <= c <= pi,
    ensures
        ipv6_main_loop(input, address, pi, compress, pointer) matches Some((a, p, c)) ==> eight_pieces(a) && 0 <= p <= 8
            && (c matches Some(c) ==> 0 <= c <= p),
    decreases input.len() - pointer
{
    if let Some(c) = c_at(input, pointer) {
        if pi != 8 {
            if c == 0x3A {
                if compress is None {
                    lemma_ipv6_main_loop_bound(input, address, pi + 1, Some(pi + 1), pointer + 1);
                }
            } else {
                lemma_ipv6_hex_digits_bound(input, pointer, 0, 0);
                let (value, length) = ipv6_hex_digits(input, pointer, 0, 0);
                let after = pointer + length;
                let a2 = address.update(pi, value);
                assert(super::ipv6_text::all_pieces(a2)) by {
                    assert forall|k: int| 0 <= k < a2.len() implies #[trigger] a2[k] < 0x1_0000 by {
                        if k != pi {
                            assert(a2[k] == address[k]);
                        }
                    }
                }
                if c_at(input, after) == Some(0x2Eu32) {
                    if length != 0 && pi <= 6 {
                        lemma_ipv4_in_ipv6_bound(input, address, pi, pi, 0, pointer);
                    }
                } else if c_at(input, after) == Some(0x3Au32) {
                    if c_at(input, after + 1) is Some {
                        lemma_ipv6_main_loop_bound(input, a2, pi + 1, compress, after + 1);
                    }
                }
            }
        }
    }
}

/// Step 7.3's swaps keep eight 16-bit pieces.
pub proof fn lemma_ipv6_swaps_bound(address: Seq<nat>, pi: int, compress: int, swaps: int)
    requires
        eight_pieces(address),
        0 <= pi <= 7,
        0 <= compress,
        compress + swaps <= pi + 1,
    ensures
        eight_pieces(ipv6_swaps(address, pi, compress, swaps)),
    decreases swaps
{
    if pi != 0 && swaps > 0 {
        let other = compress + swaps - 1;
        let a2 = address.update(pi, address[other]).update(other, address[pi]);
        assert(super::ipv6_text::all_pieces(a2)) by {
            assert forall|k: int| 0 <= k < a2.len() implies #[trigger] a2[k] < 0x1_0000 by {}
        }
        lemma_ipv6_swaps_bound(a2, pi - 1, compress, swaps - 1);
    }
}

/// The IPv6 parser only returns IPv6 addresses (§3.1: "a list of 8
/// 16-bit unsigned integers").
pub proof fn lemma_ipv6_parser_pieces(input: Seq<u32>)
    ensures
        ipv6_parser(input) matches Some(a) ==> eight_pieces(a),
{
    let zeros8 = seq![0nat, 0, 0, 0, 0, 0, 0, 0];
    assert(eight_pieces(zeros8)) by {
        assert forall|k: int| 0 <= k < 8 implies #[trigger] zeros8[k] < 0x1_0000 by {}
    }
    lemma_ipv6_main_loop_bound(input, zeros8, 1, Some(1), 2);
    lemma_ipv6_main_loop_bound(input, zeros8, 0, None, 0);
    let looped = if c_at(input, 0) == Some(0x3Au32) {
        if c_at(input, 1) != Some(0x3Au32) {
            None
        } else {
            ipv6_main_loop(input, zeros8, 1, Some(1), 2)
        }
    } else {
        ipv6_main_loop(input, zeros8, 0, None, 0)
    };
    if let Some((address, piece_index, compress)) = looped {
        if let Some(c) = compress {
            if piece_index <= 8 {
                lemma_ipv6_swaps_bound(address, 7, c, piece_index - c);
            }
        }
    }
}

} // verus!
