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

} // verus!
