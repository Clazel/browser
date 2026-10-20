//! The executable IPv4 number parser, ends in a number checker and IPv4
//! parser (URL §3.5), and Infra's strictly split, proven to meet
//! [`super::contract`]. Each loop mirrors its spec function; the step
//! comments live in [`super::spec`].

use super::record::at32;
#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Infra "collect a sequence of code points" not equal to `delimiter`,
/// from `position`.
fn collect_not_equal_exec(input: &[u32], delimiter: u32, position: usize) -> (token: Vec<u32>)
    requires
        position <= input.len(),
    ensures
        token@ == collect_not_equal(input@, delimiter, position as nat),
{
    let mut token: Vec<u32> = Vec::new();
    let mut i = position;
    assert(token@ + collect_not_equal(input@, delimiter, i as nat) =~= collect_not_equal(input@, delimiter, position as nat));
    while i < input.len() && at32(input, i) != delimiter
        invariant
            position <= i <= input.len(),
            collect_not_equal(input@, delimiter, position as nat) == token@ + collect_not_equal(input@, delimiter, i as nat),
        decreases input.len() - i,
    {
        let ghost before = token@;
        token.push(at32(input, i));
        i = i.saturating_add(1);
        assert(before + collect_not_equal(input@, delimiter, (i - 1) as nat) =~= token@ + collect_not_equal(input@, delimiter, i as nat));
    }
    assert(token@ + collect_not_equal(input@, delimiter, i as nat) =~= token@);
    token
}

/// Infra "strictly split" `input` on `delimiter`.
pub fn strictly_split_exec(input: &[u32], delimiter: u32) -> (parts: Vec<Vec<u32>>)
    ensures
        super::record::parts_view(parts@) == strictly_split(input@, delimiter),
{
    let token = collect_not_equal_exec(input, delimiter, 0);
    proof {
        super::termination::lemma_collect_not_equal_len(input@, delimiter, 0);
    }
    let mut position = token.len();
    let mut tokens: Vec<Vec<u32>> = Vec::new();
    tokens.push(token);
    assert(super::record::parts_view(tokens@) =~= seq![collect_not_equal(input@, delimiter, 0)]);
    while position < input.len()
        invariant
            position <= input.len(),
            strictly_split(input@, delimiter) == strictly_split_loop(input@, delimiter, position as nat, super::record::parts_view(tokens@)),
        decreases input.len() - position,
    {
        let ghost before = super::record::parts_view(tokens@);
        // Never saturates: position < input.len().
        let next = position.saturating_add(1);
        let token = collect_not_equal_exec(input, delimiter, next);
        proof {
            super::termination::lemma_collect_not_equal_len(input@, delimiter, next as nat);
        }
        let ghost token_view = token@;
        // Never saturates: the token ends within the input.
        position = next.saturating_add(token.len());
        tokens.push(token);
        assert(super::record::parts_view(tokens@) =~= before.push(token_view));
    }
    tokens
}

/// The value of an ASCII hex digit.
pub fn hex_value(c: u32) -> (v: u64)
    requires
        is_ascii_hex_digit(c),
    ensures
        v as nat == hex_digit_value(c),
        v < 16,
{
    // Never saturate: each branch's range is above its offset.
    if c <= 0x39 {
        (c as u64).saturating_sub(0x30)
    } else if c <= 0x46 {
        (c as u64).saturating_sub(0x37)
    } else {
        (c as u64).saturating_sub(0x57)
    }
}

/// Whether `c` is an ASCII hex digit.
pub fn is_hex(c: u32) -> (r: bool)
    ensures
        r == is_ascii_hex_digit(c),
{
    (0x30..=0x39).contains(&c) || (0x41..=0x46).contains(&c) || (0x61..=0x66).contains(&c)
}

/// The IPv4 number parser (URL §3.5), with the number saturated at 2^32.
pub fn ipv4_number_parser(input: &[u32]) -> (output: Option<(u64, bool)>)
    ensures
        super::contract::ipv4_number_parser_ensures(input@, output),
{
    if input.is_empty() {
        return None;
    }
    let (validation_error, start, r): (bool, usize, u64) = if input.len() >= 2 && at32(input, 0) == 0x30 && (at32(input, 1)
        == 0x58 || at32(input, 1) == 0x78) {
        (true, 2, 16)
    } else if input.len() >= 2 && at32(input, 0) == 0x30 {
        (true, 1, 8)
    } else {
        (false, 0, 10)
    };
    let ghost rest = input@.subrange(start as int, input.len() as int);
    assert(input@.subrange(0, input.len() as int) =~= input@);
    if start == input.len() {
        return Some((0, true));
    }
    let mut value: u64 = 0;
    let mut i = start;
    assert(rest.subrange(0, 0) =~= Seq::<u32>::empty());
    assert(super::spec::ipv4_number_parser(input@) == if all_radix_digits(rest, r as nat) {
        Some((radix_value(rest, r as nat), validation_error))
    } else {
        None
    });
    while i < input.len()
        invariant
            super::spec::ipv4_number_parser(input@) == if all_radix_digits(rest, r as nat) {
                Some((radix_value(rest, r as nat), validation_error))
            } else {
                None
            },
            start <= i <= input.len(),
            start < input.len(),
            rest == input@.subrange(start as int, input.len() as int),
            8 <= r <= 16,
            all_radix_digits(rest.subrange(0, i - start), r as nat),
            value as nat == super::contract::saturate_u32(radix_value(rest.subrange(0, i - start), r as nat)),
        decreases input.len() - i,
    {
        let c = at32(input, i);
        let ghost prefix = rest.subrange(0, i - start);
        let ghost next = rest.subrange(0, i - start + 1);
        assert(next.drop_last() =~= prefix);
        assert(next.last() == c);
        if !(is_hex(c) && hex_value(c) < r) {
            proof {
                super::lemmas::lemma_all_radix_digits_index(rest, r as nat, i - start);
            }
            return None;
        }
        let d = hex_value(c);
        proof {
            super::lemmas::lemma_saturate_step(radix_value(prefix, r as nat), r as nat, d as nat);
        }
        // Never saturate: value <= 2^32, r <= 16, d < 16.
        let t = value.saturating_mul(r).saturating_add(d);
        assert(t as nat == value as nat * r as nat + d as nat) by (nonlinear_arith)
            requires
                value <= 0x1_0000_0000u64,
                r <= 16,
                d < 16,
                t == value.saturating_mul(r).saturating_add(d),
        ;
        value = if t > 0xFFFF_FFFF {
            0x1_0000_0000
        } else {
            t
        };
        i = i.saturating_add(1);
    }
    assert(rest.subrange(0, i - start) =~= rest);
    Some((value, validation_error))
}

/// Whether `s` contains only ASCII digits.
fn contains_only_ascii_digits_exec(s: &[u32]) -> (r: bool)
    ensures
        r == contains_only_ascii_digits(s@),
{
    let mut i: usize = 0;
    assert(s@.subrange(0, 0) =~= Seq::<u32>::empty());
    while i < s.len()
        invariant
            i <= s.len(),
            contains_only_ascii_digits(s@.subrange(0, i as int)),
        decreases s.len() - i,
    {
        let c = at32(s, i);
        assert(s@.subrange(0, i + 1).drop_last() =~= s@.subrange(0, i as int));
        if !(0x30..=0x39).contains(&c) {
            proof {
                super::lemmas::lemma_contains_only_ascii_digits_index(s@, i as int);
            }
            return false;
        }
        i = i.saturating_add(1);
    }
    assert(s@.subrange(0, s.len() as int) =~= s@);
    true
}

/// The length of the last element of `parts`, which is non-empty.
fn last_len(parts: &[Vec<u32>]) -> (n: usize)
    requires
        parts.len() > 0,
    ensures
        n == super::record::parts_view(parts@).last().len(),
{
    // Never saturates: parts.len() > 0.
    match parts.get(parts.len().saturating_sub(1)) {
        Some(last) => last.len(),
        // Unreachable: the index is below parts.len().
        None => 0,
    }
}

/// `256^(5 - size)` for a size of 1 to 4 (IPv4 parser step 9).
fn pow256_five_minus(size: usize) -> (p: u64)
    requires
        1 <= size <= 4,
    ensures
        p as nat == pow256((5 - size) as nat),
        p <= 0x1_0000_0000,
{
    reveal_with_fuel(pow256, 5);
    if size == 1 {
        0x1_0000_0000
    } else if size == 2 {
        0x100_0000
    } else if size == 3 {
        0x1_0000
    } else {
        0x100
    }
}

/// `256^(3 - counter)` for a counter of 0 to 2 (IPv4 parser step 13.1).
fn pow256_three_minus(counter: usize) -> (p: u64)
    requires
        counter <= 2,
    ensures
        p as nat == pow256((3 - counter) as nat),
        p <= 0x100_0000,
{
    reveal_with_fuel(pow256, 4);
    if counter == 0 {
        0x100_0000
    } else if counter == 1 {
        0x1_0000
    } else {
        0x100
    }
}

/// The ends in a number checker (URL §3.5).
pub fn ends_in_a_number(input: &[u32]) -> (output: bool)
    requires
        super::contract::ends_in_a_number_requires(input@),
    ensures
        super::contract::ends_in_a_number_ensures(input@, output),
{
    let mut parts = strictly_split_exec(input, 0x2E);
    proof {
        super::lemmas::lemma_strictly_split_shape(input@, 0x2E);
    }
    let ghost all = super::record::parts_view(parts@);
    if last_len(parts.as_slice()) == 0 {
        parts.pop();
        assert(super::record::parts_view(parts@) =~= all.drop_last());
    }
    let ghost kept = super::record::parts_view(parts@);
    // Never saturates: parts is still non-empty (lemma_strictly_split_shape).
    match parts.get(parts.len().saturating_sub(1)) {
        Some(last) => {
            assert(last@ == kept.last());
            if !last.is_empty() && contains_only_ascii_digits_exec(last.as_slice()) {
                true
            } else {
                ipv4_number_parser(last.as_slice()).is_some()
            }
        },
        // Unreachable: the index is below parts.len().
        None => false,
    }
}

/// The IPv4 parser (URL §3.5).
pub fn ipv4_parser(input: &[u32]) -> (output: Option<u32>)
    ensures
        super::contract::ipv4_parser_ensures(input@, output),
{
    let mut parts = strictly_split_exec(input, 0x2E);
    proof {
        super::lemmas::lemma_strictly_split_shape(input@, 0x2E);
    }
    let ghost all = super::record::parts_view(parts@);
    if last_len(parts.as_slice()) == 0 && parts.len() > 1 {
        parts.pop();
        assert(super::record::parts_view(parts@) =~= all.drop_last());
    }
    let ghost pv = super::record::parts_view(parts@);
    assert(pv == super::lemmas::ipv4_parser_parts(input@));
    if parts.len() > 4 {
        return None;
    }
    let mut numbers: Vec<u64> = Vec::new();
    let ghost mut exact: Seq<nat> = seq![];
    let mut i: usize = 0;
    while i < parts.len()
        invariant
            i <= parts.len(),
            1 <= parts.len() <= 4,
            pv == super::lemmas::ipv4_parser_parts(input@),
            pv.len() <= 4,
            pv == super::record::parts_view(parts@),
            exact.len() == i,
            numbers@.len() == i,
            forall|k: int| 0 <= k < i ==> (#[trigger] numbers@[k]) as nat == super::contract::saturate_u32(exact[k]),
            ipv4_parse_parts(pv, 0, seq![]) == ipv4_parse_parts(pv, i as nat, exact),
        decreases parts.len() - i,
    {
        let part = parts.get(i)?;
        assert(part@ == pv[i as int]);
        match ipv4_number_parser(part.as_slice()) {
            None => {
                return None;
            },
            Some((n, _)) => {
                let ghost result = super::spec::ipv4_number_parser(pv[i as int]);
                proof {
                    exact = exact.push(result.unwrap().0);
                }
                numbers.push(n);
            },
        }
        i = i.saturating_add(1);
    }
    proof {
        super::lemmas::lemma_ipv4_parse_parts_done(pv, exact);
    }
    let size = numbers.len();
    // Never saturates: size >= 1.
    let last_index = size.saturating_sub(1);
    // 8.
    let mut k: usize = 0;
    while k < last_index
        invariant
            k <= last_index,
            pv == super::lemmas::ipv4_parser_parts(input@),
            pv.len() <= 4,
            ipv4_parse_parts(pv, 0, seq![]) == Some(exact),
            last_index + 1 == size,
            size == numbers@.len(),
            exact.len() == size,
            forall|q: int| 0 <= q < size ==> (#[trigger] numbers@[q]) as nat == super::contract::saturate_u32(exact[q]),
            forall|q: int| 0 <= q < k ==> (#[trigger] exact[q]) <= 255,
            any_greater_than_255(exact, 0, last_index as nat) == any_greater_than_255(exact, k as nat, last_index as nat),
        decreases last_index - k,
    {
        let n = *numbers.get(k)?;
        assert(numbers@[k as int] == n);
        if n > 255 {
            return None;
        }
        k = k.saturating_add(1);
    }
    // 9.
    let last = *numbers.get(last_index)?;
    assert(numbers@[last_index as int] == last);
    if last >= pow256_five_minus(size) {
        return None;
    }
    // 10. to 13.
    let mut ipv4: u64 = last;
    let mut counter: usize = 0;
    let ghost rest = exact.drop_last();
    assert(exact.last() == exact[last_index as int]);
    assert(exact.last() == last as nat);
    while counter < last_index
        invariant
            pv == super::lemmas::ipv4_parser_parts(input@),
            pv.len() <= 4,
            ipv4_parse_parts(pv, 0, seq![]) == Some(exact),
            counter <= last_index,
            last_index + 1 == size,
            size <= 4,
            size == numbers@.len(),
            exact.len() == size,
            rest == exact.drop_last(),
            forall|q: int| 0 <= q < size ==> (#[trigger] numbers@[q]) as nat == super::contract::saturate_u32(exact[q]),
            forall|q: int| 0 <= q < last_index ==> (#[trigger] exact[q]) <= 255,
            ipv4 <= 0x1_0000_0000 * (counter + 1),
            ipv4_sum(rest, 0, exact.last()) == ipv4_sum(rest, counter as nat, ipv4 as nat),
        decreases last_index - counter,
    {
        let n = *numbers.get(counter)?;
        assert(n as nat == exact[counter as int]);
        let p = pow256_three_minus(counter);
        // Never saturate: n <= 255, p <= 2^24, ipv4 <= 2^34.
        let term = n.saturating_mul(p);
        assert(term == n * p && term <= 0xFF00_0000) by (nonlinear_arith)
            requires
                n <= 255,
                p <= 0x100_0000,
                term == n.saturating_mul(p),
        ;
        ipv4 = ipv4.saturating_add(term);
        counter = counter.saturating_add(1);
    }
    proof {
        super::lemmas::lemma_ipv4_parser_32_bit(input@);
    }
    Some(ipv4 as u32)
}

} // verus!
