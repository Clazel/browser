//! The pattern matching algorithm (MIME Sniffing §6), and the helpers the
//! other exec sniffing modules share. Each is proven against
//! [`super::contract`] or its spec definition.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;
use crate::mime_type::record::MimeType;

verus! {

/// Is `b` a binary data byte (§3)?
pub fn is_binary_data_byte_exec(b: u8) -> (r: bool)
    ensures
        r == is_binary_data_byte(b),
{
    b <= 0x08 || b == 0x0B || (0x0E..=0x1A).contains(&b) || (0x1C..=0x1F).contains(&b)
}

/// Is `b` a whitespace byte (§3)?
pub fn is_whitespace_byte_exec(b: u8) -> (r: bool)
    ensures
        r == is_whitespace_byte(b),
{
    b == 0x09 || b == 0x0A || b == 0x0C || b == 0x0D || b == 0x20
}

/// `contains_binary_data_byte(bytes.drop(i))` is `contains_binary_data_byte`
/// of what is left from `i`, one byte at a time.
proof fn lemma_contains_binary_step(bytes: Seq<u8>, i: int)
    requires
        0 <= i < bytes.len(),
    ensures
        contains_binary_data_byte(bytes.subrange(i, bytes.len() as int)) == (is_binary_data_byte(bytes[i])
            || contains_binary_data_byte(bytes.subrange(i + 1, bytes.len() as int))),
{
    assert(bytes.subrange(i, bytes.len() as int).drop_first() =~= bytes.subrange(i + 1, bytes.len() as int));
}

/// Does `bytes` contain a binary data byte (§3)?
pub fn contains_binary_data_byte_exec(bytes: &[u8]) -> (r: bool)
    ensures
        r == contains_binary_data_byte(bytes@),
{
    let mut i: usize = 0;
    assert(bytes@.subrange(0, bytes.len() as int) =~= bytes@);
    while i < bytes.len()
        invariant
            i <= bytes.len(),
            contains_binary_data_byte(bytes@) == contains_binary_data_byte(bytes@.subrange(i as int, bytes.len() as int)),
        decreases bytes.len() - i,
    {
        proof {
            lemma_contains_binary_step(bytes@, i as int);
        }
        if let Some(b) = bytes.get(i) {
            if is_binary_data_byte_exec(*b) {
                return true;
            }
        }
        // Never saturates: i < bytes.len().
        i = i.saturating_add(1);
    }
    false
}

/// "ignored contains `b`".
fn ignored_contains_exec(ignored: &Ignored, b: u8) -> (r: bool)
    ensures
        r == ignored_contains(*ignored, b),
{
    match ignored {
        Ignored::None => false,
        Ignored::WhitespaceBytes => is_whitespace_byte_exec(b),
    }
}

/// Is `input[s]` a byte that `ignored` contains?
fn ignored_at(input: &[u8], s: usize, ignored: &Ignored) -> (r: bool)
    requires
        s < input.len(),
    ensures
        r == ignored_contains(*ignored, input@[s as int]),
{
    match input.get(s) {
        Some(b) => ignored_contains_exec(ignored, *b),
        None => false,
    }
}

/// The pattern matching algorithm (§6, #pattern-matching-algorithm).
pub fn pattern_matching(input: &[u8], pattern: &[u8], mask: &[u8], ignored: Ignored) -> (r: bool)
    requires
        super::contract::pattern_matching_requires(pattern@, mask@),
    ensures
        super::contract::pattern_matching_ensures(input@, pattern@, mask@, ignored, r),
{
    // 1. "Assert: pattern's length is equal to mask's length." (requires)
    // 2. "If input's length is less than pattern's length, return false."
    if input.len() < pattern.len() {
        return false;
    }
    // 3. "Let s be 0."
    let mut s: usize = 0;
    // 4. "While s < input's length:" 4.1 "If ignored does not contain
    //    input[s], break." 4.2 "Set s to s + 1."
    while s < input.len() && ignored_at(input, s, &ignored)
        invariant
            s <= input.len(),
            skip_ignored(input@, 0, ignored) == skip_ignored(input@, s as nat, ignored),
        decreases input.len() - s,
    {
        // Never saturates: s < input.len().
        s = s.saturating_add(1);
    }
    let ghost start = s as nat;
    assert(skip_ignored(input@, s as nat, ignored) == s);
    // 5. "Let p be 0."
    let mut p: usize = 0;
    // 6. "While p < pattern's length:"
    while p < pattern.len()
        invariant
            p <= pattern.len(),
            pattern.len() == mask.len(),
            start == skip_ignored(input@, 0, ignored),
            compare_pattern(input@, pattern@, mask@, start, 0) == compare_pattern(input@, pattern@, mask@, s as nat, p as nat),
        decreases pattern.len() - p,
    {
        // Erratum (see spec.rs): no byte past the end of input matches.
        if s >= input.len() {
            return false;
        }
        let data = match input.get(s) {
            Some(b) => *b,
            None => return false,
        };
        let m = match mask.get(p) {
            Some(m) => *m,
            None => return false,
        };
        let q = match pattern.get(p) {
            Some(q) => *q,
            None => return false,
        };
        assert(data == input@[s as int] && m == mask@[p as int] && q == pattern@[p as int]);
        // 6.1 "Let maskedData be the result of applying the bitwise AND
        //     operator to input[s] and mask[p]."
        // 6.2 "If maskedData is not equal to pattern[p], return false."
        if data & m != q {
            return false;
        }
        assert(p < pattern@.len() && s < input@.len() && (input@[s as int] & mask@[p as int]) == pattern@[p as int]);
        assert(compare_pattern(input@, pattern@, mask@, s as nat, p as nat)
            == compare_pattern(input@, pattern@, mask@, s as nat + 1, p as nat + 1));
        // 6.3 "Set s to s + 1." 6.4 "Set p to p + 1." Never saturate: s <
        // input.len(), p < pattern.len().
        s = s.saturating_add(1);
        p = p.saturating_add(1);
    }
    // 7. "Return true."
    true
}

/// The MIME type the standard writes as the literal `type_/subtype`.
pub fn mime_literal(type_: &[u32], subtype: &[u32]) -> (m: MimeType)
    ensures
        m@ == mime_type(type_@, subtype@),
{
    let m = MimeType {
        type_: vstd::slice::slice_to_vec(type_),
        subtype: vstd::slice::slice_to_vec(subtype),
        parameters: Vec::new(),
    };
    assert(m@.parameters =~= Seq::<(Seq<u32>, Seq<u32>)>::empty());
    m
}

/// One row of a table: "Let patternMatched be the result of the pattern
/// matching algorithm given input, [the row's first three columns]",
/// where `table[i]` is that row.
pub fn row_matches(input: &[u8], pattern: &[u8], mask: &[u8], ignored: Ignored, Ghost(table): Ghost<Seq<Row>>, Ghost(i): Ghost<nat>) -> (r: bool)
    requires
        i < table.len(),
        table[i as int].pattern == pattern@,
        table[i as int].mask == mask@,
        table[i as int].ignored == ignored,
        pattern@.len() == mask@.len(),
    ensures
        r ==> match_table(input@, table, i) == Some(table[i as int].computed),
        !r ==> match_table(input@, table, i) == match_table(input@, table, i + 1),
{
    pattern_matching(input, pattern, mask, ignored)
}

} // verus!
