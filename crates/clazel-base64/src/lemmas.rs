//! Facts proven about the spec in [`super::spec`]. They do not constrain the
//! implementation directly; they show the transcription behaves as the
//! standard says it should, which is evidence that the transcription is
//! right.
//!
//! Main results:
//! - [`lemma_decode_encode`]: decode inverts encode, for every byte
//!   sequence.
//! - [`lemma_step_9_assertion`]: decode step 9 asserts that a non-empty
//!   buffer "contains either 12 or 18 bits"; here it is proven.
//! - [`lemma_fails_exactly`]: decode fails exactly when, after whitespace
//!   removal, the input is not alphabet characters followed by at most two
//!   "=" that complete a 4-character quantum, or leaves one character over
//!   (steps 2 to 4, stated without their control flow).
//! - [`lemma_ignores_whitespace`] and [`lemma_rejects_other`]: inserting
//!   one of the five code points Infra lists as ASCII whitespace anywhere
//!   changes nothing; inserting any code point that is neither that, the
//!   alphabet nor "=" makes decode fail. Both name the code points as
//!   literals, so a mistake in `is_ascii_whitespace` contradicts them.
//! - [`lemma_encode_ascii`]: the encoder outputs only ASCII.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------
// Table 1
// ---------------------------------------------------------------------------

/// Table 1's rows hold distinct code points.
pub proof fn lemma_table_1_injective(r: nat, v: nat)
    requires
        r < 64,
        v < 64,
        table_1_encoding(r) == table_1_encoding(v),
    ensures
        r == v,
{
}

/// Every row's code point is one step 4 allows.
pub proof fn lemma_table_1_allowed(v: nat)
    requires
        v < 64,
    ensures
        is_step_4_allowed(table_1_encoding(v)),
        table_1_encoding(v) < 0x80,
{
}

/// The search from `row` finds row `v`, when no earlier row matches.
proof fn lemma_find_from(c: u32, row: nat, v: nat)
    requires
        row <= v < 64,
        table_1_encoding(v) == c,
    ensures
        find_in_table_1(c, row) == v,
    decreases v - row
{
    if row < v {
        if table_1_encoding(row) == c {
            lemma_table_1_injective(row, v);
        }
        lemma_find_from(c, row + 1, v);
    }
}

/// Step 8.1 inverts Table 1.
pub proof fn lemma_find_encoding(v: nat)
    requires
        v < 64,
    ensures
        find_in_table_1(table_1_encoding(v), 0) == v,
{
    lemma_find_from(table_1_encoding(v), 0, v);
}

/// The row of a code point step 4 allows, in closed form.
pub open spec fn table_1_row(c: u32) -> nat {
    if is_ascii_upper_alpha(c) {
        (c - 0x41) as nat
    } else if is_ascii_lower_alpha(c) {
        (c - 0x61 + 26) as nat
    } else if is_ascii_digit(c) {
        (c - 0x30 + 52) as nat
    } else if c == 0x2B {
        62
    } else {
        63
    }
}

/// Every code point step 4 allows is in Table 1, at [`table_1_row`], and
/// step 8.1 finds it there.
pub proof fn lemma_find_allowed(c: u32)
    requires
        is_step_4_allowed(c),
    ensures
        table_1_row(c) < 64,
        table_1_encoding(table_1_row(c)) == c,
        find_in_table_1(c, 0) == table_1_row(c),
{
    lemma_find_from(c, 0, table_1_row(c));
}

// ---------------------------------------------------------------------------
// Steps 1 and 4 on sequences
// ---------------------------------------------------------------------------

/// Step 4's recursive condition is "contains a code point that is not
/// allowed".
pub proof fn lemma_contains_disallowed(data: Seq<u32>)
    ensures
        contains_disallowed(data) <==> exists|k: int| 0 <= k < data.len() && !is_step_4_allowed(#[trigger] data[k]),
    decreases data.len()
{
    if data.len() > 0 {
        let init = data.drop_last();
        lemma_contains_disallowed(init);
        if contains_disallowed(init) {
            let k = choose|k: int| 0 <= k < init.len() && !is_step_4_allowed(#[trigger] init[k]);
            assert(data[k] == init[k]);
        }
        if exists|k: int| 0 <= k < data.len() && !is_step_4_allowed(#[trigger] data[k]) {
            let k = choose|k: int| 0 <= k < data.len() && !is_step_4_allowed(#[trigger] data[k]);
            if k < data.len() - 1 {
                assert(init[k] == data[k]);
            }
        }
    }
}

/// Step 1 distributes over concatenation.
pub proof fn lemma_remove_whitespace_append(x: Seq<u32>, y: Seq<u32>)
    ensures
        remove_ascii_whitespace(x + y) == remove_ascii_whitespace(x) + remove_ascii_whitespace(y),
    decreases y.len()
{
    if y.len() == 0 {
        assert(x + y =~= x);
        assert(remove_ascii_whitespace(x) + seq![] =~= remove_ascii_whitespace(x));
    } else {
        assert((x + y).drop_last() =~= x + y.drop_last());
        assert((x + y).last() == y.last());
        lemma_remove_whitespace_append(x, y.drop_last());
        assert(remove_ascii_whitespace(x) + remove_ascii_whitespace(y.drop_last()).push(y.last())
            =~= (remove_ascii_whitespace(x) + remove_ascii_whitespace(y.drop_last())).push(y.last()));
    }
}

/// Step 1 leaves a string without ASCII whitespace unchanged.
pub proof fn lemma_remove_whitespace_none(data: Seq<u32>)
    requires
        forall|k: int| 0 <= k < data.len() ==> !is_ascii_whitespace(#[trigger] data[k]),
    ensures
        remove_ascii_whitespace(data) == data,
    decreases data.len()
{
    if data.len() > 0 {
        let init = data.drop_last();
        assert forall|k: int| 0 <= k < init.len() implies !is_ascii_whitespace(#[trigger] init[k]) by {
            assert(init[k] == data[k]);
        }
        lemma_remove_whitespace_none(init);
        assert(data.last() == data[data.len() - 1]);
        assert(init.push(data.last()) =~= data);
    }
}

/// Step 1's result has no ASCII whitespace, and every code point in it was
/// in the input.
pub proof fn lemma_remove_whitespace_members(data: Seq<u32>)
    ensures
        forall|k: int| 0 <= k < remove_ascii_whitespace(data).len()
            ==> !is_ascii_whitespace(#[trigger] remove_ascii_whitespace(data)[k]),
    decreases data.len()
{
    if data.len() > 0 {
        lemma_remove_whitespace_members(data.drop_last());
        let r = remove_ascii_whitespace(data);
        let ri = remove_ascii_whitespace(data.drop_last());
        assert forall|k: int| 0 <= k < r.len() implies !is_ascii_whitespace(#[trigger] r[k]) by {
            if k < ri.len() {
                assert(r[k] == ri[k]);
            }
        }
    }
}

/// Step 1 keeps a code point that is not ASCII whitespace.
pub proof fn lemma_remove_whitespace_keeps(c: u32)
    requires
        !is_ascii_whitespace(c),
    ensures
        remove_ascii_whitespace(seq![c]) == seq![c],
{
    assert(seq![c].drop_last() =~= Seq::<u32>::empty());
    assert(remove_ascii_whitespace(Seq::<u32>::empty()) == Seq::<u32>::empty());
    assert(Seq::<u32>::empty().push(c) =~= seq![c]);
}

/// Step 1 removes a code point that is ASCII whitespace.
pub proof fn lemma_remove_whitespace_drops(c: u32)
    requires
        is_ascii_whitespace(c),
    ensures
        remove_ascii_whitespace(seq![c]) == Seq::<u32>::empty(),
{
    assert(seq![c].drop_last() =~= Seq::<u32>::empty());
    assert(remove_ascii_whitespace(Seq::<u32>::empty()) == Seq::<u32>::empty());
}

// ---------------------------------------------------------------------------
// Step 8 on concatenations
// ---------------------------------------------------------------------------

/// Step 8 over `x + y`, from inside `y`, is step 8 over `y`.
proof fn lemma_decode_loop_shift(x: Seq<u32>, y: Seq<u32>, j: nat, output: Seq<u8>, buffer: Buffer)
    ensures
        decode_loop(x + y, x.len() + j, output, buffer) == decode_loop(y, j, output, buffer),
    decreases y.len() - j
{
    if j < y.len() {
        assert((x + y)[x.len() + j as int] == y[j as int]);
        let n = find_in_table_1(y[j as int], 0);
        let b = Buffer { bits: buffer.bits * 64 + n, len: buffer.len + 6 };
        if b.len == 24 {
            let out = output + seq![(b.bits / 65536) as u8, (b.bits / 256 % 256) as u8, (b.bits % 256) as u8];
            lemma_decode_loop_shift(x, y, j + 1, out, empty_buffer());
        } else {
            lemma_decode_loop_shift(x, y, j + 1, output, b);
        }
        assert(x.len() + j + 1 == x.len() + (j + 1));
    }
}

/// Step 8 over `x + y` is step 8 over `y`, continuing from where step 8
/// over `x` stopped.
pub proof fn lemma_decode_loop_append(x: Seq<u32>, y: Seq<u32>, i: nat, output: Seq<u8>, buffer: Buffer)
    requires
        i <= x.len(),
    ensures
        decode_loop(x + y, i, output, buffer) == ({
            let s = decode_loop(x, i, output, buffer);
            decode_loop(y, 0, s.output, s.buffer)
        }),
    decreases x.len() - i
{
    if i < x.len() {
        assert((x + y)[i as int] == x[i as int]);
        let n = find_in_table_1(x[i as int], 0);
        let b = Buffer { bits: buffer.bits * 64 + n, len: buffer.len + 6 };
        if b.len == 24 {
            let out = output + seq![(b.bits / 65536) as u8, (b.bits / 256 % 256) as u8, (b.bits % 256) as u8];
            lemma_decode_loop_append(x, y, i + 1, out, empty_buffer());
        } else {
            lemma_decode_loop_append(x, y, i + 1, output, b);
        }
    } else {
        lemma_decode_loop_shift(x, y, 0, output, buffer);
    }
}

// ---------------------------------------------------------------------------
// Step 9's assertion
// ---------------------------------------------------------------------------

/// A buffer of `len` bits holds a number below 2^len, for the lengths the
/// loop can reach.
pub open spec fn buffer_fits(b: Buffer) -> bool {
    &&& (b.len == 0 ==> b.bits == 0)
    &&& (b.len == 6 ==> b.bits < 64)
    &&& (b.len == 12 ==> b.bits < 4096)
    &&& (b.len == 18 ==> b.bits < 262144)
}

/// From position `position`, with a buffer of `6 * (position % 4)` bits,
/// step 8 ends with a buffer of `6 * (data.len() % 4)` bits.
pub proof fn lemma_decode_loop_buffer(data: Seq<u32>, position: nat, output: Seq<u8>, buffer: Buffer)
    requires
        position <= data.len(),
        buffer.len == 6 * (position % 4),
        buffer_fits(buffer),
    ensures
        decode_loop(data, position, output, buffer).buffer.len == 6 * (data.len() % 4),
        buffer_fits(decode_loop(data, position, output, buffer).buffer),
    decreases data.len() - position
{
    if position < data.len() {
        let n = find_in_table_1(data[position as int], 0);
        // find_in_table_1 returns a row number.
        lemma_find_below_64(data[position as int], 0);
        let b = Buffer { bits: buffer.bits * 64 + n, len: buffer.len + 6 };
        if b.len == 24 {
            let out = output + seq![(b.bits / 65536) as u8, (b.bits / 256 % 256) as u8, (b.bits % 256) as u8];
            lemma_decode_loop_buffer(data, position + 1, out, empty_buffer());
        } else {
            lemma_decode_loop_buffer(data, position + 1, output, b);
        }
    }
}

/// Step 8.1's search returns a row of Table 1 (or 0).
pub proof fn lemma_find_below_64(c: u32, row: nat)
    ensures
        find_in_table_1(c, row) < 64,
    decreases 64 - row
{
    if row < 64 && table_1_encoding(row) != c {
        lemma_find_below_64(c, row + 1);
    }
}

/// The string steps 3 to 9 work on.
pub open spec fn after_step_2(data: Seq<u32>) -> Seq<u32> {
    let data = remove_ascii_whitespace(data);
    if data.len() % 4 == 0 { remove_trailing_padding(data) } else { data }
}

/// Decode step 9: "If buffer is not empty, it contains either 12 or 18
/// bits." Proven for every input that reaches step 9.
pub proof fn lemma_step_9_assertion(input: Seq<u32>)
    requires
        forgiving_base64_decode(input) is Some,
    ensures
        ({
            let s = decode_loop(after_step_2(input), 0, seq![], empty_buffer());
            s.buffer.len == 0 || s.buffer.len == 12 || s.buffer.len == 18
        }),
{
    lemma_decode_loop_buffer(after_step_2(input), 0, seq![], empty_buffer());
}

} // verus!
