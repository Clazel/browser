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

// ---------------------------------------------------------------------------
// Decode inverts encode
// ---------------------------------------------------------------------------

/// Step 2.1 only looks at the last two code points.
pub proof fn lemma_padding_append(x: Seq<u32>, y: Seq<u32>)
    requires
        y.len() >= 2,
    ensures
        remove_trailing_padding(x + y) == x + remove_trailing_padding(y),
{
    let xy = x + y;
    assert(xy[xy.len() - 1] == y[y.len() - 1]);
    assert(xy[xy.len() - 2] == y[y.len() - 2]);
    assert(xy.subrange(0, xy.len() - 2) =~= x + y.subrange(0, y.len() - 2));
    assert(xy.subrange(0, xy.len() - 1) =~= x + y.subrange(0, y.len() - 1));
}

/// "=" is not one of step 4's code points.
pub proof fn lemma_pad_not_allowed()
    ensures
        !is_step_4_allowed(pad()),
        !is_ascii_whitespace(pad()),
{
}

/// The arithmetic of a 24-bit group: its four 6-bit groups spell it again,
/// and its three bytes are its 8-bit groups.
proof fn lemma_group_arith(a: u32, b: u32, c: u32)
    requires
        a < 256,
        b < 256,
        c < 256,
    ensures
        ({
            let g = a * 65536 + b * 256 + c;
            &&& (((g / 262144 % 64) * 64 + g / 4096 % 64) * 64 + g / 64 % 64) * 64 + g % 64 == g
            &&& g / 65536 == a
            &&& g / 256 % 256 == b
            &&& g % 256 == c
        }),
{
    assert({
        let g = a * 65536 + b * 256 + c;
        &&& (((g / 262144 % 64) * 64 + g / 4096 % 64) * 64 + g / 64 % 64) * 64 + g % 64 == g
        &&& g / 65536 == a
        &&& g / 256 % 256 == b
        &&& g % 256 == c
    }) by (bit_vector)
        requires
            a < 256,
            b < 256,
            c < 256,
    ;
}

/// The arithmetic of the final 16 bits, padded to 18.
proof fn lemma_final_16_arith(a: u32, b: u32)
    requires
        a < 256,
        b < 256,
    ensures
        ({
            let g = (a * 256 + b) * 4;
            &&& ((g / 4096 % 64) * 64 + g / 64 % 64) * 64 + g % 64 == g
            &&& g / 4 / 256 == a
            &&& g / 4 % 256 == b
        }),
{
    assert({
        let g = (a * 256 + b) * 4;
        &&& ((g / 4096 % 64) * 64 + g / 64 % 64) * 64 + g % 64 == g
        &&& g / 4 / 256 == a
        &&& g / 4 % 256 == b
    }) by (bit_vector)
        requires
            a < 256,
            b < 256,
    ;
}

/// One full 24-bit group: decoding its four characters from an empty
/// buffer appends its three bytes and empties the buffer again.
proof fn lemma_decode_group(a: u8, b: u8, c: u8, output: Seq<u8>)
    ensures
        ({
            let group: nat = a as nat * 65536 + b as nat * 256 + c as nat;
            let q = seq![
                encode_6_bit_group(group / 262144),
                encode_6_bit_group(group / 4096),
                encode_6_bit_group(group / 64),
                encode_6_bit_group(group),
            ];
            decode_loop(q, 0, output, empty_buffer()) == DecodeState {
                output: output + seq![a, b, c],
                buffer: empty_buffer(),
            }
        }),
{
    let group: nat = a as nat * 65536 + b as nat * 256 + c as nat;
    let q = seq![
        encode_6_bit_group(group / 262144),
        encode_6_bit_group(group / 4096),
        encode_6_bit_group(group / 64),
        encode_6_bit_group(group),
    ];
    let n0 = group / 262144 % 64;
    let n1 = group / 4096 % 64;
    let n2 = group / 64 % 64;
    let n3 = group % 64;
    lemma_find_encoding(n0);
    lemma_find_encoding(n1);
    lemma_find_encoding(n2);
    lemma_find_encoding(n3);
    lemma_group_arith(a as u32, b as u32, c as u32);
    assert(((n0 * 64 + n1) * 64 + n2) * 64 + n3 == group);
    let bits = group;
    assert(bits / 65536 == a);
    assert(bits / 256 % 256 == b);
    assert(bits % 256 == c);
    let b1 = Buffer { bits: n0, len: 6 };
    let b2 = Buffer { bits: n0 * 64 + n1, len: 12 };
    let b3 = Buffer { bits: (n0 * 64 + n1) * 64 + n2, len: 18 };
    let out = output + seq![a, b, c];
    assert(decode_loop(q, 4, out, empty_buffer()) == DecodeState { output: out, buffer: empty_buffer() });
    assert(seq![(bits / 65536) as u8, (bits / 256 % 256) as u8, (bits % 256) as u8] =~= seq![a, b, c]);
    assert(decode_loop(q, 3, output, b3) == decode_loop(q, 4, out, empty_buffer()));
    assert(decode_loop(q, 2, output, b2) == decode_loop(q, 3, output, b3));
    assert(decode_loop(q, 1, output, b1) == decode_loop(q, 2, output, b2));
    assert(decode_loop(q, 0, output, empty_buffer()) == decode_loop(q, 1, output, b1));
}

/// The final 8 bits, case (2): two characters (after step 2 removed the
/// two "="), then step 9.
proof fn lemma_decode_final_8(a: u8, output: Seq<u8>)
    ensures
        ({
            let group: nat = a as nat * 16;
            let q = seq![encode_6_bit_group(group / 64), encode_6_bit_group(group)];
            let s = decode_loop(q, 0, output, empty_buffer());
            decode_step_9(s.output, s.buffer) == output.push(a)
        }),
{
    let group: nat = a as nat * 16;
    let q = seq![encode_6_bit_group(group / 64), encode_6_bit_group(group)];
    let n0 = group / 64 % 64;
    let n1 = group % 64;
    lemma_find_encoding(n0);
    lemma_find_encoding(n1);
    assert(n0 * 64 + n1 == group);
    let b2 = Buffer { bits: n0 * 64 + n1, len: 12 };
    assert(decode_loop(q, 2, output, b2) == DecodeState { output, buffer: b2 });
    assert(decode_loop(q, 1, output, Buffer { bits: n0, len: 6 }) == decode_loop(q, 2, output, b2));
    assert(decode_loop(q, 0, output, empty_buffer()) == decode_loop(q, 1, output, Buffer { bits: n0, len: 6 }));
    assert(group / 16 == a);
}

/// The final 16 bits, case (3): three characters (after step 2 removed the
/// "="), then step 9.
proof fn lemma_decode_final_16(a: u8, b: u8, output: Seq<u8>)
    ensures
        ({
            let group: nat = (a as nat * 256 + b as nat) * 4;
            let q = seq![
                encode_6_bit_group(group / 4096),
                encode_6_bit_group(group / 64),
                encode_6_bit_group(group),
            ];
            let s = decode_loop(q, 0, output, empty_buffer());
            decode_step_9(s.output, s.buffer) == output + seq![a, b]
        }),
{
    let group: nat = (a as nat * 256 + b as nat) * 4;
    let q = seq![
        encode_6_bit_group(group / 4096),
        encode_6_bit_group(group / 64),
        encode_6_bit_group(group),
    ];
    let n0 = group / 4096 % 64;
    let n1 = group / 64 % 64;
    let n2 = group % 64;
    lemma_find_encoding(n0);
    lemma_find_encoding(n1);
    lemma_find_encoding(n2);
    lemma_final_16_arith(a as u32, b as u32);
    assert((n0 * 64 + n1) * 64 + n2 == group);
    let b1 = Buffer { bits: n0, len: 6 };
    let b2 = Buffer { bits: n0 * 64 + n1, len: 12 };
    let b3 = Buffer { bits: (n0 * 64 + n1) * 64 + n2, len: 18 };
    assert(decode_loop(q, 3, output, b3) == DecodeState { output, buffer: b3 });
    assert(decode_loop(q, 2, output, b2) == decode_loop(q, 3, output, b3));
    assert(decode_loop(q, 1, output, b1) == decode_loop(q, 2, output, b2));
    assert(decode_loop(q, 0, output, empty_buffer()) == decode_loop(q, 1, output, b1));
    let remaining = group / 4;
    assert(remaining / 256 == a);
    assert(remaining % 256 == b);
    assert(seq![(remaining / 256) as u8, (remaining % 256) as u8] =~= seq![a, b]);
}

/// Every code point of `e` is allowed by step 4, or is "=".
pub open spec fn allowed_or_pad(e: Seq<u32>) -> bool {
    forall|k: int| 0 <= k < e.len() ==> is_step_4_allowed(#[trigger] e[k]) || e[k] == pad()
}

/// Every code point of `e` is allowed by step 4.
pub open spec fn all_allowed(e: Seq<u32>) -> bool {
    forall|k: int| 0 <= k < e.len() ==> is_step_4_allowed(#[trigger] e[k])
}

/// What the encoder outputs from byte `i` on, and what steps 2 to 9 of
/// decode make of it, continuing from `output`.
pub open spec fn encode_from_facts(data: Seq<u8>, i: nat, output: Seq<u8>) -> bool {
    let e = encode_from(data, i);
    let s = remove_trailing_padding(e);
    let st = decode_loop(s, 0, output, empty_buffer());
    &&& e.len() % 4 == 0
    &&& allowed_or_pad(e)
    &&& all_allowed(s)
    &&& s.len() % 4 != 1
    &&& decode_step_9(st.output, st.buffer) == output + data.subrange(i as int, data.len() as int)
}

/// [`encode_from_facts`] for a full 24-bit group, from the facts after it.
proof fn lemma_encode_from_group(data: Seq<u8>, i: nat, output: Seq<u8>)
    requires
        i + 3 <= data.len(),
        encode_from_facts(data, i + 3, output + seq![data[i as int], data[i as int + 1], data[i as int + 2]]),
    ensures
        encode_from_facts(data, i, output),
{
    let ii = i as int;
    let (a, b, c) = (data[ii], data[ii + 1], data[ii + 2]);
    let out = output + seq![a, b, c];
    let group: nat = a as nat * 65536 + b as nat * 256 + c as nat;
    let q = seq![
        encode_6_bit_group(group / 262144),
        encode_6_bit_group(group / 4096),
        encode_6_bit_group(group / 64),
        encode_6_bit_group(group),
    ];
    lemma_table_1_allowed(group / 262144 % 64);
    lemma_table_1_allowed(group / 4096 % 64);
    lemma_table_1_allowed(group / 64 % 64);
    lemma_table_1_allowed(group % 64);
    assert(all_allowed(q));
    let e = encode_from(data, i);
    let e2 = encode_from(data, i + 3);
    let s = remove_trailing_padding(e);
    let s2 = remove_trailing_padding(e2);
    assert(e == q + e2);
    assert forall|k: int| 0 <= k < e.len() implies is_step_4_allowed(#[trigger] e[k]) || e[k] == pad() by {
        if k >= 4 {
            assert(e[k] == e2[k - 4]);
        }
    }
    lemma_pad_not_allowed();
    if e2.len() >= 2 {
        lemma_padding_append(q, e2);
    } else {
        assert(e2.len() == 0);
        assert(e =~= q);
        assert(s2 =~= seq![]);
        assert(q + s2 =~= q);
    }
    assert(s == q + s2);
    assert forall|k: int| 0 <= k < s.len() implies is_step_4_allowed(#[trigger] s[k]) by {
        if k >= 4 {
            assert(s[k] == s2[k - 4]);
        }
    }
    lemma_decode_group(a, b, c, output);
    lemma_decode_loop_append(q, s2, 0, output, empty_buffer());
    assert(out + data.subrange(ii + 3, data.len() as int) =~= output + data.subrange(ii, data.len() as int));
}

/// [`encode_from_facts`] for the final 8 bits.
proof fn lemma_encode_from_final_8(data: Seq<u8>, i: nat, output: Seq<u8>)
    requires
        i + 1 == data.len(),
    ensures
        encode_from_facts(data, i, output),
{
    let ii = i as int;
    let a = data[ii];
    let group: nat = a as nat * 16;
    lemma_table_1_allowed(group / 64 % 64);
    lemma_table_1_allowed(group % 64);
    lemma_pad_not_allowed();
    let q = seq![encode_6_bit_group(group / 64), encode_6_bit_group(group)];
    let e = encode_from(data, i);
    assert(e == q + seq![pad(), pad()]);
    assert(remove_trailing_padding(e) =~= q);
    lemma_decode_final_8(a, output);
    assert(output.push(a) =~= output + data.subrange(ii, data.len() as int));
}

/// [`encode_from_facts`] for the final 16 bits.
proof fn lemma_encode_from_final_16(data: Seq<u8>, i: nat, output: Seq<u8>)
    requires
        i + 2 == data.len(),
    ensures
        encode_from_facts(data, i, output),
{
    let ii = i as int;
    let (a, b) = (data[ii], data[ii + 1]);
    let group: nat = (a as nat * 256 + b as nat) * 4;
    lemma_table_1_allowed(group / 4096 % 64);
    lemma_table_1_allowed(group / 64 % 64);
    lemma_table_1_allowed(group % 64);
    lemma_pad_not_allowed();
    let q = seq![
        encode_6_bit_group(group / 4096),
        encode_6_bit_group(group / 64),
        encode_6_bit_group(group),
    ];
    let e = encode_from(data, i);
    assert(e == q.push(pad()));
    assert(remove_trailing_padding(e) =~= q);
    lemma_decode_final_16(a, b, output);
    assert(output + seq![a, b] =~= output + data.subrange(ii, data.len() as int));
}

/// [`encode_from_facts`] holds from every position.
pub proof fn lemma_decode_encode_from(data: Seq<u8>, i: nat, output: Seq<u8>)
    requires
        i <= data.len(),
    ensures
        encode_from_facts(data, i, output),
    decreases data.len() - i
{
    if i + 3 <= data.len() {
        let ii = i as int;
        lemma_decode_encode_from(data, i + 3, output + seq![data[ii], data[ii + 1], data[ii + 2]]);
        lemma_encode_from_group(data, i, output);
    } else if i + 1 == data.len() {
        lemma_encode_from_final_8(data, i, output);
    } else if i + 2 == data.len() {
        lemma_encode_from_final_16(data, i, output);
    } else {
        let e = encode_from(data, i);
        assert(e =~= seq![]);
        assert(remove_trailing_padding(e) =~= seq![]);
        assert(output + data.subrange(i as int, data.len() as int) =~= output);
    }
}

/// Decode inverts encode: "forgiving-base64 decode" of "forgiving-base64
/// encode" of any byte sequence is that byte sequence.
pub proof fn lemma_decode_encode(data: Seq<u8>)
    ensures
        forgiving_base64_decode(forgiving_base64_encode(data)) == Some(data),
{
    let e = forgiving_base64_encode(data);
    lemma_decode_encode_from(data, 0, seq![]);
    lemma_pad_not_allowed();
    assert forall|k: int| 0 <= k < e.len() implies !is_ascii_whitespace(#[trigger] e[k]) by {
        assert(is_step_4_allowed(e[k]) || e[k] == pad());
    }
    lemma_remove_whitespace_none(e);
    let s = remove_trailing_padding(e);
    lemma_contains_disallowed(s);
    assert(Seq::<u8>::empty() + data.subrange(0, data.len() as int) =~= data);
}

/// The encoder outputs only ASCII code points.
pub proof fn lemma_encode_ascii(data: Seq<u8>)
    ensures
        forall|k: int| 0 <= k < forgiving_base64_encode(data).len() ==> #[trigger] forgiving_base64_encode(data)[k] < 0x80,
{
    lemma_decode_encode_from(data, 0, seq![]);
    let e = forgiving_base64_encode(data);
    assert forall|k: int| 0 <= k < e.len() implies #[trigger] e[k] < 0x80 by {
        lemma_pad_not_allowed();
        assert(is_step_4_allowed(e[k]) || e[k] == pad());
    }
}


// ---------------------------------------------------------------------------
// When decode fails
// ---------------------------------------------------------------------------

/// The strings decode accepts once ASCII whitespace is gone: step 4's code
/// points, leaving no single one over at the end of the last 4-character
/// quantum; or such code points followed by one or two "=" that complete a
/// quantum.
pub open spec fn well_formed(t: Seq<u32>) -> bool {
    let n = t.len() as int;
    ||| all_allowed(t) && t.len() % 4 != 1
    ||| t.len() % 4 == 0 && n >= 1 && t[n - 1] == pad() && all_allowed(t.subrange(0, n - 1))
    ||| t.len() % 4 == 0 && n >= 2 && t[n - 1] == pad() && t[n - 2] == pad() && all_allowed(t.subrange(0, n - 2))
}

/// Decode fails exactly on the cases steps 3 and 4 list, stated without
/// the steps' control flow: it succeeds if and only if the input, without
/// its ASCII whitespace, is [`well_formed`].
pub proof fn lemma_fails_exactly(input: Seq<u32>)
    ensures
        forgiving_base64_decode(input) is Some <==> well_formed(remove_ascii_whitespace(input)),
{
    let t = remove_ascii_whitespace(input);
    let n = t.len() as int;
    let d = after_step_2(input);
    lemma_contains_disallowed(d);
    lemma_pad_not_allowed();
    if t.len() % 4 == 0 && n >= 2 && t[n - 1] == pad() && t[n - 2] == pad() {
        assert(d == t.subrange(0, n - 2));
        // Disjuncts 1 and 2 fail on a "=" that step 4 rejects.
        assert(!is_step_4_allowed(t[n - 1]));
        assert(t.subrange(0, n - 1)[n - 2] == pad());
    } else if t.len() % 4 == 0 && n >= 1 && t[n - 1] == pad() {
        assert(d == t.subrange(0, n - 1));
        assert(!is_step_4_allowed(t[n - 1]));
    } else if t.len() % 4 == 0 {
        assert(d == t);
    } else {
        assert(d == t);
    }
}

/// The input with code point `c` inserted at index `k`.
pub open spec fn insert(s: Seq<u32>, k: int, c: u32) -> Seq<u32> {
    s.subrange(0, k) + seq![c] + s.subrange(k, s.len() as int)
}

/// Inserting any of the five code points Infra §4.6 lists as ASCII
/// whitespace (named here as literals: TAB, LF, FF, CR, SPACE), anywhere,
/// does not change what decode returns.
pub proof fn lemma_ignores_whitespace(s: Seq<u32>, k: int, c: u32)
    requires
        0 <= k <= s.len(),
        c == 0x09 || c == 0x0A || c == 0x0C || c == 0x0D || c == 0x20,
    ensures
        forgiving_base64_decode(insert(s, k, c)) == forgiving_base64_decode(s),
{
    let x = s.subrange(0, k);
    let y = s.subrange(k, s.len() as int);
    lemma_remove_whitespace_append(x + seq![c], y);
    lemma_remove_whitespace_append(x, seq![c]);
    lemma_remove_whitespace_drops(c);
    lemma_remove_whitespace_append(x, y);
    assert(x + y =~= s);
    assert(remove_ascii_whitespace(x) + Seq::<u32>::empty() =~= remove_ascii_whitespace(x));
}

/// Inserting a code point that is none of the 64 in Table 1, "=", or the
/// five ASCII whitespace ones (all named here as literals), anywhere, makes
/// decode fail.
pub proof fn lemma_rejects_other(s: Seq<u32>, k: int, c: u32)
    requires
        0 <= k <= s.len(),
        !(c == 0x09 || c == 0x0A || c == 0x0C || c == 0x0D || c == 0x20),
        !(c == 0x2B || c == 0x2F || c == 0x3D || (0x30 <= c <= 0x39) || (0x41 <= c <= 0x5A) || (0x61 <= c
            <= 0x7A)),
    ensures
        forgiving_base64_decode(insert(s, k, c)) is None,
{
    let x = s.subrange(0, k);
    let y = s.subrange(k, s.len() as int);
    let input = insert(s, k, c);
    lemma_remove_whitespace_append(x + seq![c], y);
    lemma_remove_whitespace_append(x, seq![c]);
    lemma_remove_whitespace_keeps(c);
    let t = remove_ascii_whitespace(input);
    let p = remove_ascii_whitespace(x).len() as int;
    assert(t[p] == c);
    let d = after_step_2(input);
    // Step 2 removes only "=", and c is not "=", so c is still in d.
    assert(p < d.len());
    assert(d[p] == c);
    lemma_contains_disallowed(d);
}


/// RFC 4648 §10's test vectors, evaluated on the spec: "f" is "Zg==",
/// "fo" is "Zm8=", "foo" is "Zm9v", "foobar" is "Zm9vYmFy", and decode
/// takes each back. Also Infra's own note on step 9: "YQ" and "YR" both
/// return `a`.
pub proof fn lemma_examples() {
    assert(forgiving_base64_encode(seq![0x66u8]) == seq![0x5Au32, 0x67, 0x3D, 0x3D]) by (compute_only);
    assert(forgiving_base64_encode(seq![0x66u8, 0x6F]) == seq![0x5Au32, 0x6D, 0x38, 0x3D]) by (compute_only);
    assert(forgiving_base64_encode(seq![0x66u8, 0x6F, 0x6F]) == seq![0x5Au32, 0x6D, 0x39, 0x76]) by (compute_only);
    assert(forgiving_base64_encode(seq![0x66u8, 0x6F, 0x6F, 0x62, 0x61, 0x72])
        == seq![0x5Au32, 0x6D, 0x39, 0x76, 0x59, 0x6D, 0x46, 0x79]) by (compute_only);
    assert(forgiving_base64_decode(seq![0x5Au32, 0x67, 0x3D, 0x3D]) == Some(seq![0x66u8])) by (compute_only);
    assert(forgiving_base64_decode(seq![0x5Au32, 0x6D, 0x38, 0x3D]) == Some(seq![0x66u8, 0x6F])) by (compute_only);
    assert(forgiving_base64_decode(seq![0x5Au32, 0x6D, 0x39, 0x76, 0x59, 0x6D, 0x46, 0x79])
        == Some(seq![0x66u8, 0x6F, 0x6F, 0x62, 0x61, 0x72])) by (compute_only);
    assert(forgiving_base64_decode(seq![0x59u32, 0x51]) == Some(seq![0x61u8])) by (compute_only);
    assert(forgiving_base64_decode(seq![0x59u32, 0x52]) == Some(seq![0x61u8])) by (compute_only);
}

} // verus!
