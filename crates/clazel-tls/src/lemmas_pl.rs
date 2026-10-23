//! Facts proven about the presentation-language readers and writers of
//! [`super::spec`] (RFC 8446 §3). They are evidence that the transcription
//! is right, not part of what the implementation must meet. The ones that
//! matter:
//!
//! - **round trips both ways**: a writer's output is read back
//!   ([`lemma_read_vec_write_vec`], [`lemma_read_list_write_list`]) and
//!   what a reader accepts is exactly what the writer writes
//!   ([`lemma_read_vec_canonical`], [`lemma_write_list_read_list`]), so
//!   each value has one encoding;
//! - **no over-read**: a reader's result depends only on the bytes it
//!   consumed ([`lemma_read_uint_extend`], [`lemma_read_vec_extend`]);
//! - **bounded reservation**: a list has no more elements than bytes
//!   ([`lemma_read_list_len`]).

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------
// Network byte order.
// ---------------------------------------------------------------------------

/// 256^n is at least 1.
pub proof fn lemma_pow256_positive(n: nat)
    ensures
        pow256(n) >= 1,
    decreases n,
{
    if n > 0 {
        lemma_pow256_positive((n - 1) as nat);
    }
}

/// The widths used here: one, two, three, four and eight bytes.
pub proof fn lemma_pow256_widths()
    ensures
        pow256(0) == 1,
        pow256(1) == 256,
        pow256(2) == 65536,
        pow256(3) == 16777216,
        pow256(4) == 4294967296,
        pow256(8) == 0x1_0000_0000_0000_0000,
{
    assert(pow256(0) == 1) by (compute_only);
    assert(pow256(1) == 256) by (compute_only);
    assert(pow256(2) == 65536) by (compute_only);
    assert(pow256(3) == 16777216) by (compute_only);
    assert(pow256(4) == 4294967296) by (compute_only);
    assert(pow256(8) == 0x1_0000_0000_0000_0000) by (compute_only);
}

/// `n` bytes spell a number below 256^n.
pub proof fn lemma_be_value_bound(s: Seq<u8>)
    ensures
        be_value(s) < pow256(s.len()),
    decreases s.len(),
{
    if s.len() > 0 {
        lemma_be_value_bound(s.drop_last());
        assert(be_value(s) == be_value(s.drop_last()) * 256 + s.last() as nat);
        assert(pow256(s.len()) == 256 * pow256((s.len() - 1) as nat));
    }
}

/// `be_bytes(v, w)` has `w` bytes.
pub proof fn lemma_be_bytes_len(v: nat, w: nat)
    ensures
        be_bytes(v, w).len() == w,
    decreases w,
{
    if w > 0 {
        lemma_be_bytes_len(v / 256, (w - 1) as nat);
    }
}

/// Reading back what [`be_bytes`] wrote: any `v` below 256^w survives.
pub proof fn lemma_be_value_of_be_bytes(v: nat, w: nat)
    requires
        v < pow256(w),
    ensures
        be_value(be_bytes(v, w)) == v,
    decreases w,
{
    if w > 0 {
        let rest = be_bytes(v / 256, (w - 1) as nat);
        assert(pow256(w) == 256 * pow256((w - 1) as nat));
        assert(v / 256 < pow256((w - 1) as nat));
        lemma_be_value_of_be_bytes(v / 256, (w - 1) as nat);
        lemma_be_bytes_len(v / 256, (w - 1) as nat);
        let s = rest.push((v % 256) as u8);
        assert(s.drop_last() =~= rest);
        assert(s.last() == (v % 256) as u8);
        assert(be_value(s) == be_value(rest) * 256 + (v % 256) as nat);
        assert(v == (v / 256) * 256 + v % 256);
    }
}

/// Writing what [`be_value`] read: `s` is spelled back byte for byte.
pub proof fn lemma_be_bytes_of_be_value(s: Seq<u8>)
    ensures
        be_bytes(be_value(s), s.len()) =~= s,
    decreases s.len(),
{
    if s.len() > 0 {
        let d = s.drop_last();
        lemma_be_bytes_of_be_value(d);
        let v = be_value(s);
        assert(v == be_value(d) * 256 + s.last() as nat);
        assert(v / 256 == be_value(d)) by (nonlinear_arith)
            requires
                v == be_value(d) * 256 + s.last() as nat,
                s.last() < 256,
        ;
        assert(v % 256 == s.last() as nat) by (nonlinear_arith)
            requires
                v == be_value(d) * 256 + s.last() as nat,
                s.last() < 256,
        ;
        assert(be_bytes(v, s.len()) =~= be_bytes(v / 256, d.len()).push((v % 256) as u8));
        assert(d.push(s.last()) =~= s);
    }
}

// ---------------------------------------------------------------------------
// §3.3: numbers.
// ---------------------------------------------------------------------------

/// Reading a number that was written reads it back, and leaves whatever
/// follows.
pub proof fn lemma_read_uint_write(v: nat, w: nat, rest: Seq<u8>)
    requires
        v < pow256(w),
    ensures
        read_uint(be_bytes(v, w) + rest, w) == Some((v, rest)),
{
    lemma_be_bytes_len(v, w);
    lemma_be_value_of_be_bytes(v, w);
    let b = be_bytes(v, w) + rest;
    assert(b.take(w as int) =~= be_bytes(v, w));
    assert(b.skip(w as int) =~= rest);
}

/// What [`read_uint`] reads is what [`be_bytes`] writes: the bytes read
/// are the number's one encoding, so the number is below 256^w and the
/// input is those bytes and the rest.
pub proof fn lemma_read_uint_canonical(b: Seq<u8>, w: nat)
    ensures
        match read_uint(b, w) {
            Some((v, r)) => {
                &&& v < pow256(w)
                &&& b =~= be_bytes(v, w) + r
                &&& r.len() == b.len() - w
            },
            None => b.len() < w,
        },
{
    if let Some((v, r)) = read_uint(b, w) {
        let t = b.take(w as int);
        lemma_be_value_bound(t);
        lemma_be_bytes_of_be_value(t);
        assert(b =~= t + b.skip(w as int));
    }
}

/// No over-read: the result of [`read_uint`] does not depend on the bytes
/// after the number.
pub proof fn lemma_read_uint_extend(b: Seq<u8>, w: nat, extra: Seq<u8>)
    ensures
        match read_uint(b, w) {
            Some((v, r)) => read_uint(b + extra, w) == Some((v, r + extra)),
            None => true,
        },
{
    if let Some((v, r)) = read_uint(b, w) {
        assert((b + extra).take(w as int) =~= b.take(w as int));
        assert((b + extra).skip(w as int) =~= b.skip(w as int) + extra);
    }
}

/// No over-read: the same for [`read_fixed`].
pub proof fn lemma_read_fixed_extend(b: Seq<u8>, n: nat, extra: Seq<u8>)
    ensures
        match read_fixed(b, n) {
            Some((v, r)) => read_fixed(b + extra, n) == Some((v, r + extra)),
            None => true,
        },
{
    if let Some((v, r)) = read_fixed(b, n) {
        assert((b + extra).take(n as int) =~= b.take(n as int));
        assert((b + extra).skip(n as int) =~= b.skip(n as int) + extra);
    }
}

/// What [`read_fixed`] reads is `n` bytes, and the input is those bytes
/// and the rest.
pub proof fn lemma_read_fixed_canonical(b: Seq<u8>, n: nat)
    ensures
        match read_fixed(b, n) {
            Some((s, r)) => s.len() == n && b =~= s + r && r.len() == b.len() - n,
            None => b.len() < n,
        },
{
    if let Some((s, r)) = read_fixed(b, n) {
        assert(b =~= b.take(n as int) + b.skip(n as int));
    }
}

/// A fixed-size field is read back, and is canonical.
pub proof fn lemma_read_fixed_write(s: Seq<u8>, rest: Seq<u8>)
    ensures
        read_fixed(s + rest, s.len()) == Some((s, rest)),
{
    assert((s + rest).take(s.len() as int) =~= s);
    assert((s + rest).skip(s.len() as int) =~= rest);
}

// ---------------------------------------------------------------------------
// §3.4: vectors.
// ---------------------------------------------------------------------------

/// The length field of a vector with ceiling `ceil` can hold the ceiling.
pub proof fn lemma_len_width_holds(ceil: nat)
    requires
        ceil < 16777216,
    ensures
        ceil < pow256(len_width(ceil)),
        1 <= len_width(ceil) <= 3,
{
    lemma_pow256_widths();
}

/// A vector in bounds is read back from what [`write_vec`] wrote, and
/// leaves whatever follows.
pub proof fn lemma_read_vec_write_vec(content: Seq<u8>, floor: nat, ceil: nat, rest: Seq<u8>)
    requires
        ceil < 16777216,
        vec_in_bounds(content, floor, ceil),
    ensures
        read_vec(write_vec(content, ceil) + rest, floor, ceil) == Some((content, rest)),
{
    lemma_len_width_holds(ceil);
    let w = len_width(ceil);
    let b = write_vec(content, ceil) + rest;
    assert(b =~= be_bytes(content.len(), w) + (content + rest));
    lemma_read_uint_write(content.len(), w, content + rest);
    let r = content + rest;
    assert(r.take(content.len() as int) =~= content);
    assert(r.skip(content.len() as int) =~= rest);
}

/// What [`read_vec`] accepts is what [`write_vec`] writes: the contents
/// are within the bounds, the input is the vector's encoding followed by
/// the rest, and the rest is shorter than the input.
pub proof fn lemma_read_vec_canonical(b: Seq<u8>, floor: nat, ceil: nat)
    ensures
        match read_vec(b, floor, ceil) {
            Some((c, r)) => {
                &&& vec_in_bounds(c, floor, ceil)
                &&& b =~= write_vec(c, ceil) + r
                &&& r.len() + len_width(ceil) + c.len() == b.len()
            },
            None => true,
        },
{
    if let Some((c, r)) = read_vec(b, floor, ceil) {
        let w = len_width(ceil);
        if let Some((n, r1)) = read_uint(b, w) {
            lemma_read_uint_canonical(b, w);
            assert(n == c.len());
            assert(c =~= r1.take(n as int));
            assert(r1 =~= c + r);
            assert(b =~= be_bytes(c.len(), w) + r1);
            assert(b =~= write_vec(c, ceil) + r);
        }
    }
}

/// No over-read: the result of [`read_vec`] does not depend on the bytes
/// after the vector.
pub proof fn lemma_read_vec_extend(b: Seq<u8>, floor: nat, ceil: nat, extra: Seq<u8>)
    ensures
        match read_vec(b, floor, ceil) {
            Some((c, r)) => read_vec(b + extra, floor, ceil) == Some((c, r + extra)),
            None => true,
        },
{
    if let Some((c, r)) = read_vec(b, floor, ceil) {
        let w = len_width(ceil);
        lemma_read_uint_extend(b, w, extra);
        if let Some((n, r1)) = read_uint(b, w) {
            assert((b + extra).skip(w as int) =~= r1 + extra);
            let rr = r1 + extra;
            assert(rr.take(n as int) =~= r1.take(n as int));
            assert(rr.skip(n as int) =~= r1.skip(n as int) + extra);
        }
    }
}

// ---------------------------------------------------------------------------
// §3.4: lists of elements.
// ---------------------------------------------------------------------------

/// A list of elements, each one a value its reader reads back from its
/// own encoding, is read back from [`write_list`]. `ok` says which
/// elements are encodable; an element's encoding is at least one byte, and
/// is read back wherever it sits and whatever follows it.
pub proof fn lemma_read_list_write_list<E>(
    es: Seq<E>,
    w: spec_fn(E) -> Seq<u8>,
    f: spec_fn(Seq<u8>) -> Option<(E, Seq<u8>)>,
    ok: spec_fn(E) -> bool,
)
    requires
        forall|e: E| #[trigger] ok(e) ==> w(e).len() >= 1,
        forall|e: E, rest: Seq<u8>| ok(e) ==> #[trigger] f(w(e) + rest) == Some((e, rest)),
        forall|i: int| 0 <= i < es.len() ==> #[trigger] ok(es[i]),
    ensures
        read_list(write_list(es, w), f) == Some(es),
    decreases es.len(),
{
    if es.len() > 0 {
        let e = es[0];
        let tail = es.skip(1);
        assert(ok(e));
        assert forall|i: int| 0 <= i < tail.len() implies #[trigger] ok(tail[i]) by {
            assert(tail[i] == es[i + 1]);
        }
        lemma_read_list_write_list(tail, w, f, ok);
        let wl = write_list(tail, w);
        let b = w(e) + wl;
        assert(write_list(es, w) == b);
        assert(f(b) == Some((e, wl)));
        assert(wl.len() < b.len());
        assert(es =~= seq![e] + tail);
    }
}

/// What [`read_list`] accepts is what [`write_list`] writes, given that
/// each element's reader returns an element whose encoding is the bytes
/// it consumed.
pub proof fn lemma_write_list_read_list<E>(
    b: Seq<u8>,
    w: spec_fn(E) -> Seq<u8>,
    f: spec_fn(Seq<u8>) -> Option<(E, Seq<u8>)>,
)
    requires
        forall|bb: Seq<u8>| #[trigger] f(bb) is Some ==> w(f(bb)->Some_0.0) + f(bb)->Some_0.1 == bb,
    ensures
        match read_list(b, f) {
            Some(es) => write_list(es, w) == b,
            None => true,
        },
    decreases b.len(),
{
    if b.len() > 0 {
        if let Some((e, rest)) = f(b) {
            if rest.len() < b.len() {
                lemma_write_list_read_list(rest, w, f);
                if let Some(es) = read_list(rest, f) {
                    let all = seq![e] + es;
                    assert(all.skip(1) =~= es);
                    assert(write_list(all, w) == w(e) + write_list(es, w));
                }
            }
        }
    }
}

/// Bounded reservation: a list read from `b` has at most `b.len()`
/// elements, whatever lengths the bytes declare.
pub proof fn lemma_read_list_len<E>(b: Seq<u8>, f: spec_fn(Seq<u8>) -> Option<(E, Seq<u8>)>)
    ensures
        match read_list(b, f) {
            Some(es) => es.len() <= b.len(),
            None => true,
        },
    decreases b.len(),
{
    if b.len() > 0 {
        if let Some((e, rest)) = f(b) {
            if rest.len() < b.len() {
                lemma_read_list_len(rest, f);
                if let Some(es) = read_list(rest, f) {
                    assert((seq![e] + es).len() == es.len() + 1);
                }
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Lists of uint16.
// ---------------------------------------------------------------------------

/// A `uint16` is read back from its two bytes.
pub proof fn lemma_read_u16_write(v: u16, rest: Seq<u8>)
    ensures
        read_u16(write_u16(v) + rest) == Some((v, rest)),
{
    lemma_pow256_widths();
    lemma_read_uint_write(v as nat, 2, rest);
}

/// The two bytes a `uint16` reader consumed are its encoding.
pub proof fn lemma_read_u16_canonical(b: Seq<u8>)
    ensures
        match read_u16(b) {
            Some((v, r)) => write_u16(v) + r =~= b && r.len() < b.len(),
            None => true,
        },
{
    lemma_pow256_widths();
    if let Some((v, r)) = read_u16(b) {
        lemma_read_uint_canonical(b, 2);
        lemma_be_bytes_len(v as nat, 2);
        let nv = be_value(b.take(2));
        assert(nv < 65536);
        assert(v as nat == nv);
    }
}

/// A list of `uint16` is read back from what [`write_u16s`] wrote.
pub proof fn lemma_read_u16s_write_u16s(vs: Seq<u16>)
    ensures
        read_u16s(write_u16s(vs)) == Some(vs),
{
    let w = |v: u16| write_u16(v);
    let f = |x: Seq<u8>| read_u16(x);
    let ok = |v: u16| true;
    assert forall|e: u16| #[trigger] ok(e) implies w(e).len() >= 1 by {
        lemma_be_bytes_len(e as nat, 2);
    }
    assert forall|e: u16, rest: Seq<u8>| ok(e) implies #[trigger] f(w(e) + rest) == Some((e, rest)) by {
        lemma_read_u16_write(e, rest);
    }
    lemma_read_list_write_list(vs, w, f, ok);
}

/// What [`read_u16s`] accepts is what [`write_u16s`] writes, and the bytes
/// are a whole number of `uint16`: "the length of an encoded vector must
/// be an exact multiple of the length of a single element".
pub proof fn lemma_write_u16s_read_u16s(b: Seq<u8>)
    ensures
        match read_u16s(b) {
            Some(vs) => write_u16s(vs) == b && b.len() == 2 * vs.len(),
            None => true,
        },
{
    let w = |v: u16| write_u16(v);
    let f = |x: Seq<u8>| read_u16(x);
    assert forall|bb: Seq<u8>| #[trigger] f(bb) is Some implies w(f(bb)->Some_0.0) + f(bb)->Some_0.1 == bb by {
        lemma_read_u16_canonical(bb);
    }
    lemma_write_list_read_list(b, w, f);
    if let Some(vs) = read_u16s(b) {
        lemma_write_u16s_len(vs);
    }
}

/// A list of `uint16` is twice as many bytes as elements.
pub proof fn lemma_write_u16s_len(vs: Seq<u16>)
    ensures
        write_u16s(vs).len() == 2 * vs.len(),
    decreases vs.len(),
{
    if vs.len() > 0 {
        lemma_be_bytes_len(vs[0] as nat, 2);
        lemma_write_u16s_len(vs.skip(1));
        assert(write_u16s(vs) == write_u16(vs[0]) + write_u16s(vs.skip(1)));
    }
}

} // verus!
