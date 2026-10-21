//! Facts proven about the spec itself ([`super::spec`]). They are evidence
//! that the transcription is right, not part of what the implementation
//! must meet. The three that matter are [`lemma_decode_encode`] (decode
//! inverts encode), [`lemma_encode_decode`] (encode inverts decode wherever
//! decode succeeds, so the profile is canonical) and
//! [`lemma_decode_alloc_bound`] (decoding never produces more tokens than
//! there are bytes).

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------
// Network byte order.
// ---------------------------------------------------------------------------

/// 256 to the power `n`: the number of values `n` bytes can hold.
pub open spec fn pow256(n: nat) -> nat
    decreases n
{
    if n == 0 {
        1
    } else {
        256 * pow256((n - 1) as nat)
    }
}

/// Eight bytes hold exactly the values of a `u64`.
pub proof fn lemma_pow256_8()
    ensures
        pow256(8) == 0x1_0000_0000_0000_0000,
        pow256(4) == 0x1_0000_0000,
        pow256(2) == 0x1_0000,
        pow256(1) == 256,
{
    assert(pow256(8) == 0x1_0000_0000_0000_0000) by (compute_only);
    assert(pow256(4) == 0x1_0000_0000) by (compute_only);
    assert(pow256(2) == 0x1_0000) by (compute_only);
    assert(pow256(1) == 256) by (compute_only);
}

/// `n` bytes spell a number below 256^n.
pub proof fn lemma_be_value_bound(s: Seq<u8>)
    ensures
        be_value(s) < pow256(s.len()),
    decreases s.len()
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
    decreases w
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
    decreases w
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
    decreases s.len()
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
// Heads: the initial byte and argument.
// ---------------------------------------------------------------------------

/// The head of an item that decodes is the preferred serialization of its
/// major type and argument (so a head has one encoding), is at least one
/// byte, ends within the input, and its argument fits in 64 bits.
pub proof fn lemma_decode_head_canonical(b: Seq<u8>, pos: nat)
    ensures
        match decode_head(b, pos) {
            Some((major, value, len)) => {
                &&& len >= 1
                &&& pos + len <= b.len()
                &&& value < 0x1_0000_0000_0000_0000
                &&& major == major_type(b[pos as int])
                &&& b.subrange(pos as int, (pos + len) as int) =~= encode_head(major, value)
            },
            None => true,
        },
{
    lemma_pow256_8();
    if let Some((major, value, len)) = decode_head(b, pos) {
        let ib = b[pos as int];
        let ai = additional_info(ib);
        assert(ib as int == 32 * (ib / 32) + ib % 32);
        let width = argument_bytes(ai).unwrap();
        let extra = b.subrange(pos as int + 1, (pos + 1 + width) as int);
        let head = b.subrange(pos as int, (pos + len) as int);
        assert(head =~= seq![ib] + extra);
        if ai < 24 {
            assert(value == ai as nat);
            assert(encode_head(major, value) =~= seq![(major * 32 + value) as u8]);
            assert(head =~= encode_head(major, value));
        } else {
            lemma_be_value_bound(extra);
            lemma_be_bytes_of_be_value(extra);
            assert(value == be_value(extra));
            assert(extra.len() == width);
            if ai == 24 {
                assert(pow256(1) == 256);
                assert(value >= 24 && value < 256);
            } else if ai == 25 {
                assert(value >= 256 && value < 65536);
            } else if ai == 26 {
                assert(value >= 65536 && value < 4294967296);
            } else {
                assert(value >= 4294967296);
            }
            assert(head =~= encode_head(major, value));
        }
    }
}

/// The argument bytes of a head written by [`encode_head`] are
/// `be_bytes(value, w)`.
proof fn lemma_extra_bytes(head: Seq<u8>, b: Seq<u8>, pos: nat, w: nat, value: nat)
    requires
        head.len() == 1 + w,
        head =~= seq![head[0]] + be_bytes(value, w),
        pos + 1 + w <= b.len(),
        b.subrange(pos as int, (pos + 1 + w) as int) =~= head,
    ensures
        b.subrange(pos as int + 1, (pos + 1 + w) as int) =~= be_bytes(value, w),
{
    lemma_be_bytes_len(value, w);
    let extra = b.subrange(pos as int + 1, (pos + 1 + w) as int);
    assert(extra.len() == w);
    assert forall|i: int| 0 <= i < w implies extra[i] == be_bytes(value, w)[i] by {
        assert(b.subrange(pos as int, (pos + 1 + w) as int)[1 + i] == head[1 + i]);
        assert(head[1 + i] == (seq![head[0]] + be_bytes(value, w))[1 + i]);
    }
}

/// Decoding an encoded head gives back its major type and argument, and
/// only needs the head's bytes to be at `pos`.
pub proof fn lemma_decode_head_encode_head(major: u8, value: nat, b: Seq<u8>, pos: nat)
    requires
        major < 8,
        value < 0x1_0000_0000_0000_0000,
        pos + encode_head(major, value).len() <= b.len(),
        b.subrange(pos as int, (pos + encode_head(major, value).len()) as int) =~= encode_head(major, value),
    ensures
        decode_head(b, pos) == Some((major, value, encode_head(major, value).len())),
{
    lemma_pow256_8();
    let head = encode_head(major, value);
    let ib = head[0];
    assert(b[pos as int] == ib);
    if value < 24 {
        assert(head =~= seq![(major * 32 + value) as u8]);
    } else if value < 256 {
        lemma_be_bytes_len(value, 1);
        assert(head =~= seq![(major * 32 + 24) as u8] + be_bytes(value, 1));
    } else if value < 65536 {
        lemma_be_bytes_len(value, 2);
        assert(head =~= seq![(major * 32 + 25) as u8] + be_bytes(value, 2));
    } else if value < 4294967296 {
        lemma_be_bytes_len(value, 4);
        assert(head =~= seq![(major * 32 + 26) as u8] + be_bytes(value, 4));
    } else {
        lemma_be_bytes_len(value, 8);
        assert(head =~= seq![(major * 32 + 27) as u8] + be_bytes(value, 8));
    }
    assert(major_type(ib) == major);
    let ai = additional_info(ib);
    if value < 24 {
        assert(ai as nat == value);
    } else if value < 256 {
        assert(ai == 24);
        lemma_be_value_of_be_bytes(value, 1);
        lemma_extra_bytes(head, b, pos, 1, value);
    } else if value < 65536 {
        assert(ai == 25);
        lemma_be_value_of_be_bytes(value, 2);
        lemma_extra_bytes(head, b, pos, 2, value);
    } else if value < 4294967296 {
        assert(ai == 26);
        lemma_be_value_of_be_bytes(value, 4);
        lemma_extra_bytes(head, b, pos, 4, value);
    } else {
        assert(ai == 27);
        lemma_be_value_of_be_bytes(value, 8);
        lemma_extra_bytes(head, b, pos, 8, value);
    }
}

// ---------------------------------------------------------------------------
// Tokens.
// ---------------------------------------------------------------------------

/// A token that decodes is at least one byte, ends within the input, is one
/// the profile can encode, and its bytes are exactly its preferred
/// serialization: no other bytes decode to it.
pub proof fn lemma_decode_token_canonical(b: Seq<u8>, pos: nat)
    ensures
        match decode_token(b, pos) {
            Some((token, len)) => {
                &&& len >= 1
                &&& pos + len <= b.len()
                &&& token_ok(token)
                &&& b.subrange(pos as int, (pos + len) as int) =~= encode_token(token)
            },
            None => true,
        },
{
    if let Some((token, len)) = decode_token(b, pos) {
        let ib = b[pos as int];
        assert(ib as int == 32 * (ib / 32) + ib % 32);
        if major_type(ib) == 7 {
            assert(b.subrange(pos as int, pos as int + 1) =~= seq![ib]);
        } else {
            lemma_decode_head_canonical(b, pos);
            let (major, value, head_len) = decode_head(b, pos).unwrap();
            let head = b.subrange(pos as int, (pos + head_len) as int);
            assert(head =~= encode_head(major, value));
            if major == 2 || major == 3 {
                let payload = b.subrange((pos + head_len) as int, (pos + head_len + value) as int);
                assert(b.subrange(pos as int, (pos + head_len + value) as int) =~= head + payload);
                assert(payload.len() == value);
            }
        }
    }
}

/// The payload after a head is the string the token holds.
proof fn lemma_payload(b: Seq<u8>, pos: nat, head: Seq<u8>, s: Seq<u8>)
    requires
        pos + head.len() + s.len() <= b.len(),
        b.subrange(pos as int, (pos + head.len() + s.len()) as int) =~= head + s,
    ensures
        b.subrange((pos + head.len()) as int, (pos + head.len() + s.len()) as int) =~= s,
{
    let payload = b.subrange((pos + head.len()) as int, (pos + head.len() + s.len()) as int);
    assert(payload.len() == s.len());
    assert forall|i: int| 0 <= i < s.len() implies payload[i] == s[i] by {
        assert(b.subrange(pos as int, (pos + head.len() + s.len()) as int)[head.len() + i] == (head + s)[head.len() + i]);
    }
}

/// An encoded token decodes to itself, wherever its bytes sit in the input
/// and whatever follows.
pub proof fn lemma_decode_token_encode_token(token: Token, b: Seq<u8>, pos: nat)
    requires
        token_ok(token),
        pos + encode_token(token).len() <= b.len(),
        b.subrange(pos as int, (pos + encode_token(token).len()) as int) =~= encode_token(token),
    ensures
        decode_token(b, pos) == Some((token, encode_token(token).len())),
{
    let enc = encode_token(token);
    match token {
        Token::Uint(n) => {
            lemma_decode_head_encode_head(0, n as nat, b, pos);
        },
        Token::Array(n) => {
            lemma_decode_head_encode_head(4, n as nat, b, pos);
        },
        Token::Bool(v) => {
            assert(enc.len() == 1);
            assert(b[pos as int] == enc[0]);
        },
        Token::Bytes(s) => {
            let head = encode_head(2, s.len());
            lemma_head_len(2, s.len());
            assert(b.subrange(pos as int, (pos + head.len()) as int) =~= head);
            lemma_decode_head_encode_head(2, s.len(), b, pos);
            lemma_payload(b, pos, head, s);
        },
        Token::Text(s) => {
            let head = encode_head(3, s.len());
            lemma_head_len(3, s.len());
            assert(b.subrange(pos as int, (pos + head.len()) as int) =~= head);
            lemma_decode_head_encode_head(3, s.len(), b, pos);
            lemma_payload(b, pos, head, s);
        },
    }
}

/// A head is at least one byte.
pub proof fn lemma_head_len(major: u8, value: nat)
    ensures
        encode_head(major, value).len() >= 1,
{
    lemma_be_bytes_len(value, 1);
    lemma_be_bytes_len(value, 2);
    lemma_be_bytes_len(value, 4);
    lemma_be_bytes_len(value, 8);
}

// ---------------------------------------------------------------------------
// Items: decode inverts encode, encode inverts decode.
// ---------------------------------------------------------------------------

/// `encode` of a concatenation is the concatenation of the `encode`s.
pub proof fn lemma_encode_append(a: Seq<Token>, c: Seq<Token>)
    ensures
        encode(a + c) =~= encode(a) + encode(c),
    decreases a.len()
{
    if a.len() == 0 {
        assert(a + c =~= c);
    } else {
        lemma_encode_append(a.drop_first(), c);
        assert((a + c).drop_first() =~= a.drop_first() + c);
        assert((a + c)[0] == a[0]);
        assert(encode_token(a[0]) + (encode(a.drop_first()) + encode(c)) =~= (encode_token(a[0]) + encode(a.drop_first())) + encode(c));
    }
}

/// Dropping a known prefix leaves the rest.
proof fn lemma_drop_prefix<T>(s: Seq<T>, a: Seq<T>, c: Seq<T>)
    requires
        s =~= a + c,
    ensures
        s.subrange(a.len() as int, s.len() as int) =~= c,
{
    let t = s.subrange(a.len() as int, s.len() as int);
    assert(t.len() == c.len());
    assert forall|i: int| 0 <= i < c.len() implies t[i] == c[i] by {
        assert(s[a.len() + i] == (a + c)[a.len() + i]);
    }
}

/// Decoding the encoding of `toks` (which are `pending` data items), found
/// at `pos` and filling the input to its end, reads exactly `toks`.
pub proof fn lemma_decode_from_encode(toks: Seq<Token>, pending: nat, b: Seq<u8>, pos: nat, acc: Seq<Token>)
    requires
        is_items(toks, pending),
        pos + encode(toks).len() == b.len(),
        b.subrange(pos as int, b.len() as int) =~= encode(toks),
    ensures
        decode_from(b, pos, pending, acc) == Some(acc + toks),
    decreases toks.len()
{
    if toks.len() == 0 {
        assert(encode(toks) =~= Seq::<u8>::empty());
        assert(acc + toks =~= acc);
    } else {
        let token = toks[0];
        let rest = toks.drop_first();
        let enc = encode_token(token);
        assert(encode(toks) == enc + encode(rest));
        assert(b.subrange(pos as int, (pos + enc.len()) as int) =~= enc);
        lemma_decode_token_encode_token(token, b, pos);
        lemma_head_len_token(token);
        lemma_drop_prefix(b.subrange(pos as int, b.len() as int), enc, encode(rest));
        assert(b.subrange((pos + enc.len()) as int, b.len() as int) =~= b.subrange(pos as int, b.len() as int).subrange(
            enc.len() as int,
            b.subrange(pos as int, b.len() as int).len() as int,
        ));
        lemma_decode_from_encode(rest, pending_after(pending, token), b, pos + enc.len(), acc.push(token));
        assert(acc.push(token) + rest =~= acc + toks);
    }
}

/// Every token's encoding is at least one byte.
pub proof fn lemma_head_len_token(token: Token)
    ensures
        encode_token(token).len() >= 1,
{
    match token {
        Token::Uint(n) => lemma_head_len(0, n as nat),
        Token::Array(n) => lemma_head_len(4, n as nat),
        Token::Bytes(s) => lemma_head_len(2, s.len()),
        Token::Text(s) => lemma_head_len(3, s.len()),
        Token::Bool(_) => {},
    }
}

/// Decode inverts encode: every data item of the profile decodes from its
/// encoding to itself.
pub proof fn lemma_decode_encode(item: Seq<Token>)
    ensures
        is_item(item) ==> decode(encode(item)) == Some(item),
{
    if is_item(item) {
        lemma_decode_from_encode(item, 1, encode(item), 0, seq![]);
        assert(Seq::<Token>::empty() + item =~= item);
        assert(encode(item).subrange(0, encode(item).len() as int) =~= encode(item));
    }
}

/// The argument of a head is at most 8 bytes, so it fits in 64 bits and
/// `value as u64` in [`decode_token`] loses nothing.
pub proof fn lemma_argument_fits_u64(b: Seq<u8>, pos: nat)
    ensures
        match decode_head(b, pos) {
            Some((_, value, _)) => value < 0x1_0000_0000_0000_0000,
            None => true,
        },
{
    lemma_decode_head_canonical(b, pos);
}

/// What decoding reads: from `pos`, `pending` data items, whose tokens are
/// appended to `acc`. The tokens read are exactly the data items whose
/// preferred serialization is the rest of the input, and there are at most
/// as many as there are bytes left.
pub proof fn lemma_decode_from_canonical(b: Seq<u8>, pos: nat, pending: nat, acc: Seq<Token>)
    ensures
        match decode_from(b, pos, pending, acc) {
            Some(r) => {
                &&& pos <= b.len()
                &&& pending <= b.len() - pos
                &&& acc.len() <= r.len()
                &&& r.subrange(0, acc.len() as int) =~= acc
                &&& is_items(r.skip(acc.len() as int), pending)
                &&& encode(r.skip(acc.len() as int)) =~= b.subrange(pos as int, b.len() as int)
                &&& r.len() - acc.len() <= b.len() - pos
            },
            None => true,
        },
    decreases b.len() - pos
{
    if let Some(r) = decode_from(b, pos, pending, acc) {
        if pending == 0 {
            assert(r == acc);
            assert(r.skip(acc.len() as int) =~= Seq::<Token>::empty());
            assert(b.subrange(pos as int, b.len() as int) =~= Seq::<u8>::empty());
        } else {
            lemma_decode_token_progress_pub(b, pos);
            lemma_decode_token_canonical(b, pos);
            let (token, len) = decode_token(b, pos).unwrap();
            let next = pending_after(pending, token);
            let acc2 = acc.push(token);
            lemma_decode_from_canonical(b, pos + len, next, acc2);
            let tail = r.skip(acc2.len() as int);
            // The tokens read from here are `token` followed by `tail`.
            assert(r.subrange(0, acc.len() as int) =~= acc);
            assert(r.subrange(0, acc2.len() as int) =~= acc2);
            assert(acc2[acc.len() as int] == token);
            assert(r.subrange(0, acc2.len() as int)[acc.len() as int] == acc2[acc.len() as int]);
            assert(r[acc.len() as int] == token);
            assert(r.skip(acc.len() as int)[0] == token);
            assert(r.skip(acc.len() as int).drop_first() =~= tail);
            assert(r.skip(acc.len() as int) =~= seq![token] + tail);
            assert(encode(r.skip(acc.len() as int)) =~= encode_token(token) + encode(tail));
            assert(encode_token(token) + b.subrange((pos + len) as int, b.len() as int)
                =~= b.subrange(pos as int, b.len() as int));
            match token {
                Token::Array(n) => {},
                _ => {},
            }
        }
    }
}

/// A token that decodes takes at least one byte (re-export of the fact the
/// spec's termination proof uses).
proof fn lemma_decode_token_progress_pub(b: Seq<u8>, pos: nat)
    ensures
        match decode_token(b, pos) {
            Some((_, len)) => len >= 1 && pos + len <= b.len(),
            None => true,
        },
{
    super::termination::lemma_decode_token_progress(b, pos);
}

/// Encode inverts decode wherever decode succeeds: the profile is
/// canonical. The tokens are one data item, and the input is their
/// preferred serialization, byte for byte.
pub proof fn lemma_encode_decode(b: Seq<u8>)
    ensures
        match decode(b) {
            Some(item) => is_item(item) && encode(item) =~= b,
            None => true,
        },
{
    lemma_decode_from_canonical(b, 0, 1, seq![]);
    if let Some(item) = decode(b) {
        assert(item.skip(0) =~= item);
        assert(b.subrange(0, b.len() as int) =~= b);
    }
}

/// No two byte strings decode to the same item: the profile has no parser
/// differentials between kernel and renderer.
pub proof fn lemma_decode_injective(a: Seq<u8>, b: Seq<u8>)
    requires
        decode(a) is Some,
        decode(a) == decode(b),
    ensures
        a =~= b,
{
    lemma_encode_decode(a);
    lemma_encode_decode(b);
}

/// The decoder never produces more tokens than there are bytes, and never
/// owes more items than there are bytes left (so a declared array length of
/// 2^64 fails at once instead of reserving memory).
pub proof fn lemma_decode_alloc_bound(b: Seq<u8>)
    ensures
        match decode(b) {
            Some(item) => item.len() <= b.len(),
            None => true,
        },
{
    lemma_decode_from_canonical(b, 0, 1, seq![]);
}

/// A loop that owes more items than there are bytes left cannot succeed.
pub proof fn lemma_pending_exceeds_remaining(b: Seq<u8>, pos: nat, pending: nat, acc: Seq<Token>)
    requires
        pending > b.len() - pos,
    ensures
        decode_from(b, pos, pending, acc) is None,
{
    lemma_decode_from_canonical(b, pos, pending, acc);
}

} // verus!
