//! The executable encoder, proven to meet [`super::contract`].
//!
//! It writes §4.2.1 preferred serialization: every argument in the
//! shortest form that holds it.

use super::token::*;
#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Append the `width` bytes spelling `value` in network byte order, most
/// significant first ([`be_bytes`]'s recursion).
fn push_be(out: &mut Vec<u8>, value: u64, width: usize)
    requires
        width <= 8,
        (value as nat) < super::lemmas::pow256(width as nat),
    ensures
        final(out)@ =~= old(out)@ + be_bytes(value as nat, width as nat),
    decreases width,
{
    if width == 0 {
        assert(be_bytes(value as nat, 0) =~= Seq::<u8>::empty());
        return;
    }
    // Never saturates: width >= 1.
    let before = width.saturating_sub(1);
    assert(super::lemmas::pow256(width as nat) == 256 * super::lemmas::pow256(before as nat));
    push_be(out, value / 256, before);
    out.push((value % 256) as u8);
    assert(out@ =~= old(out)@ + be_bytes(value as nat, width as nat));
}

/// Append the initial byte and argument of major type `major` and argument
/// `value` in preferred serialization (§4.2.1).
fn push_head(out: &mut Vec<u8>, major: u8, value: u64)
    requires
        major < 8,
    ensures
        final(out)@ =~= old(out)@ + encode_head(major, value as nat),
{
    proof {
        super::lemmas::lemma_pow256_8();
    }
    // Never saturates: major < 8.
    let base = major.saturating_mul(32);
    if value < 24 {
        // 0 to 23 in a single byte. Never saturates: base + value < 256.
        out.push(base.saturating_add(value as u8));
    } else if value < 256 {
        out.push(base.saturating_add(24));
        push_be(out, value, 1);
    } else if value < 65536 {
        out.push(base.saturating_add(25));
        push_be(out, value, 2);
    } else if value < 4294967296 {
        out.push(base.saturating_add(26));
        push_be(out, value, 4);
    } else {
        out.push(base.saturating_add(27));
        push_be(out, value, 8);
    }
    assert(out@ =~= old(out)@ + encode_head(major, value as nat));
}

/// Append the preferred serialization of one token.
fn push_token(out: &mut Vec<u8>, token: &Tok)
    ensures
        final(out)@ =~= old(out)@ + encode_token(token@),
{
    match token {
        Tok::Uint(n) => push_head(out, 0, *n),
        Tok::Array(n) => push_head(out, 4, *n),
        Tok::Bool(false) => out.push(244),
        Tok::Bool(true) => out.push(245),
        Tok::Bytes(s) => {
            push_head(out, 2, s.len() as u64);
            out.extend_from_slice(s.as_slice());
        },
        Tok::Text(s) => {
            push_head(out, 3, s.len() as u64);
            out.extend_from_slice(s.as_slice());
        },
    }
    assert(out@ =~= old(out)@ + encode_token(token@));
}

/// The preferred serialization of an item (§4.2.1).
pub fn encode(item: &[Tok]) -> (output: Vec<u8>)
    requires
        super::contract::encode_requires(views(item@)),
    ensures
        super::contract::encode_ensures(views(item@), output@),
{
    let mut out: Vec<u8> = Vec::new();
    let mut i: usize = 0;
    let ghost all = views(item@);
    proof {
        assert(all.subrange(0, 0) =~= Seq::<super::spec::Token>::empty());
    }
    while i < item.len()
        invariant
            i <= item.len(),
            all == views(item@),
            out@ =~= super::spec::encode(all.subrange(0, i as int)),
        decreases item.len() - i,
    {
        let ghost prefix = all.subrange(0, i as int);
        let ghost token = all[i as int];
        proof {
            assert(all.subrange(0, i as int + 1) =~= prefix.push(token));
            super::lemmas::lemma_encode_append(prefix, seq![token]);
            super::lemmas::lemma_encode_single(token);
            assert(prefix + seq![token] =~= prefix.push(token));
        }
        if let Some(t) = item.get(i) {
            push_token(&mut out, t);
        }
        proof {
            assert(item@[i as int]@ == token);
            assert(out@ =~= super::spec::encode(all.subrange(0, i as int + 1)));
        }
        // Never saturates: i < item.len().
        i = i.saturating_add(1);
    }
    assert(all.subrange(0, item.len() as int) =~= all);
    out
}

} // verus!
