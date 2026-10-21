//! The executable decoder, proven to meet [`super::contract`].
//!
//! It follows [`super::spec`] step by step (the step comments and quotes
//! live there): the loop of `decode_from` is a `while` loop, and an
//! array's declared length is never used to reserve memory.

use super::token::*;
#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// §3: the `width` bytes at `pos` as an unsigned integer in network byte
/// order. The recursion is [`be_value`]'s: the last byte is the least
/// significant.
pub(crate) fn read_be(input: &[u8], pos: usize, width: usize) -> (value: u64)
    requires
        width <= 8,
        pos + width <= input.len(),
    ensures
        value as nat == be_value(input@.subrange(pos as int, pos as int + width as int)),
    decreases width,
{
    if width == 0 {
        assert(input@.subrange(pos as int, pos as int) =~= Seq::<u8>::empty());
        return 0;
    }
    let ghost whole = input@.subrange(pos as int, pos as int + width as int);
    let ghost init = input@.subrange(pos as int, pos as int + width as int - 1);
    assert(whole.drop_last() =~= init);
    // Never saturates: width >= 1.
    let before = width.saturating_sub(1);
    let high = read_be(input, pos, before);
    proof {
        super::lemmas::lemma_be_value_bound(init);
        super::lemmas::lemma_pow256_at_most_8(width as nat);
        assert(super::lemmas::pow256(width as nat) == 256 * super::lemmas::pow256(before as nat));
        assert(high as nat * 256 + 255 <= 0xFFFF_FFFF_FFFF_FFFF);
    }
    // Never saturates: pos + width <= input.len(), so the index is in range.
    let index = pos.saturating_add(before);
    let last = match input.get(index) {
        Some(&b) => b,
        None => 0,
    };
    assert(whole.last() == input@[index as int]);
    // Never saturates: high * 256 + last <= 2^64 - 1 (shown above).
    high.saturating_mul(256).saturating_add(last as u64)
}

/// §3 and §4.2.1: the initial byte and argument at `pos`.
fn decode_head(input: &[u8], pos: usize) -> (r: Option<(u8, u64, usize)>)
    ensures
        match r {
            Some((major, value, len)) => super::spec::decode_head(input@, pos as nat) == Some((major, value as nat, len as nat)),
            None => super::spec::decode_head(input@, pos as nat) is None,
        },
{
    let ib = match input.get(pos) {
        Some(&b) => b,
        None => return None,
    };
    let ai = ib % 32;
    let major = ib / 32;
    let width: usize = if ai < 24 {
        0
    } else if ai == 24 {
        1
    } else if ai == 25 {
        2
    } else if ai == 26 {
        4
    } else if ai == 27 {
        8
    } else {
        return None;
    };
    // pos < input.len() since get succeeded, so this does not saturate.
    let after_initial = input.len().saturating_sub(pos).saturating_sub(1);
    if width > after_initial {
        return None;
    }
    let value: u64 = if ai < 24 {
        ai as u64
    } else {
        // Never saturates: pos + 1 + width <= input.len().
        read_be(input, pos.saturating_add(1), width)
    };
    let shortest = if ai < 24 {
        true
    } else if ai == 24 {
        value >= 24
    } else if ai == 25 {
        value >= 256
    } else if ai == 26 {
        value >= 65536
    } else {
        value >= 4294967296
    };
    if !shortest {
        return None;
    }
    // Never saturates: width <= 8.
    Some((major, value, width.saturating_add(1)))
}

/// §3: the token at `pos` and its length in bytes, payload included.
fn decode_token(input: &[u8], pos: usize) -> (r: Option<(Tok, usize)>)
    ensures
        match r {
            Some((token, len)) => super::spec::decode_token(input@, pos as nat) == Some((token@, len as nat)),
            None => super::spec::decode_token(input@, pos as nat) is None,
        },
{
    let ib = match input.get(pos) {
        Some(&b) => b,
        None => return None,
    };
    let major = ib / 32;
    if major == 7 {
        // 7.
        let ai = ib % 32;
        if ai == 20 {
            return Some((Tok::Bool(false), 1));
        } else if ai == 21 {
            return Some((Tok::Bool(true), 1));
        } else {
            return None;
        }
    }
    if !(major == 0 || major == 2 || major == 3 || major == 4) {
        // 1, 5, 6.
        return None;
    }
    let (_, value, head_len) = decode_head(input, pos)?;
    if major == 0 {
        // 0.
        return Some((Tok::Uint(value), head_len));
    }
    if major == 4 {
        // 4.
        return Some((Tok::Array(value), head_len));
    }
    // 2, 3. `rest` is the number of bytes after the head.
    let rest = input.len().saturating_sub(pos).saturating_sub(head_len);
    if value > rest as u64 {
        return None;
    }
    // value <= rest <= usize::MAX, so this is exact.
    let count = value as usize;
    let start = pos.saturating_add(head_len);
    let end = start.saturating_add(count);
    let payload = vstd::slice::slice_to_vec(vstd::slice::slice_subrange(input, start, end));
    if major == 2 {
        // 2.
        // Never saturates: head_len + count <= input.len() - pos.
        return Some((Tok::Bytes(payload), head_len.saturating_add(count)));
    }
    // 3.
    clazel_encoding::utf8::decode::decode_without_bom_or_fail(payload.as_slice())?;
    Some((Tok::Text(payload), head_len.saturating_add(count)))
}

/// Decode a byte string as one data item of the profile: `None` unless it
/// is the preferred serialization of exactly one. Never reserves more
/// tokens than there are bytes.
pub fn decode(input: &[u8]) -> (output: Option<Vec<Tok>>)
    ensures
        super::contract::decode_ensures(input@, option_views(output)),
        super::contract::decode_alloc_ensures(
            input@.len(),
            match output {
                Some(v) => Some(v@.len()),
                None => None,
            },
        ),
{
    let mut pos: usize = 0;
    // The number of data items still owed.
    let mut pending: u64 = 1;
    let mut acc: Vec<Tok> = Vec::new();
    proof {
        assert(views(acc@) =~= Seq::<super::spec::Token>::empty());
    }
    while pending > 0
        invariant
            pos <= input.len(),
            acc@.len() <= pos,
            decode_from(input@, pos as nat, pending as nat, views(acc@)) == super::spec::decode(input@),
        decreases input.len() - pos,
    {
        // Each owed item takes a byte, so more than the bytes left cannot be
        // satisfied (this is what stops a huge declared length at once).
        // pos <= input.len(), so this does not saturate.
        let remaining = input.len().saturating_sub(pos);
        if pending > remaining as u64 {
            proof {
                super::lemmas::lemma_pending_exceeds_remaining(input@, pos as nat, pending as nat, views(acc@));
            }
            return None;
        }
        let (token, len) = decode_token(input, pos)?;
        proof {
            super::termination::lemma_decode_token_progress(input@, pos as nat);
        }
        // Never saturates: pos + len <= input.len().
        let after = pos.saturating_add(len);
        let rest_after = input.len().saturating_sub(after);
        // The owed count after this token: it discharges one, and an array
        // owes its elements.
        let next: u128 = match &token {
            Tok::Array(n) => (pending as u128).saturating_sub(1).saturating_add(*n as u128),
            _ => (pending as u128).saturating_sub(1),
        };
        proof {
            lemma_views_push(acc@, token);
        }
        if next > rest_after as u128 {
            proof {
                assert(pending_after(pending as nat, token@) == next as nat);
                super::lemmas::lemma_pending_exceeds_remaining(input@, after as nat, next as nat, views(acc@).push(token@));
            }
            return None;
        }
        proof {
            assert(pending_after(pending as nat, token@) == next as nat);
        }
        pending = next as u64;
        pos = after;
        acc.push(token);
    }
    if pos == input.len() {
        proof {
            super::lemmas::lemma_decode_alloc_bound(input@);
        }
        Some(acc)
    } else {
        None
    }
}

} // verus!
