//! A second transcription of the profile, from RFC 7049 (the original CBOR
//! specification, 2013) §2 "CBOR Data Models" and §2.1 "Major Types", the
//! decoder pseudocode of Appendix C, and §3.9 "Canonical CBOR" (integers
//! "as small as possible"), plus Unicode Table 3-7 for text strings through
//! `clazel-encoding`'s own independent UTF-8 transcription.
//!
//! It differs from [`super::spec`] in form, to give a misreading no place to
//! hide twice:
//! - bit operations (`ib >> 5`, `ib & 0x1f`, as Appendix C writes them)
//!   instead of division and remainder;
//! - the width of an argument is `2^(ai - 24)` (RFC 7049 §2.1: "the
//!   following 1, 2, 4 or 8 bytes");
//! - the number in the argument bytes is accumulated from the front
//!   ([`be_front`]), where the spec reads it from the back;
//! - "as small as possible" (§3.9) is the function [`class_of`] that names
//!   the smallest argument form for a value, which the additional
//!   information must equal, where the spec lists lower bounds;
//! - decoding is recursive on the *rest of the input* (`b.skip(k)`), and
//!   builds the token list by prepending, where the spec carries a
//!   position and an accumulator;
//! - text validity is Unicode's "ill-formed code unit sequence" (D84, C10).
//!
//! It was written from the standards above and from the item's description
//! in the plan; the same agent also wrote `spec.rs`, so the two are not
//! independent in the way two people's would be. That is why the
//! conformance tests, which draw on sources outside the project, carry the
//! weight (docs/VERIFICATION.md).
//!
//! Proven equal to [`super::spec::decode`] on every input
//! ([`lemma_equals_decode`]) and to [`super::spec::is_item`] ([`lemma_ind_is_item`]).

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// 2^n.
pub open spec fn pow2(n: nat) -> nat
    decreases n
{
    if n == 0 {
        1
    } else {
        2 * pow2((n - 1) as nat)
    }
}

/// 256^n.
pub open spec fn pow256i(n: nat) -> nat
    decreases n
{
    if n == 0 {
        1
    } else {
        256 * pow256i((n - 1) as nat)
    }
}

/// The unsigned integer in `s`, network byte order, accumulated from the
/// first byte: the first byte times 256^(rest) plus the rest's value.
pub open spec fn be_front(s: Seq<u8>) -> nat
    decreases s.len()
{
    if s.len() == 0 {
        0
    } else {
        s[0] as nat * pow256i((s.len() - 1) as nat) + be_front(s.drop_first())
    }
}

/// RFC 7049 §2.1: an argument of additional information 24 to 27 is "1, 2,
/// 4 or 8 bytes" long, `2^(ai - 24)`; below 24 it is in the byte itself.
pub open spec fn ind_width(ai: u8) -> Option<nat> {
    if ai < 24 {
        Some(0)
    } else if ai <= 27 {
        Some(pow2((ai - 24) as nat))
    } else {
        None
    }
}

/// §3.9: the smallest additional information that can hold `v` (for
/// `v >= 24`): 24 if it fits in 1 byte, 25 in 2, 26 in 4, else 27.
pub open spec fn class_of(v: nat) -> u8 {
    if v < pow256i(1) {
        24
    } else if v < pow256i(2) {
        25
    } else if v < pow256i(4) {
        26
    } else {
        27
    }
}

/// Appendix C's first lines: the major type and additional information of
/// the first byte of `s`, the argument, and the head's length, with §3.9's
/// "as small as possible" required.
pub open spec fn ind_head(s: Seq<u8>) -> Option<(u8, nat, nat)> {
    if s.len() == 0 {
        None
    } else {
        let ib = s[0];
        let mt = ib >> 5;
        let ai = ib & 0x1f;
        match ind_width(ai) {
            None => None,
            Some(w) => {
                if s.len() < 1 + w {
                    None
                } else {
                    let v = if ai < 24 { ai as nat } else { be_front(s.subrange(1, 1 + w as int)) };
                    if ai >= 24 && !(v >= 24 && class_of(v) == ai) {
                        None
                    } else {
                        Some((mt, v, 1 + w))
                    }
                }
            },
        }
    }
}

/// Text is well formed when Unicode's conversion (C10) does not fail.
pub open spec fn ind_text_ok(s: Seq<u8>) -> bool {
    clazel_encoding::utf8::independent::unicode_decode_or_error(s) is Some
}

/// One data item's first token of `s`, and the length of the bytes it
/// takes (Appendix C: "decode_item", for the profile's major types).
pub open spec fn ind_token(s: Seq<u8>) -> Option<(Token, nat)> {
    if s.len() == 0 {
        None
    } else {
        let ib = s[0];
        let mt = ib >> 5;
        let ai = ib & 0x1f;
        if mt == 7 {
            if ai == 20 {
                Some((Token::Bool(false), 1))
            } else if ai == 21 {
                Some((Token::Bool(true), 1))
            } else {
                None
            }
        } else if mt == 0 {
            match ind_head(s) {
                Some((_, v, hl)) => Some((Token::Uint(v as u64), hl)),
                None => None,
            }
        } else if mt == 4 {
            match ind_head(s) {
                Some((_, v, hl)) => Some((Token::Array(v as u64), hl)),
                None => None,
            }
        } else if mt == 2 || mt == 3 {
            match ind_head(s) {
                Some((_, v, hl)) => {
                    if s.len() < hl + v {
                        None
                    } else {
                        let body = s.subrange(hl as int, (hl + v) as int);
                        if mt == 2 {
                            Some((Token::Bytes(body), hl + v))
                        } else if ind_text_ok(body) {
                            Some((Token::Text(body), hl + v))
                        } else {
                            None
                        }
                    }
                },
                None => None,
            }
        } else {
            None
        }
    }
}

/// How many items are owed after `token`, given `n` before it.
pub open spec fn ind_owed(n: nat, token: Token) -> nat {
    match token {
        Token::Array(k) => (n - 1 + k as nat) as nat,
        _ => (n - 1) as nat,
    }
}

/// The tokens of exactly `n` items filling `s`, or `None`. Recursive on the
/// rest of the input; the tokens are built by prepending.
pub open spec fn ind_items(s: Seq<u8>, n: nat) -> Option<Seq<Token>>
    decreases s.len() via ind_items_decreases
{
    if n == 0 {
        if s.len() == 0 {
            Some(seq![])
        } else {
            None
        }
    } else {
        match ind_token(s) {
            None => None,
            Some((token, k)) => match ind_items(s.skip(k as int), ind_owed(n, token)) {
                Some(rest) => Some(seq![token] + rest),
                None => None,
            },
        }
    }
}

/// Termination of [`ind_items`]: a token takes at least one byte and no
/// more than there are.
#[via_fn]
pub proof fn ind_items_decreases(s: Seq<u8>, n: nat) {
    lemma_ind_token_progress(s);
}

/// A token that decodes takes at least one byte and ends within `s`.
pub proof fn lemma_ind_token_progress(s: Seq<u8>)
    ensures
        match ind_token(s) {
            Some((_, k)) => k >= 1 && k <= s.len(),
            None => true,
        },
{
}

/// The independent decoder: one item filling the input.
pub open spec fn ind_decode(b: Seq<u8>) -> Option<Seq<Token>> {
    ind_items(b, 1)
}

/// Whether `tokens` are exactly `n` items, each one the profile allows
/// (§3.9: each item "as small as possible" is a property of the bytes, so
/// here a token needs only to be representable).
pub open spec fn ind_is_items(tokens: Seq<Token>, n: nat) -> bool
    decreases tokens.len()
{
    if tokens.len() == 0 {
        n == 0
    } else {
        n > 0 && match tokens[0] {
            Token::Bytes(s) => s.len() < pow256i(8),
            Token::Text(s) => s.len() < pow256i(8) && ind_text_ok(s),
            _ => true,
        } && ind_is_items(tokens.drop_first(), ind_owed(n, tokens[0]))
    }
}

// ---------------------------------------------------------------------------
// The proofs of equality.
// ---------------------------------------------------------------------------

/// `pow256i` is `pow256`, and `pow2` and `pow256i` agree on bytes.
pub proof fn lemma_pow256i_eq(n: nat)
    ensures
        pow256i(n) == super::lemmas::pow256(n),
    decreases n
{
    if n > 0 {
        lemma_pow256i_eq((n - 1) as nat);
    }
}

/// Reading from the front or from the back gives the same number.
pub proof fn lemma_be_front_eq(s: Seq<u8>)
    ensures
        be_front(s) == be_value(s),
    decreases s.len()
{
    if s.len() > 0 {
        lemma_be_value_cons(s[0], s.drop_first());
        assert(s =~= seq![s[0]] + s.drop_first());
        lemma_be_front_eq(s.drop_first());
        lemma_pow256i_eq((s.len() - 1) as nat);
    }
}

/// The number spelled by a first byte and the rest.
pub proof fn lemma_be_value_cons(x: u8, t: Seq<u8>)
    ensures
        be_value(seq![x] + t) == x as nat * super::lemmas::pow256(t.len()) + be_value(t),
    decreases t.len()
{
    let s = seq![x] + t;
    if t.len() == 0 {
        assert(s.drop_last() =~= Seq::<u8>::empty());
        assert(s.last() == x);
        assert(s.len() == 1);
        assert(be_value(Seq::<u8>::empty()) == 0);
        assert(t =~= Seq::<u8>::empty());
        assert(super::lemmas::pow256(0) == 1);
        assert(be_value(s) == be_value(s.drop_last()) * 256 + x as nat);
    } else {
        let dl = t.drop_last();
        lemma_be_value_cons(x, dl);
        assert(s.drop_last() =~= seq![x] + dl);
        assert(s.last() == t.last());
        assert(super::lemmas::pow256(t.len()) == 256 * super::lemmas::pow256(dl.len()));
        assert(be_value(s) == be_value(seq![x] + dl) * 256 + t.last() as nat);
        assert(be_value(t) == be_value(dl) * 256 + t.last() as nat);
        assert(be_value(seq![x] + dl) == x as nat * super::lemmas::pow256(dl.len()) + be_value(dl));
        assert(be_value(s) == x as nat * super::lemmas::pow256(t.len()) + be_value(t)) by (nonlinear_arith)
            requires
                be_value(s) == be_value(seq![x] + dl) * 256 + t.last() as nat,
                be_value(t) == be_value(dl) * 256 + t.last() as nat,
                be_value(seq![x] + dl) == x as nat * super::lemmas::pow256(dl.len()) + be_value(dl),
                super::lemmas::pow256(t.len()) == 256 * super::lemmas::pow256(dl.len()),
        ;
    }
}

/// The shift and mask are the division and remainder.
pub proof fn lemma_shift_mask(ib: u8)
    ensures
        ib >> 5 == ib / 32,
        ib & 0x1f == ib % 32,
{
    assert(ib >> 5 == ib / 32) by (bit_vector);
    assert(ib & 0x1f == ib % 32) by (bit_vector);
}

/// The widths of an argument are the same.
pub proof fn lemma_width_eq(ai: u8)
    ensures
        ind_width(ai) == argument_bytes(ai),
{
    assert(pow2(0) == 1 && pow2(1) == 2 && pow2(2) == 4 && pow2(3) == 8) by (compute_only);
}

/// "As small as possible" by [`class_of`] is the spec's lower bounds, for
/// a value that fits the argument's width.
pub proof fn lemma_shortest_eq(ai: u8, v: nat)
    requires
        24 <= ai <= 27,
        v < pow256i(ind_width(ai).unwrap()),
    ensures
        (v >= 24 && class_of(v) == ai) == is_shortest(ai, v),
{
    assert(pow256i(1) == 256 && pow256i(2) == 65536 && pow256i(4) == 4294967296 && pow256i(8) == 0x1_0000_0000_0000_0000)
        by (compute_only);
    assert(pow2(0) == 1 && pow2(1) == 2 && pow2(2) == 4 && pow2(3) == 8) by (compute_only);
}

/// The two head parsers agree at `pos`.
pub proof fn lemma_ind_head_eq(b: Seq<u8>, pos: nat)
    requires
        pos <= b.len(),
    ensures
        ind_head(b.skip(pos as int)) == decode_head(b, pos),
{
    let s = b.skip(pos as int);
    if pos < b.len() {
        let ib = b[pos as int];
        assert(s[0] == ib);
        lemma_shift_mask(ib);
        let ai = additional_info(ib);
        lemma_width_eq(ai);
        if let Some(w) = argument_bytes(ai) {
            if pos + 1 + w <= b.len() {
                let extra = b.subrange(pos as int + 1, (pos + 1 + w) as int);
                assert(s.subrange(1, 1 + w as int) =~= extra);
                if ai >= 24 {
                    lemma_be_front_eq(extra);
                    super::lemmas::lemma_be_value_bound(extra);
                    lemma_pow256i_eq(w);
                    lemma_shortest_eq(ai, be_value(extra));
                }
            }
        }
    }
}

/// The two token parsers agree at `pos`.
pub proof fn lemma_ind_token_eq(b: Seq<u8>, pos: nat)
    requires
        pos <= b.len(),
    ensures
        ind_token(b.skip(pos as int)) == decode_token(b, pos),
{
    let s = b.skip(pos as int);
    if pos < b.len() {
        let ib = b[pos as int];
        assert(s[0] == ib);
        lemma_shift_mask(ib);
        lemma_ind_head_eq(b, pos);
        if let Some((_, v, hl)) = decode_head(b, pos) {
            if (major_type(ib) == 2 || major_type(ib) == 3) && pos + hl + v <= b.len() {
                let body = b.subrange((pos + hl) as int, (pos + hl + v) as int);
                assert(s.subrange(hl as int, (hl + v) as int) =~= body);
                clazel_encoding::utf8::independent::lemma_equals_utf8_decode_without_bom_or_fail(body);
            }
        }
    }
}

/// Reading `n` items from `pos` and prepending is reading them from the
/// rest of the input and appending to what was read.
pub proof fn lemma_items_eq(b: Seq<u8>, pos: nat, n: nat, acc: Seq<Token>)
    requires
        pos <= b.len(),
    ensures
        decode_from(b, pos, n, acc) == match ind_items(b.skip(pos as int), n) {
            Some(t) => Some(acc + t),
            None => None,
        },
    decreases b.len() - pos
{
    let s = b.skip(pos as int);
    if n == 0 {
        assert(s.len() == b.len() - pos);
        assert(acc + Seq::<Token>::empty() =~= acc);
    } else {
        lemma_ind_token_eq(b, pos);
        super::termination::lemma_decode_token_progress(b, pos);
        if let Some((token, k)) = decode_token(b, pos) {
            assert(ind_owed(n, token) == pending_after(n, token));
            lemma_items_eq(b, pos + k, pending_after(n, token), acc.push(token));
            assert(b.skip((pos + k) as int) =~= s.skip(k as int));
            if let Some(rest) = ind_items(s.skip(k as int), ind_owed(n, token)) {
                assert(acc.push(token) + rest =~= acc + (seq![token] + rest));
            }
        }
    }
}

/// The independent decoder equals the spec's, on every input.
pub proof fn lemma_equals_decode(b: Seq<u8>)
    ensures
        ind_decode(b) == decode(b),
{
    lemma_items_eq(b, 0, 1, seq![]);
    assert(b.skip(0) =~= b);
    if let Some(t) = ind_items(b, 1) {
        assert(Seq::<Token>::empty() + t =~= t);
    }
}

/// The spec's "one item of the profile" is the independent one.
pub proof fn lemma_ind_is_item(tokens: Seq<Token>, n: nat)
    ensures
        ind_is_items(tokens, n) == is_items(tokens, n),
    decreases tokens.len()
{
    if tokens.len() > 0 {
        lemma_ind_is_item(tokens.drop_first(), ind_owed(n, tokens[0]));
        assert(ind_owed(n, tokens[0]) == pending_after(n, tokens[0]));
        match tokens[0] {
            Token::Text(s) => {
                clazel_encoding::utf8::independent::lemma_equals_utf8_decode_without_bom_or_fail(s);
                assert(pow256i(8) == 0x1_0000_0000_0000_0000) by (compute_only);
            },
            Token::Bytes(s) => {
                assert(pow256i(8) == 0x1_0000_0000_0000_0000) by (compute_only);
            },
            _ => {},
        }
    }
}

} // verus!
