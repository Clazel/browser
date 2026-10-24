//! Executable quoted strings (§5.6.4): reading a `quoted-string` and
//! writing one. Each function is proven to meet [`super::contract`].

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

use super::string::at;

verus! {

/// `qdtext` (§5.6.4).
fn is_qdtext_exec(c: u8) -> (r: bool)
    ensures
        r == is_qdtext(c),
{
    c == 0x09 || c == 0x20 || c == 0x21 || (0x23..=0x5B).contains(&c) || (0x5D..=0x7E).contains(&c) || c >= 0x80
}

/// The octet after the backslash of a `quoted-pair` (§5.6.4).
fn is_quoted_pair_octet_exec(c: u8) -> (r: bool)
    ensures
        r == is_quoted_pair_octet(c),
{
    c == 0x09 || c == 0x20 || (0x21..=0x7E).contains(&c) || c >= 0x80
}

/// `parse_quoted_string` (§5.6.4): the unquoted value, and the position
/// after the closing DQUOTE.
pub fn parse_quoted_string(input: &[u8]) -> (out: Option<(Vec<u8>, usize)>)
    ensures
        super::contract::parse_quoted_string_ensures(input@, match out {
            Some((v, p)) => Some((v@, p as nat)),
            None => None,
        }),
{
    if at(input, 0) != Some(0x22u8) {
        return None;
    }
    let ghost target = super::spec::parse_quoted_string(input@);
    let mut value: Vec<u8> = Vec::new();
    let mut pos: usize = 1;
    assert(input@.skip(1) =~= input@.drop_first());
    while pos < input.len()
        invariant
            1 <= pos <= input.len(),
            target == super::spec::parse_quoted_string(input@),
            target == quoted_body(input@.skip(pos as int), value@),
        decreases input.len() - pos,
    {
        let c = match at(input, pos) {
            Some(c) => c,
            None => {
                // Unreachable: pos < input.len().
                assert(false);
                0
            },
        };
        assert(input@.skip(pos as int)[0] == input@[pos as int]);
        assert(input@.skip(pos as int).drop_first() =~= input@.skip(pos as int + 1));
        if c == 0x22 {
            // Never saturates: pos < input.len().
            let end = pos.saturating_add(1);
            assert(end == pos + 1);
            assert(input@.skip(end as int) =~= input@.skip(pos as int).drop_first());
            assert(quoted_body(input@.skip(pos as int), value@) == Some((value@, input@.skip(pos as int).drop_first())));
            return Some((value, end));
        } else if c == 0x5C {
            // Never saturates: pos < input.len().
            let next = pos.saturating_add(1);
            match at(input, next) {
                Some(q) => {
                    assert(input@.skip(pos as int).len() >= 2);
                    assert(input@.skip(pos as int)[1] == input@[next as int]);
                    if !is_quoted_pair_octet_exec(q) {
                        return None;
                    }
                    assert(input@.skip(pos as int).drop_first().drop_first() =~= input@.skip(next as int + 1));
                    value.push(q);
                    // Never saturates: next < input.len().
                    pos = next.saturating_add(1);
                },
                None => {
                    assert(input@.skip(pos as int).len() < 2);
                    return None;
                },
            }
        } else {
            if !is_qdtext_exec(c) {
                return None;
            }
            value.push(c);
            // Never saturates: pos < input.len().
            pos = pos.saturating_add(1);
        }
    }
    assert(input@.skip(pos as int).len() == 0);
    None
}

/// `quote` (§5.6.4): `v` as a `quoted-string`, if every octet can be sent
/// in one.
pub fn quote(v: &[u8]) -> (out: Option<Vec<u8>>)
    ensures
        super::contract::quote_ensures(v@, match out {
            Some(o) => Some(o@),
            None => None,
        }),
{
    let quotable = super::string::all_in_exec(v, &Class::QuotedPair);
    if !quotable {
        return None;
    }
    let mut out: Vec<u8> = Vec::new();
    out.push(0x22);
    assert(v@.take(0) =~= Seq::<u8>::empty());
    let mut i: usize = 0;
    while i < v.len()
        invariant
            i <= v.len(),
            out@ == seq![0x22u8] + quote_octets(v@.take(i as int)),
        decreases v.len() - i,
    {
        let c = match at(v, i) {
            Some(c) => c,
            None => {
                // Unreachable: i < v.len().
                assert(false);
                0
            },
        };
        proof {
            super::lemmas::lemma_quote_octets_push(v@.take(i as int), c);
        }
        assert(v@.take(i as int + 1) =~= v@.take(i as int).push(c));
        if c == 0x22 || c == 0x5C {
            out.push(0x5C);
        }
        out.push(c);
        // Never saturates: i < v.len().
        i = i.saturating_add(1);
    }
    out.push(0x22);
    assert(v@.take(v.len() as int) =~= v@);
    assert(out@ =~= super::spec::quote(v@));
    Some(out)
}

} // verus!
