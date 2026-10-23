//! Executable lists (§5.6.1): the comma-separated pieces of a field value.
//! Each function is proven to meet [`super::contract`].

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

use super::string::{at, copy, strip_ows};

verus! {

/// All the pieces of the comma-separated list `input`, empty ones
/// included, each stripped of OWS (§5.6.1).
pub fn split_values(input: &[u8]) -> (out: Vec<Vec<u8>>)
    ensures
        super::contract::split_values_ensures(input@, super::types::strings_view(out@)),
{
    assert(input@.skip(0) =~= input@);
    let mut acc: Vec<Vec<u8>> = Vec::new();
    let mut cur: Vec<u8> = Vec::new();
    assert(super::types::strings_view(acc@) =~= Seq::<Seq<u8>>::empty());
    let mut state = QState::Plain;
    let mut i: usize = 0;
    while i < input.len()
        invariant
            i <= input.len(),
            super::spec::split_values(input@) == split_scan(input@.skip(i as int), state, cur@, super::types::strings_view(acc@)),
        decreases input.len() - i,
    {
        let c = match at(input, i) {
            Some(c) => c,
            None => {
                // Unreachable: i < input.len().
                assert(false);
                0
            },
        };
        assert(input@.skip(i as int)[0] == input@[i as int]);
        assert(input@.skip(i as int).drop_first() =~= input@.skip(i as int + 1));
        match state {
            QState::Plain => {
                if c == 0x2C {
                    let piece = strip_ows(cur.as_slice());
                    let ghost before = super::types::strings_view(acc@);
                    acc.push(piece);
                    assert(super::types::strings_view(acc@) =~= before.push(super::spec::strip_ows(cur@)));
                    cur = Vec::new();
                } else if c == 0x22 {
                    state = QState::Quoted;
                    cur.push(c);
                } else {
                    cur.push(c);
                }
            },
            QState::Quoted => {
                if c == 0x5C {
                    state = QState::Escaped;
                    cur.push(c);
                } else if c == 0x22 {
                    state = QState::Plain;
                    cur.push(c);
                } else {
                    cur.push(c);
                }
            },
            QState::Escaped => {
                state = QState::Quoted;
                cur.push(c);
            },
        }
        // Never saturates: i < input.len().
        i = i.saturating_add(1);
    }
    assert(input@.skip(i as int).len() == 0);
    let piece = strip_ows(cur.as_slice());
    let ghost before = super::types::strings_view(acc@);
    acc.push(piece);
    assert(super::types::strings_view(acc@) =~= before.push(super::spec::strip_ows(cur@)));
    acc
}

/// The elements of `#element` (§5.6.1.2): the pieces without the empty ones.
pub fn list_elements(input: &[u8]) -> (out: Vec<Vec<u8>>)
    ensures
        super::contract::list_elements_ensures(input@, super::types::strings_view(out@)),
{
    let pieces = split_values(input);
    let ghost view = super::types::strings_view(pieces@);
    assert(view.take(0) =~= Seq::<Seq<u8>>::empty());
    let mut out: Vec<Vec<u8>> = Vec::new();
    let mut i: usize = 0;
    while i < pieces.len()
        invariant
            i <= pieces.len(),
            view == super::types::strings_view(pieces@),
            super::types::strings_view(out@) == drop_empty(view.take(i as int)),
        decreases pieces.len() - i,
    {
        if let Some(piece) = pieces.get(i) {
            proof {
                super::lemmas::lemma_drop_empty_push(view.take(i as int), piece@);
            }
            assert(view.take(i as int + 1) =~= view.take(i as int).push(piece@));
            if !piece.is_empty() {
                let ghost before = super::types::strings_view(out@);
                out.push(copy(piece.as_slice()));
                assert(super::types::strings_view(out@) =~= before.push(piece@));
            }
        }
        // Never saturates: i < pieces.len().
        i = i.saturating_add(1);
    }
    assert(view.take(pieces.len() as int) =~= view);
    out
}

} // verus!
