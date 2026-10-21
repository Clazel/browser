//! The executable token type: the exec twin of [`super::spec::Token`], whose
//! view it is. A data item is a `Vec<Tok>` in wire order (an array's token
//! is followed by its elements' tokens).

#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// One token of a data item in the profile; see [`super::spec::Token`].
#[derive(Debug, PartialEq, Eq)]
pub enum Tok {
    /// Major type 0: an unsigned integer.
    Uint(u64),
    /// Major type 2: a byte string.
    Bytes(Vec<u8>),
    /// Major type 3: a text string, as its UTF-8 bytes (valid UTF-8).
    Text(Vec<u8>),
    /// Major type 7: false or true.
    Bool(bool),
    /// Major type 4: an array of this many elements, whose tokens follow.
    Array(u64),
}

impl View for Tok {
    type V = super::spec::Token;

    open spec fn view(&self) -> super::spec::Token {
        match self {
            Tok::Uint(n) => super::spec::Token::Uint(*n),
            Tok::Bytes(v) => super::spec::Token::Bytes(v@),
            Tok::Text(v) => super::spec::Token::Text(v@),
            Tok::Bool(b) => super::spec::Token::Bool(*b),
            Tok::Array(n) => super::spec::Token::Array(*n),
        }
    }
}

/// The spec view of a token sequence.
pub open spec fn views(tokens: Seq<Tok>) -> Seq<super::spec::Token> {
    tokens.map_values(|t: Tok| t@)
}

/// The view of an optional item; `None` is failure.
pub open spec fn option_views(item: Option<Vec<Tok>>) -> Option<Seq<super::spec::Token>> {
    match item {
        Some(v) => Some(views(v@)),
        None => None,
    }
}

/// Pushing a token pushes its view.
pub proof fn lemma_views_push(tokens: Seq<Tok>, t: Tok)
    ensures
        views(tokens.push(t)) =~= views(tokens).push(t@),
{
    assert(views(tokens.push(t)).len() == tokens.len() + 1);
    assert forall|i: int| 0 <= i < tokens.len() + 1 implies views(tokens.push(t))[i] == views(tokens).push(t@)[i] by {
        if i < tokens.len() {
            assert(tokens.push(t)[i] == tokens[i]);
        }
    }
}

} // verus!
