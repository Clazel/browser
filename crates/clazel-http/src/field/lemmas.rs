//! Facts proven about the spec itself. They are evidence that the
//! transcription is right (docs/SPEC-STYLE.md), not part of what the
//! implementation must meet. The first group are the index forms of the
//! recursive definitions, which the executable loops use.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ===========================================================================
// Index forms of the recursive definitions.
// ===========================================================================

/// `all_in` says every octet is in the class.
pub proof fn lemma_all_in_index(s: Seq<u8>, class: Class)
    ensures
        all_in(s, class) <==> (forall|i: int| 0 <= i < s.len() ==> in_class(class, #[trigger] s[i])),
    decreases s.len()
{
    if s.len() > 0 {
        lemma_all_in_index(s.drop_first(), class);
        if all_in(s, class) {
            assert forall|i: int| 0 <= i < s.len() implies in_class(class, #[trigger] s[i]) by {
                if i > 0 {
                    assert(s.drop_first()[i - 1] == s[i]);
                }
            }
        }
        if forall|i: int| 0 <= i < s.len() ==> in_class(class, #[trigger] s[i]) {
            assert forall|j: int| 0 <= j < s.drop_first().len() implies in_class(class, #[trigger] s.drop_first()[j]) by {
                assert(s.drop_first()[j] == s[j + 1]);
            }
        }
    }
}

/// What `run_len` measures: the longest prefix whose octets are all in the
/// class.
pub proof fn lemma_run_len_props(class: Class, s: Seq<u8>)
    ensures
        run_len(class, s) <= s.len(),
        forall|j: int| 0 <= j < run_len(class, s) ==> in_class(class, #[trigger] s[j]),
        run_len(class, s) < s.len() ==> !in_class(class, s[run_len(class, s) as int]),
    decreases s.len()
{
    if s.len() > 0 && in_class(class, s[0]) {
        lemma_run_len_props(class, s.drop_first());
        let n = run_len(class, s.drop_first());
        assert forall|j: int| 0 <= j < run_len(class, s) implies in_class(class, #[trigger] s[j]) by {
            if j > 0 {
                assert(s.drop_first()[j - 1] == s[j]);
            }
        }
        if run_len(class, s) < s.len() {
            assert(s.drop_first()[n as int] == s[(n + 1) as int]);
        }
    }
}

/// Joining one more value: the first has nothing before it, the others
/// come after ", ".
pub proof fn lemma_combine_push(values: Seq<Seq<u8>>, v: Seq<u8>)
    ensures
        combine(values.push(v)) == if values.len() == 0 { v } else { combine(values) + seq![0x2Cu8, 0x20u8] + v },
    decreases values.len()
{
    let pushed = values.push(v);
    if values.len() >= 2 {
        lemma_combine_push(values.drop_first(), v);
        assert(pushed.drop_first() =~= values.drop_first().push(v));
        assert(pushed[0] == values[0]);
        assert(combine(pushed) =~= combine(values) + seq![0x2Cu8, 0x20u8] + v);
    } else if values.len() == 1 {
        assert(pushed.drop_first() =~= seq![v]);
        assert(combine(seq![v]) == v);
        assert(combine(values) == values[0]);
    } else {
        assert(pushed =~= seq![v]);
    }
}

/// Dropping empty members commutes with appending one.
pub proof fn lemma_drop_empty_push(v: Seq<Seq<u8>>, e: Seq<u8>)
    ensures
        drop_empty(v.push(e)) == drop_empty(v) + (if e.len() == 0 { seq![] } else { seq![e] }),
    decreases v.len()
{
    let pushed = v.push(e);
    if v.len() == 0 {
        assert(pushed =~= seq![e]);
        assert(pushed.drop_first() =~= Seq::<Seq<u8>>::empty());
        assert(v =~= Seq::<Seq<u8>>::empty());
    } else {
        lemma_drop_empty_push(v.drop_first(), e);
        assert(pushed.drop_first() =~= v.drop_first().push(e));
        assert(pushed[0] == v[0]);
        assert(drop_empty(pushed) =~= drop_empty(v) + (if e.len() == 0 { seq![] } else { seq![e] }));
    }
}

/// Quoting one more octet.
pub proof fn lemma_quote_octets_push(v: Seq<u8>, c: u8)
    ensures
        quote_octets(v.push(c)) == quote_octets(v) + (if c == 0x22 || c == 0x5C { seq![0x5Cu8, c] } else { seq![c] }),
    decreases v.len()
{
    let pushed = v.push(c);
    if v.len() == 0 {
        assert(pushed =~= seq![c]);
        assert(pushed.drop_first() =~= Seq::<u8>::empty());
        assert(v =~= Seq::<u8>::empty());
    } else {
        lemma_quote_octets_push(v.drop_first(), c);
        assert(pushed.drop_first() =~= v.drop_first().push(c));
        assert(pushed[0] == v[0]);
        assert(quote_octets(pushed) =~= quote_octets(v) + (if c == 0x22 || c == 0x5C { seq![0x5Cu8, c] } else { seq![c] }));
    }
}

/// `all_tokens` says every member is a token.
pub proof fn lemma_all_tokens_index(v: Seq<Seq<u8>>)
    ensures
        all_tokens(v) <==> (forall|i: int| 0 <= i < v.len() ==> is_token(#[trigger] v[i])),
    decreases v.len()
{
    if v.len() > 0 {
        lemma_all_tokens_index(v.drop_first());
        if all_tokens(v) {
            assert forall|i: int| 0 <= i < v.len() implies is_token(#[trigger] v[i]) by {
                if i > 0 {
                    assert(v.drop_first()[i - 1] == v[i]);
                }
            }
        }
        if forall|i: int| 0 <= i < v.len() ==> is_token(#[trigger] v[i]) {
            assert forall|j: int| 0 <= j < v.drop_first().len() implies is_token(#[trigger] v.drop_first()[j]) by {
                assert(v.drop_first()[j] == v[j + 1]);
            }
        }
    }
}

/// `all_equal` says every member is `e`.
pub proof fn lemma_all_equal_index(v: Seq<Seq<u8>>, e: Seq<u8>)
    ensures
        all_equal(v, e) <==> (forall|i: int| 0 <= i < v.len() ==> (#[trigger] v[i]) == e),
    decreases v.len()
{
    if v.len() > 0 {
        lemma_all_equal_index(v.drop_first(), e);
        if all_equal(v, e) {
            assert forall|i: int| 0 <= i < v.len() implies (#[trigger] v[i]) == e by {
                if i > 0 {
                    assert(v.drop_first()[i - 1] == v[i]);
                }
            }
        }
        if forall|i: int| 0 <= i < v.len() ==> (#[trigger] v[i]) == e {
            assert forall|j: int| 0 <= j < v.drop_first().len() implies (#[trigger] v.drop_first()[j]) == e by {
                assert(v.drop_first()[j] == v[j + 1]);
            }
        }
    }
}

/// Reading one more transfer coding.
pub proof fn lemma_codings_push(elements: Seq<Seq<u8>>, e: Seq<u8>)
    ensures
        parse_transfer_codings(elements.push(e)) == match (parse_transfer_codings(elements), parse_transfer_coding(e)) {
            (Some(a), Some(c)) => Some(a.push(c)),
            _ => None,
        },
    decreases elements.len()
{
    let pushed = elements.push(e);
    if elements.len() == 0 {
        assert(pushed =~= seq![e]);
        assert(pushed.drop_first() =~= Seq::<Seq<u8>>::empty());
        assert(elements =~= Seq::<Seq<u8>>::empty());
        if parse_transfer_coding(e) is Some {
            assert(seq![parse_transfer_coding(e)->Some_0] + Seq::<TransferCoding>::empty() =~= seq![parse_transfer_coding(e)->Some_0]);
        }
    } else {
        lemma_codings_push(elements.drop_first(), e);
        assert(pushed.drop_first() =~= elements.drop_first().push(e));
        assert(pushed[0] == elements[0]);
        if let (Some(first), Some(a), Some(c)) = (
            parse_transfer_coding(elements[0]),
            parse_transfer_codings(elements.drop_first()),
            parse_transfer_coding(e),
        ) {
            assert(seq![first] + a.push(c) =~= (seq![first] + a).push(c));
        }
    }
}

/// Reading one more digit.
pub proof fn lemma_decimal_value_push(s: Seq<u8>, c: u8)
    ensures
        decimal_value(s.push(c)) == decimal_value(s) * 10 + ((c - 0x30) as nat),
{
    assert(s.push(c).drop_last() =~= s);
    assert(s.push(c).last() == c);
}

/// A string is all in the class exactly when its run is all of it.
pub proof fn lemma_all_in_run_len(s: Seq<u8>, class: Class)
    ensures
        all_in(s, class) <==> run_len(class, s) == s.len(),
    decreases s.len()
{
    if s.len() > 0 && in_class(class, s[0]) {
        lemma_all_in_run_len(s.drop_first(), class);
    }
}

} // verus!
