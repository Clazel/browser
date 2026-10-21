//! Facts about splitting a domain into labels and joining them back, which
//! the executable functions need to know that a suffix of a domain, built
//! by joining its last labels, is the string the spec says it is.
//!
//! `clazel-url`'s `lemma_strictly_split_join` says splitting a joined list
//! of dot-free labels gives the list back. This adds the converse (joining
//! what `strictly_split` returns gives the string back, and its labels are
//! dot-free), by a second definition of splitting, [`split_naive`], that
//! recurses on the first code point.

#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Splitting at "." by recursion on the first code point: the labels of
/// `s`.
pub open spec fn split_naive(s: Seq<u32>) -> Seq<Seq<u32>>
    decreases s.len(),
{
    if s.len() == 0 {
        seq![seq![]]
    } else if s[0] == 0x2Eu32 {
        seq![seq![]] + split_naive(s.drop_first())
    } else {
        let r = split_naive(s.drop_first());
        seq![seq![s[0]] + r[0]] + r.drop_first()
    }
}

/// [`split_naive`] gives a non-empty list of dot-free labels that joins
/// back to `s`.
pub proof fn lemma_split_naive(s: Seq<u32>)
    ensures
        split_naive(s).len() >= 1,
        forall|k: int| 0 <= k < split_naive(s).len() ==> clazel_url::host::lemmas::free_of(#[trigger] split_naive(s)[k], 0x2E),
        clazel_url::host::lemmas::split_join(split_naive(s), 0x2E) == s,
    decreases s.len(),
{
    if s.len() == 0 {
        assert(split_naive(s) =~= seq![seq![]]);
        assert(split_naive(s).drop_first() =~= Seq::<Seq<u32>>::empty());
        assert(clazel_url::host::lemmas::split_join(split_naive(s), 0x2E) =~= s);
    } else if s[0] == 0x2Eu32 {
        let rest = s.drop_first();
        lemma_split_naive(rest);
        let r = split_naive(rest);
        let result = split_naive(s);
        assert(result =~= seq![seq![]] + r);
        assert(result.drop_first() =~= r);
        assert(clazel_url::host::lemmas::split_tail(r, 0x2E) =~= seq![0x2Eu32] + clazel_url::host::lemmas::split_join(r, 0x2E)) by {
            assert(r.drop_first() =~= r.drop_first());
        }
        assert(clazel_url::host::lemmas::split_join(result, 0x2E) =~= s) by {
            assert(s =~= seq![0x2Eu32] + rest);
        }
        assert forall|k: int| 0 <= k < result.len() implies clazel_url::host::lemmas::free_of(#[trigger] result[k], 0x2E) by {
            if k >= 1 {
                assert(result[k] == r[k - 1]);
            } else {
                assert(result[0] =~= Seq::<u32>::empty());
            }
        }
    } else {
        let rest = s.drop_first();
        lemma_split_naive(rest);
        let r = split_naive(rest);
        let result = split_naive(s);
        assert(result =~= seq![seq![s[0]] + r[0]] + r.drop_first());
        assert(result.drop_first() =~= r.drop_first());
        assert(result[0] == seq![s[0]] + r[0]);
        assert(clazel_url::host::lemmas::split_join(result, 0x2E) =~= s) by {
            assert(clazel_url::host::lemmas::split_join(r, 0x2E) == r[0] + clazel_url::host::lemmas::split_tail(r.drop_first(), 0x2E));
            assert(s =~= seq![s[0]] + rest);
        }
        assert forall|k: int| 0 <= k < result.len() implies clazel_url::host::lemmas::free_of(#[trigger] result[k], 0x2E) by {
            if k >= 1 {
                assert(result[k] == r[k]);
            } else {
                assert(clazel_url::host::lemmas::free_of(r[0], 0x2E));
                assert forall|j: int| 0 <= j < result[0].len() implies result[0][j] != 0x2Eu32 by {
                    if j >= 1 {
                        assert(result[0][j] == r[0][j - 1]);
                    }
                }
            }
        }
    }
}

/// Splitting a string and joining the labels gives the string back, and
/// the labels have no ".", and there is at least one.
pub proof fn lemma_split_join_round_trip(s: Seq<u32>)
    ensures
        clazel_url::host::spec::strictly_split(s, 0x2E).len() >= 1,
        forall|k: int| 0 <= k < clazel_url::host::spec::strictly_split(s, 0x2E).len() ==> clazel_url::host::lemmas::free_of(#[trigger] clazel_url::host::spec::strictly_split(s, 0x2E)[k], 0x2E),
        clazel_url::host::lemmas::split_join(clazel_url::host::spec::strictly_split(s, 0x2E), 0x2E) == s,
{
    lemma_split_naive(s);
    clazel_url::host::lemmas::lemma_strictly_split_join(split_naive(s), 0x2E);
    assert(clazel_url::host::spec::strictly_split(s, 0x2E) == split_naive(s));
}

/// Joining is injective on non-empty lists of dot-free labels.
pub proof fn lemma_join_injective(a: Seq<Seq<u32>>, b: Seq<Seq<u32>>)
    requires
        a.len() >= 1,
        b.len() >= 1,
        forall|k: int| 0 <= k < a.len() ==> clazel_url::host::lemmas::free_of(#[trigger] a[k], 0x2E),
        forall|k: int| 0 <= k < b.len() ==> clazel_url::host::lemmas::free_of(#[trigger] b[k], 0x2E),
        clazel_url::host::lemmas::split_join(a, 0x2E) == clazel_url::host::lemmas::split_join(b, 0x2E),
    ensures
        a == b,
{
    clazel_url::host::lemmas::lemma_strictly_split_join(a, 0x2E);
    clazel_url::host::lemmas::lemma_strictly_split_join(b, 0x2E);
}

/// Appending a label to a list extends its tail.
pub proof fn lemma_split_tail_push(rest: Seq<Seq<u32>>, x: Seq<u32>)
    ensures
        clazel_url::host::lemmas::split_tail(rest.push(x), 0x2E) == clazel_url::host::lemmas::split_tail(rest, 0x2E) + seq![0x2Eu32] + x,
    decreases rest.len(),
{
    if rest.len() == 0 {
        let pushed = rest.push(x);
        assert(pushed.len() == 1);
        assert(pushed[0] == x);
        assert(pushed.drop_first() =~= Seq::<Seq<u32>>::empty());
        assert(clazel_url::host::lemmas::split_tail(pushed.drop_first(), 0x2E) == Seq::<u32>::empty());
        assert(clazel_url::host::lemmas::split_tail(pushed, 0x2E) =~= seq![0x2Eu32] + x);
        assert(clazel_url::host::lemmas::split_tail(rest, 0x2E) == Seq::<u32>::empty());
    } else {
        let tail = rest.drop_first();
        lemma_split_tail_push(tail, x);
        assert(rest.push(x).drop_first() =~= tail.push(x));
        assert(clazel_url::host::lemmas::split_tail(rest.push(x), 0x2E) =~= seq![0x2Eu32] + rest[0] + clazel_url::host::lemmas::split_tail(tail.push(x), 0x2E));
        assert(clazel_url::host::lemmas::split_tail(rest, 0x2E) =~= seq![0x2Eu32] + rest[0] + clazel_url::host::lemmas::split_tail(tail, 0x2E));
    }
}

/// Joining a list with one more label appended.
pub proof fn lemma_split_join_push(a: Seq<Seq<u32>>, x: Seq<u32>)
    requires
        a.len() >= 1,
    ensures
        clazel_url::host::lemmas::split_join(a.push(x), 0x2E) == clazel_url::host::lemmas::split_join(a, 0x2E) + seq![0x2Eu32] + x,
{
    lemma_split_tail_push(a.drop_first(), x);
    assert(a.push(x).drop_first() =~= a.drop_first().push(x));
    assert(a.push(x)[0] == a[0]);
}

} // verus!
