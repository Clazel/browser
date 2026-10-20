//! Facts proven about the UTS #46 spec: tools for the proofs of the
//! executable code, and (below) evidence that the transcription is right.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// A code point above U+007F at `i` makes [`contains_non_ascii`] true.
pub proof fn lemma_contains_non_ascii(s: Seq<u32>, i: int)
    requires
        0 <= i < s.len(),
        s[i] > 0x7F,
    ensures
        contains_non_ascii(s),
    decreases s.len()
{
    if i < s.len() - 1 {
        assert(s.drop_last()[i] == s[i]);
        lemma_contains_non_ascii(s.drop_last(), i);
    }
}

/// An R, AL or AN code point at `i` makes the label an RTL label.
pub proof fn lemma_is_rtl_label(s: Seq<u32>, i: int)
    requires
        0 <= i < s.len(),
        is_r_al_an(s[i]),
    ensures
        is_rtl_label(s),
    decreases s.len()
{
    if i < s.len() - 1 {
        assert(s.drop_last()[i] == s[i]);
        lemma_is_rtl_label(s.drop_last(), i);
    }
}

/// A code point at `i` whose class is not allowed makes [`all_allowed`]
/// false.
pub proof fn lemma_all_allowed(s: Seq<u32>, i: int, rtl: bool)
    requires
        0 <= i < s.len(),
        !(if rtl {
            rtl_allowed(bidi_class(s[i]))
        } else {
            ltr_allowed(bidi_class(s[i]))
        }),
    ensures
        !all_allowed(s, rtl),
    decreases s.len()
{
    if i < s.len() - 1 {
        assert(s.drop_last()[i] == s[i]);
        lemma_all_allowed(s.drop_last(), i, rtl);
    }
}

/// A code point of class `class` at `i` makes [`contains_class`] true.
pub proof fn lemma_contains_class(s: Seq<u32>, i: int, class: super::tables::BidiClass)
    requires
        0 <= i < s.len(),
        bidi_class(s[i]) == Some(class),
    ensures
        contains_class(s, class),
    decreases s.len()
{
    if i < s.len() - 1 {
        assert(s.drop_last()[i] == s[i]);
        lemma_contains_class(s.drop_last(), i, class);
    }
}

/// A full stop or a code point with a disallowed Status at `i` makes
/// [`code_points_allowed`] false.
pub proof fn lemma_code_points_allowed(s: Seq<u32>, i: int, flags: Flags)
    requires
        0 <= i < s.len(),
        s[i] == full_stop() || !status_allowed(s[i], flags),
    ensures
        !code_points_allowed(s, flags),
    decreases s.len()
{
    if i < s.len() - 1 {
        assert(s.drop_last()[i] == s[i]);
        lemma_code_points_allowed(s.drop_last(), i, flags);
    }
}

/// A label at `k` whose length is not 1 to 63 makes
/// [`label_lengths_ok`] false.
pub proof fn lemma_label_lengths_ok(labels: Seq<Seq<u32>>, k: int)
    requires
        0 <= k < labels.len(),
        !(1 <= labels[k].len() <= 63),
    ensures
        !label_lengths_ok(labels),
    decreases labels.len()
{
    if k < labels.len() - 1 {
        assert(labels.drop_last()[k] == labels[k]);
        lemma_label_lengths_ok(labels.drop_last(), k);
    }
}

/// A forbidden domain code point at `i` makes
/// [`contains_forbidden_domain_code_point`] true.
pub proof fn lemma_contains_forbidden(s: Seq<u32>, i: int)
    requires
        0 <= i < s.len(),
        is_forbidden_domain_code_point(s[i]),
    ensures
        contains_forbidden_domain_code_point(s),
    decreases s.len()
{
    if i < s.len() - 1 {
        assert(s.drop_last()[i] == s[i]);
        lemma_contains_forbidden(s.drop_last(), i);
    }
}

/// If ToASCII step 3 fails on a prefix of the labels, it fails on all of
/// them.
pub proof fn lemma_to_ascii_labels_prefix(labels: Seq<Seq<u32>>, j: int)
    requires
        0 <= j <= labels.len(),
        to_ascii_labels(labels.subrange(0, j)) is None,
    ensures
        to_ascii_labels(labels) is None,
    decreases labels.len() - j
{
    if j < labels.len() {
        let next = labels.subrange(0, j + 1);
        assert(next.drop_last() =~= labels.subrange(0, j));
        lemma_to_ascii_labels_prefix(labels, j + 1);
    } else {
        assert(labels.subrange(0, j) =~= labels);
    }
}

/// If ToASCII step 3 fails on label `k`, it fails.
pub proof fn lemma_to_ascii_labels_none(labels: Seq<Seq<u32>>, k: int)
    requires
        0 <= k < labels.len(),
    ensures
        to_ascii_label(labels[k]) is None ==> to_ascii_labels(labels) is None,
{
    if to_ascii_label(labels[k]) is None {
        let next = labels.subrange(0, k + 1);
        assert(next.drop_last() =~= labels.subrange(0, k));
        assert(next.last() == labels[k]);
        lemma_to_ascii_labels_prefix(labels, k + 1);
    }
}

// ---------------------------------------------------------------------------
// Evidence: facts the standards state or imply.
// ---------------------------------------------------------------------------

/// Breaking a string at U+002E and joining the labels with U+002E gives
/// the string back (§4 step 3 and §4.2 step 6 are inverse).
pub proof fn lemma_join_break(s: Seq<u32>)
    ensures
        break_labels(s).len() >= 1,
        join_labels(break_labels(s)) == s,
    decreases s.len()
{
    if s.len() == 0 {
        assert(join_labels(seq![seq![]]) =~= Seq::<u32>::empty());
    } else {
        let d = s.drop_last();
        lemma_join_break(d);
        let labels = break_labels(d);
        let n = labels.len();
        if s.last() == full_stop() {
            let next = labels.push(seq![]);
            assert(next.drop_last() =~= labels);
            assert(join_labels(next) =~= d.push(full_stop()));
            assert(d.push(full_stop()) =~= s);
        } else {
            let next = labels.update(n - 1, labels.last().push(s.last()));
            if n == 1 {
                assert(join_labels(next) == next[0]);
                assert(next[0] =~= labels[0].push(s.last()));
                assert(join_labels(labels) == labels[0]);
            } else {
                assert(next.drop_last() =~= labels.drop_last());
                assert(join_labels(next) =~= join_labels(labels.drop_last()).push(full_stop()) + labels.last().push(
                    s.last(),
                ));
                assert(join_labels(labels) == join_labels(labels.drop_last()).push(full_stop()) + labels.last());
            }
            assert(join_labels(next) =~= d.push(s.last()));
            assert(d.push(s.last()) =~= s);
        }
    }
}

/// D108: positions `i` and `i + 1` of `s` hold a Reorderable Pair.
pub open spec fn reorderable_at(s: Seq<u32>, i: int) -> bool {
    ccc(s[i]) > ccc(s[i + 1]) && ccc(s[i + 1]) > 0
}

/// D109's result: "the sequence contains no more Reorderable Pairs".
pub open spec fn no_reorderable_pair(s: Seq<u32>) -> bool {
    forall|i: int| 0 <= i < s.len() - 1 ==> !#[trigger] reorderable_at(s, i)
}

proof fn lemma_insert_ordered_last(done: Seq<u32>, c: u32)
    ensures
        insert_ordered(done, c).len() == done.len() + 1,
        insert_ordered(done, c).last() == c || (done.len() > 0 && insert_ordered(done, c).last() == done.last()),
    decreases done.len()
{
    if !(ccc(c) == 0 || done.len() == 0 || ccc(done.last()) <= ccc(c)) {
        lemma_insert_ordered_last(done.drop_last(), c);
    }
}

proof fn lemma_insert_ordered_keeps(done: Seq<u32>, c: u32)
    requires
        no_reorderable_pair(done),
    ensures
        no_reorderable_pair(insert_ordered(done, c)),
    decreases done.len()
{
    let r = insert_ordered(done, c);
    lemma_insert_ordered_last(done, c);
    if ccc(c) == 0 || done.len() == 0 || ccc(done.last()) <= ccc(c) {
        assert forall|i: int| 0 <= i < r.len() - 1 implies !#[trigger] reorderable_at(r, i) by {
            if i < done.len() - 1 {
                assert(reorderable_at(done, i) == reorderable_at(r, i));
            }
        }
    } else {
        let d = done.drop_last();
        assert forall|i: int| 0 <= i < d.len() - 1 implies !#[trigger] reorderable_at(d, i) by {
            assert(reorderable_at(done, i) == reorderable_at(d, i));
        }
        lemma_insert_ordered_keeps(d, c);
        lemma_insert_ordered_last(d, c);
        let inner = insert_ordered(d, c);
        assert forall|i: int| 0 <= i < r.len() - 1 implies !#[trigger] reorderable_at(r, i) by {
            if i < inner.len() - 1 {
                assert(reorderable_at(inner, i) == reorderable_at(r, i));
            } else {
                // The new pair: (inner's last, done's last).
                if inner.last() != c {
                    assert(reorderable_at(done, done.len() - 2) == reorderable_at(r, i));
                }
            }
        }
    }
}

/// D109: the Canonical Ordering Algorithm leaves no Reorderable Pair.
pub proof fn lemma_canonical_order_no_reorderable_pair(s: Seq<u32>)
    ensures
        no_reorderable_pair(canonical_order(s)),
        canonical_order(s).len() == s.len(),
    decreases s.len()
{
    if s.len() > 0 {
        lemma_canonical_order_no_reorderable_pair(s.drop_last());
        lemma_insert_ordered_keeps(canonical_order(s.drop_last()), s.last());
        lemma_insert_ordered_last(canonical_order(s.drop_last()), s.last());
    }
}

} // verus!
