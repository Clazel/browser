//! Facts proven about the Punycode spec. They are evidence that the
//! transcription is right, and tools for the proofs of the executable code;
//! they are not part of what the implementation must meet.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// [`contains_non_basic`] is "some code point of `s` is not basic".
pub proof fn lemma_contains_non_basic(s: Seq<u32>)
    ensures
        contains_non_basic(s) <==> exists|x: int| 0 <= x < s.len() && !is_basic(#[trigger] s[x]),
    decreases s.len()
{
    if s.len() > 0 {
        lemma_contains_non_basic(s.drop_last());
        if contains_non_basic(s.drop_last()) {
            let x = choose|x: int| 0 <= x < s.drop_last().len() && !is_basic(#[trigger] s.drop_last()[x]);
            assert(s[x] == s.drop_last()[x]);
        }
        if exists|x: int| 0 <= x < s.len() && !is_basic(#[trigger] s[x]) {
            let x = choose|x: int| 0 <= x < s.len() && !is_basic(#[trigger] s[x]);
            if x < s.len() - 1 {
                assert(s.drop_last()[x] == s[x]);
            }
        }
    }
}

/// The number of code points in `s` less than `n`.
pub open spec fn count_less(s: Seq<u32>, n: nat) -> nat
    decreases s.len()
{
    if s.len() == 0 {
        0
    } else {
        count_less(s.drop_last(), n) + if (s.last() as nat) < n {
            1nat
        } else {
            0nat
        }
    }
}

/// The number of code points in `s` equal to `n`.
pub open spec fn count_equal(s: Seq<u32>, n: nat) -> nat
    decreases s.len()
{
    if s.len() == 0 {
        0
    } else {
        count_equal(s.drop_last(), n) + if s.last() as nat == n {
            1nat
        } else {
            0nat
        }
    }
}

/// The code points less than `initial_n` are the basic ones.
pub proof fn lemma_count_basic(s: Seq<u32>)
    ensures
        count_less(s, initial_n()) == basic_code_points(s).len(),
    decreases s.len()
{
    if s.len() > 0 {
        lemma_count_basic(s.drop_last());
    }
}

/// Counting below `n + 1` is counting below `n` and at `n`; neither
/// exceeds the length.
pub proof fn lemma_count_step(s: Seq<u32>, n: nat)
    ensures
        count_less(s, n) + count_equal(s, n) == count_less(s, n + 1),
        count_less(s, n + 1) <= s.len(),
        count_less(s, n) <= s.len(),
    decreases s.len()
{
    if s.len() > 0 {
        lemma_count_step(s.drop_last(), n);
    }
}

/// No code point lies between `n` and the minimum code point `>= n`; if
/// there is none, every code point is below `n`.
pub proof fn lemma_count_min(s: Seq<u32>, n: nat)
    ensures
        min_at_least(s, n) matches Some(m) ==> count_less(s, m as nat) == count_less(s, n) && m >= n,
        min_at_least(s, n) is None ==> count_less(s, n) == s.len(),
    decreases s.len()
{
    if s.len() > 0 {
        lemma_count_min(s.drop_last(), n);
        super::termination::lemma_min_at_least(s.drop_last(), n);
        if let Some(m) = min_at_least(s, n) {
            if let Some(r) = min_at_least(s.drop_last(), n) {
                if (s.last() as nat) >= n && r >= s.last() {
                    lemma_count_below_min(s.drop_last(), n, s.last() as nat);
                }
            } else {
                lemma_count_below_min(s.drop_last(), n, m as nat);
            }
        }
    }
}

/// If no code point of `s` is in `[n, m)`, counting below `m` is counting
/// below `n`. Stated through [`min_at_least`]: its result, if any, is at
/// least `m`.
proof fn lemma_count_below_min(s: Seq<u32>, n: nat, m: nat)
    requires
        n <= m,
        min_at_least(s, n) matches Some(r) ==> r >= m,
    ensures
        count_less(s, m) == count_less(s, n),
    decreases s.len()
{
    if s.len() > 0 {
        let rest = min_at_least(s.drop_last(), n);
        if let Some(r) = rest {
            if (s.last() as nat) >= n {
                assert(r >= m);
            }
        }
        lemma_count_below_min(s.drop_last(), n, m);
    }
}

/// Extending a prefix by one code point.
pub proof fn lemma_count_equal_prefix(s: Seq<u32>, j: int, m: nat)
    requires
        0 <= j < s.len(),
    ensures
        count_equal(s.subrange(0, j + 1), m) == count_equal(s.subrange(0, j), m) + if s[j] as nat == m {
            1nat
        } else {
            0nat
        },
{
    assert(s.subrange(0, j + 1).drop_last() =~= s.subrange(0, j));
}

/// A prefix has no more code points equal to `m` than the whole.
pub proof fn lemma_count_equal_prefix_le(s: Seq<u32>, j: int, m: nat)
    requires
        0 <= j <= s.len(),
    ensures
        count_equal(s.subrange(0, j), m) <= count_equal(s, m),
    decreases s.len() - j
{
    if j < s.len() {
        lemma_count_equal_prefix(s, j, m);
        lemma_count_equal_prefix_le(s, j + 1, m);
    } else {
        assert(s.subrange(0, j) =~= s);
    }
}

} // verus!
