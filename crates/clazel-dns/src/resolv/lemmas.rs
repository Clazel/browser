//! Facts the executable resolv.conf parser needs about the spec
//! ([`super::spec`]).

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// A prefix of a string of digits is a string of digits.
pub proof fn lemma_all_digits_prefix(s: Seq<u8>, k: int)
    requires
        all_digits(s),
        0 <= k <= s.len(),
    ensures
        all_digits(s.subrange(0, k)),
    decreases s.len() - k,
{
    if k < s.len() {
        assert(s.drop_last().subrange(0, k) =~= s.subrange(0, k));
        lemma_all_digits_prefix(s.drop_last(), k);
    } else {
        assert(s.subrange(0, k) =~= s);
    }
}

/// 65536 to the power `n`: the number of values `n` pieces of 16 bits can
/// hold.
pub open spec fn pow65536(n: nat) -> nat
    decreases n,
{
    if n == 0 {
        1
    } else {
        65536 * pow65536((n - 1) as nat)
    }
}

/// Pieces below 65536 spell a number below 65536^n.
pub proof fn lemma_pieces_value_bound(p: Seq<nat>)
    requires
        forall|i: int| 0 <= i < p.len() ==> #[trigger] p[i] < 65536,
    ensures
        pieces_value(p) < pow65536(p.len()),
    decreases p.len(),
{
    if p.len() > 0 {
        let d = p.drop_last();
        assert forall|i: int| 0 <= i < d.len() implies #[trigger] d[i] < 65536 by {
            assert(d[i] == p[i]);
        }
        lemma_pieces_value_bound(d);
        assert(p.last() == p[p.len() - 1]);
        assert(pow65536(p.len()) == 65536 * pow65536((p.len() - 1) as nat));
    }
}

/// Eight pieces hold exactly the values of a `u128`.
pub proof fn lemma_pow65536_8()
    ensures
        pow65536(8) == 0x1_0000_0000_0000_0000_0000_0000_0000_0000,
{
    assert(pow65536(8) == 0x1_0000_0000_0000_0000_0000_0000_0000_0000) by (compute_only);
}

/// Up to eight pieces of 16 bits fit in a `u128`.
pub proof fn lemma_pow65536_up_to_8(n: nat)
    requires
        n <= 8,
    ensures
        pow65536(n) <= 0x1_0000_0000_0000_0000_0000_0000_0000_0000,
    decreases 8 - n,
{
    if n < 8 {
        lemma_pow65536_up_to_8(n + 1);
        assert(pow65536(n + 1) == 65536 * pow65536(n));
        assert(pow65536(n) >= 1) by {
            lemma_pow65536_positive(n);
        }
    } else {
        lemma_pow65536_8();
    }
}

/// 65536^n is at least 1.
pub proof fn lemma_pow65536_positive(n: nat)
    ensures
        pow65536(n) >= 1,
    decreases n,
{
    if n > 0 {
        lemma_pow65536_positive((n - 1) as nat);
    }
}

} // verus!
