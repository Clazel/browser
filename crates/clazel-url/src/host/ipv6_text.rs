//! Facts about the IPv6 parser and serializer on text made of pieces:
//! what the parser's loops do on "h16:h16:...", what text the serializer
//! writes, and what the compress swaps (parser step 7) do. They prove the
//! round trip in [`super::lemmas`], and the agreement with RFC 3986 in
//! [`super::independent`].

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------
// Text built from pieces.
// ---------------------------------------------------------------------

/// Each piece in shortest lowercase hex, followed by ":".
pub open spec fn hex_text_colons(ps: Seq<nat>) -> Seq<u32>
    decreases ps.len()
{
    if ps.len() == 0 {
        seq![]
    } else {
        shortest_lowercase_hex(ps[0]) + seq![0x3Au32] + hex_text_colons(ps.drop_first())
    }
}

/// The pieces in shortest lowercase hex, separated by ":".
pub open spec fn hex_text(ps: Seq<nat>) -> Seq<u32>
    decreases ps.len()
{
    if ps.len() == 0 {
        seq![]
    } else if ps.len() == 1 {
        shortest_lowercase_hex(ps[0])
    } else {
        shortest_lowercase_hex(ps[0]) + seq![0x3Au32] + hex_text(ps.drop_first())
    }
}

/// `addr` with `ps` written from index `i` on.
pub open spec fn write(addr: Seq<nat>, i: int, ps: Seq<nat>) -> Seq<nat>
    decreases ps.len()
{
    if ps.len() == 0 {
        addr
    } else {
        write(addr.update(i, ps[0]), i + 1, ps.drop_first())
    }
}

/// Every piece is below 2^16.
pub open spec fn all_pieces(ps: Seq<nat>) -> bool {
    forall|k: int| 0 <= k < ps.len() ==> #[trigger] ps[k] < 0x1_0000
}

/// The number of consecutive zero pieces of `a` from index `i`.
pub open spec fn zero_run_len(a: Seq<nat>, i: int) -> nat
    decreases a.len() - i
{
    if 0 <= i < a.len() && a[i] == 0 {
        1 + zero_run_len(a, i + 1)
    } else {
        0
    }
}

/// The digits of `t` are ASCII hex digits.
pub open spec fn all_hex(t: Seq<u32>) -> bool {
    forall|k: int| 0 <= k < t.len() ==> is_ascii_hex_digit(#[trigger] t[k])
}

// ---------------------------------------------------------------------
// Hex digits.
// ---------------------------------------------------------------------

/// The shortest lowercase hex form of a 16-bit number: one to four ASCII
/// hex digits, with that value.
pub proof fn lemma_shortest_hex(n: nat)
    requires
        n < 0x1_0000,
    ensures
        1 <= shortest_lowercase_hex(n).len() <= 4,
        n < 16 ==> shortest_lowercase_hex(n).len() == 1,
        n < 256 ==> shortest_lowercase_hex(n).len() <= 2,
        n < 0x1000 ==> shortest_lowercase_hex(n).len() <= 3,
        all_hex(shortest_lowercase_hex(n)),
        radix_value(shortest_lowercase_hex(n), 16) == n,
    decreases n
{
    let t = shortest_lowercase_hex(n);
    assert(hex_digit_value(lowercase_hex_digit(n % 16)) == n % 16);
    if n < 16 {
        assert(t.drop_last() =~= Seq::<u32>::empty());
        assert(radix_value(t, 16) == radix_value(t.drop_last(), 16) * 16 + hex_digit_value(t.last()));
    } else {
        lemma_shortest_hex(n / 16);
        let u = shortest_lowercase_hex(n / 16);
        assert(t.drop_last() =~= u);
        assert(t.last() == lowercase_hex_digit(n % 16));
        assert(n == (n / 16) * 16 + n % 16);
        assert(radix_value(t, 16) == radix_value(u, 16) * 16 + hex_digit_value(t.last()));
        assert forall|k: int| 0 <= k < t.len() implies is_ascii_hex_digit(#[trigger] t[k]) by {
            if k < u.len() {
                assert(t[k] == u[k]);
            }
        }
    }
}

/// Reading a hex digit string `t` at `start` (IPv6 parser step 6.4) gives
/// its value and length, when what follows it is not a hex digit.
pub proof fn lemma_hex_digits_read(input: Seq<u32>, start: int, t: Seq<u32>, k: nat)
    requires
        0 <= start,
        start + t.len() <= input.len(),
        input.subrange(start, start + t.len()) == t,
        1 <= t.len() <= 4,
        all_hex(t),
        start + t.len() == input.len() || !is_ascii_hex_digit(input[start + t.len()]),
        k <= t.len(),
    ensures
        ipv6_hex_digits(input, start, radix_value(t.subrange(0, k as int), 16), k) == (radix_value(t, 16), t.len()),
    decreases t.len() - k
{
    if k < t.len() {
        assert(input[start + k] == t[k as int]);
        assert(t.subrange(0, k + 1int).drop_last() =~= t.subrange(0, k as int));
        lemma_hex_digits_read(input, start, t, k + 1);
    } else {
        assert(t.subrange(0, k as int) =~= t);
    }
}

// ---------------------------------------------------------------------
// The IPv6 parser's main loop on pieces.
// ---------------------------------------------------------------------

/// The text at `p`: `input[p..p + t.len()]` is `t`.
pub open spec fn text_at(input: Seq<u32>, p: int, t: Seq<u32>) -> bool {
    0 <= p && p + t.len() <= input.len() && input.subrange(p, p + t.len()) == t
}

/// The main loop reads one piece followed by ":" and more text.
pub proof fn lemma_main_loop_piece_colon(input: Seq<u32>, address: Seq<nat>, pi: int, compress: Option<int>, p: int, n: nat)
    requires
        n < 0x1_0000,
        text_at(input, p, shortest_lowercase_hex(n) + seq![0x3Au32]),
        p + shortest_lowercase_hex(n).len() + 1 < input.len(),
        0 <= pi < 8,
    ensures
        ipv6_main_loop(input, address, pi, compress, p) == ipv6_main_loop(
            input,
            address.update(pi, n),
            pi + 1,
            compress,
            p + shortest_lowercase_hex(n).len() + 1,
        ),
{
    let t = shortest_lowercase_hex(n);
    lemma_shortest_hex(n);
    let tc = t + seq![0x3Au32];
    assert(input[p] == tc[0]);
    assert(input.subrange(p, p + t.len()) =~= t) by {
        assert forall|k: int| 0 <= k < t.len() implies input.subrange(p, p + t.len())[k] == t[k] by {
            assert(input[p + k] == tc[k]);
        }
    }
    assert(input[p + t.len()] == tc[t.len() as int]);
    lemma_hex_digits_read(input, p, t, 0);
    assert(t.subrange(0, 0) =~= Seq::<u32>::empty());
}

/// The main loop reads one final piece, up to the end.
pub proof fn lemma_main_loop_piece_end(input: Seq<u32>, address: Seq<nat>, pi: int, compress: Option<int>, p: int, n: nat)
    requires
        n < 0x1_0000,
        text_at(input, p, shortest_lowercase_hex(n)),
        p + shortest_lowercase_hex(n).len() == input.len(),
        0 <= pi < 8,
    ensures
        ipv6_main_loop(input, address, pi, compress, p) == Some((address.update(pi, n), pi + 1, compress)),
{
    let t = shortest_lowercase_hex(n);
    lemma_shortest_hex(n);
    assert(input[p] == t[0]);
    lemma_hex_digits_read(input, p, t, 0);
    assert(t.subrange(0, 0) =~= Seq::<u32>::empty());
}

/// The main loop reads pieces each followed by ":", then more text.
pub proof fn lemma_main_loop_colons(input: Seq<u32>, address: Seq<nat>, pi: int, compress: Option<int>, p: int, ps: Seq<nat>)
    requires
        all_pieces(ps),
        text_at(input, p, hex_text_colons(ps)),
        p + hex_text_colons(ps).len() < input.len(),
        0 <= pi,
        pi + ps.len() <= 8,
    ensures
        ipv6_main_loop(input, address, pi, compress, p) == ipv6_main_loop(
            input,
            write(address, pi, ps),
            pi + ps.len(),
            compress,
            p + hex_text_colons(ps).len(),
        ),
    decreases ps.len()
{
    if ps.len() > 0 {
        let t = shortest_lowercase_hex(ps[0]);
        let rest = ps.drop_first();
        let all = hex_text_colons(ps);
        assert(all =~= (t + seq![0x3Au32]) + hex_text_colons(rest));
        let head = t + seq![0x3Au32];
        assert(input.subrange(p, p + head.len()) =~= head) by {
            assert forall|k: int| 0 <= k < head.len() implies input.subrange(p, p + head.len())[k] == head[k] by {
                assert(input[p + k] == all[k]);
            }
        }
        lemma_main_loop_piece_colon(input, address, pi, compress, p, ps[0]);
        let q = p + head.len();
        assert(input.subrange(q, q + hex_text_colons(rest).len()) =~= hex_text_colons(rest)) by {
            assert forall|k: int| 0 <= k < hex_text_colons(rest).len() implies input.subrange(q, q + hex_text_colons(rest).len())[k]
                == hex_text_colons(rest)[k] by {
                assert(input[q + k] == all[head.len() + k]);
            }
        }
        assert(all_pieces(rest)) by {
            assert forall|k: int| 0 <= k < rest.len() implies #[trigger] rest[k] < 0x1_0000 by {
                assert(rest[k] == ps[k + 1]);
            }
        }
        lemma_main_loop_colons(input, address.update(pi, ps[0]), pi + 1, compress, q, rest);
    }
}

/// The main loop reads pieces separated by ":", up to the end.
pub proof fn lemma_main_loop_list(input: Seq<u32>, address: Seq<nat>, pi: int, compress: Option<int>, p: int, ps: Seq<nat>)
    requires
        ps.len() >= 1,
        all_pieces(ps),
        text_at(input, p, hex_text(ps)),
        p + hex_text(ps).len() == input.len(),
        0 <= pi,
        pi + ps.len() <= 8,
    ensures
        ipv6_main_loop(input, address, pi, compress, p) == Some((write(address, pi, ps), pi + ps.len(), compress)),
    decreases ps.len()
{
    let rest = ps.drop_first();
    if ps.len() == 1 {
        lemma_main_loop_piece_end(input, address, pi, compress, p, ps[0]);
        assert(write(address.update(pi, ps[0]), pi + 1, rest) == address.update(pi, ps[0]));
    } else {
        let t = shortest_lowercase_hex(ps[0]);
        let all = hex_text(ps);
        let head = t + seq![0x3Au32];
        assert(all =~= head + hex_text(rest));
        lemma_shortest_hex(ps[1]);
        assert(hex_text(rest).len() >= 1);
        assert(input.subrange(p, p + head.len()) =~= head) by {
            assert forall|k: int| 0 <= k < head.len() implies input.subrange(p, p + head.len())[k] == head[k] by {
                assert(input[p + k] == all[k]);
            }
        }
        lemma_main_loop_piece_colon(input, address, pi, compress, p, ps[0]);
        let q = p + head.len();
        assert(input.subrange(q, q + hex_text(rest).len()) =~= hex_text(rest)) by {
            assert forall|k: int| 0 <= k < hex_text(rest).len() implies input.subrange(q, q + hex_text(rest).len())[k]
                == hex_text(rest)[k] by {
                assert(input[q + k] == all[head.len() + k]);
            }
        }
        assert(all_pieces(rest)) by {
            assert forall|k: int| 0 <= k < rest.len() implies #[trigger] rest[k] < 0x1_0000 by {
                assert(rest[k] == ps[k + 1]);
            }
        }
        lemma_main_loop_list(input, address.update(pi, ps[0]), pi + 1, compress, q, rest);
    }
}

// ---------------------------------------------------------------------
// Writing pieces, and the compress swaps.
// ---------------------------------------------------------------------

/// What `write` does to each index.
pub proof fn lemma_write(addr: Seq<nat>, i: int, ps: Seq<nat>)
    requires
        0 <= i,
        i + ps.len() <= addr.len(),
    ensures
        write(addr, i, ps).len() == addr.len(),
        forall|k: int| 0 <= k < addr.len() ==> #[trigger] write(addr, i, ps)[k] == if i <= k < i + ps.len() {
            ps[k - i]
        } else {
            addr[k]
        },
    decreases ps.len()
{
    if ps.len() > 0 {
        let rest = ps.drop_first();
        lemma_write(addr.update(i, ps[0]), i + 1, rest);
        assert forall|k: int| 0 <= k < addr.len() implies #[trigger] write(addr, i, ps)[k] == if i <= k < i + ps.len() {
            ps[k - i]
        } else {
            addr[k]
        } by {
            if i + 1 <= k < i + ps.len() {
                assert(rest[k - (i + 1)] == ps[k - i]);
            }
        }
    }
}

/// IPv6 parser step 7.3, the swaps, from a state partway through. The
/// right-hand pieces `r` start at `compress`; `s` of them are still there
/// and the rest are already at the end.
pub proof fn lemma_ipv6_swaps(addr: Seq<nat>, pi: int, compress: int, s: int, r: Seq<nat>)
    requires
        addr.len() == 8,
        1 <= compress,
        compress + r.len() <= 8,
        0 <= s <= r.len(),
        pi == 7 - (r.len() - s),
        forall|j: int| 0 <= j < s ==> addr[compress + j] == r[j],
        forall|j: int| s <= j < r.len() ==> addr[pi + 1 + (j - s)] == r[j],
        forall|k: int| compress + s <= k <= pi ==> addr[k] == 0,
    ensures
        ipv6_swaps(addr, pi, compress, s) == addr.subrange(0, compress) + Seq::new(
            (8 - r.len() - compress) as nat,
            |_i: int| 0nat,
        ) + r,
    decreases s
{
    let zeros = Seq::new((8 - r.len() - compress) as nat, |_i: int| 0nat);
    if s > 0 {
        let other = compress + s - 1;
        let swapped = addr.update(pi, addr[other]).update(other, addr[pi]);
        assert(pi != 0);
        assert forall|j: int| 0 <= j < s - 1 implies swapped[compress + j] == r[j] by {}
        assert forall|j: int| s - 1 <= j < r.len() implies swapped[pi - 1 + 1 + (j - (s - 1))] == r[j] by {
            if j == s - 1 {
                if other == pi {
                } else {
                    assert(addr[pi] == 0);
                }
            }
        }
        assert forall|k: int| compress + (s - 1) <= k <= pi - 1 implies swapped[k] == 0 by {
            if k == other {
                assert(addr[pi] == 0);
            }
        }
        lemma_ipv6_swaps(swapped, pi - 1, compress, s - 1, r);
        assert(swapped.subrange(0, compress) =~= addr.subrange(0, compress));
    } else {
        assert(ipv6_swaps(addr, pi, compress, s) == addr);
        assert(addr =~= addr.subrange(0, compress) + zeros + r) by {
            assert forall|k: int| 0 <= k < 8 implies #[trigger] addr[k] == (addr.subrange(0, compress) + zeros + r)[k] by {
                if compress <= k < 8 - r.len() {
                    assert(addr[k] == 0);
                } else if k >= 8 - r.len() {
                    assert(addr[pi + 1 + (k - (8 - r.len()))] == r[k - (8 - r.len())]);
                }
            }
        }
    }
}

// ---------------------------------------------------------------------
// Zero runs.
// ---------------------------------------------------------------------

/// A zero run is all zeros, and ends at the end or at a non-zero piece.
pub proof fn lemma_zero_run(a: Seq<nat>, i: int)
    requires
        0 <= i <= a.len(),
    ensures
        i + zero_run_len(a, i) <= a.len(),
        forall|k: int| i <= k < i + zero_run_len(a, i) ==> #[trigger] a[k] == 0,
        i + zero_run_len(a, i) < a.len() ==> a[i + zero_run_len(a, i)] != 0,
    decreases a.len() - i
{
    if i < a.len() && a[i] == 0 {
        lemma_zero_run(a, i + 1);
    }
}

// ---------------------------------------------------------------------
// The IPv6 serializer's text.
// ---------------------------------------------------------------------

/// "Find the IPv6 address compressed piece index" returns the index of a
/// zero piece, if any.
pub proof fn lemma_find_compressed_loop(a: Seq<nat>, pi: nat, li: Option<int>, ls: nat, fi: Option<int>, fs: nat)
    requires
        pi <= a.len(),
        li matches Some(l) ==> 0 <= l < a.len() && a[l] == 0,
        fi matches Some(f) ==> 0 <= f < a.len() && a[f] == 0,
    ensures
        find_compressed_loop(a, pi, li, ls, fi, fs) matches Some(c) ==> 0 <= c < a.len() && a[c] == 0,
    decreases a.len() - pi
{
    if pi < a.len() {
        if a[pi as int] != 0 {
            let (l2, s2) = if fs > ls {
                (fi, fs)
            } else {
                (li, ls)
            };
            lemma_find_compressed_loop(a, pi + 1, l2, s2, None, 0);
        } else {
            let f2 = if fi is None {
                Some(pi as int)
            } else {
                fi
            };
            lemma_find_compressed_loop(a, pi + 1, li, ls, f2, fs + 1);
        }
    }
}

/// The serializer loop writes pieces `i` to `j` (none of them compress),
/// each followed by ":".
pub proof fn lemma_serializer_colons(a: Seq<nat>, compress: Option<int>, i: int, j: int, out: Seq<u32>)
    requires
        a.len() == 8,
        0 <= i <= j <= 7,
        forall|k: int| i <= k < j ==> compress != Some(k),
    ensures
        ipv6_serializer_loop(a, compress, false, i as nat, out) == ipv6_serializer_loop(
            a,
            compress,
            false,
            j as nat,
            out + hex_text_colons(a.subrange(i, j)),
        ),
    decreases j - i
{
    if i < j {
        let t = shortest_lowercase_hex(a[i]);
        assert(a.subrange(i, j).drop_first() =~= a.subrange(i + 1, j));
        lemma_serializer_colons(a, compress, i + 1, j, out + t + seq![0x3Au32]);
        assert(out + t + seq![0x3Au32] + hex_text_colons(a.subrange(i + 1, j)) =~= out + hex_text_colons(a.subrange(i, j)));
    } else {
        assert(hex_text_colons(a.subrange(i, j)) =~= Seq::<u32>::empty());
        assert(out + Seq::<u32>::empty() =~= out);
    }
}

/// With ignore0 set, the serializer loop skips a run of zeros.
pub proof fn lemma_serializer_skip(a: Seq<nat>, compress: Option<int>, i: int, out: Seq<u32>)
    requires
        a.len() == 8,
        0 <= i <= 8,
    ensures
        ipv6_serializer_loop(a, compress, true, i as nat, out) == ipv6_serializer_loop(
            a,
            compress,
            true,
            (i + zero_run_len(a, i)) as nat,
            out,
        ),
    decreases 8 - i
{
    if i < 8 && a[i] == 0 {
        lemma_serializer_skip(a, compress, i + 1, out);
    }
}

/// The serializer loop writes pieces `i` to 7 (none of them compress),
/// separated by ":".
pub proof fn lemma_serializer_list(a: Seq<nat>, compress: Option<int>, ignore0: bool, i: int, out: Seq<u32>)
    requires
        a.len() == 8,
        0 <= i <= 8,
        !ignore0 || i == 8 || a[i] != 0,
        forall|k: int| i <= k < 8 ==> compress != Some(k),
    ensures
        ipv6_serializer_loop(a, compress, ignore0, i as nat, out) == out + hex_text(a.subrange(i, 8)),
    decreases 8 - i
{
    if i == 8 {
        assert(hex_text(a.subrange(i, 8)) =~= Seq::<u32>::empty());
        assert(out + Seq::<u32>::empty() =~= out);
    } else if i == 7 {
        let t = shortest_lowercase_hex(a[7]);
        lemma_serializer_list(a, compress, false, 8, out + t);
        assert(a.subrange(7, 8).len() == 1);
        assert(hex_text(a.subrange(7, 8)) == t);
        assert(out + t + hex_text(a.subrange(8, 8)) =~= out + t) by {
            assert(hex_text(a.subrange(8, 8)) =~= Seq::<u32>::empty());
        }
    } else {
        let t = shortest_lowercase_hex(a[i]);
        lemma_serializer_list(a, compress, false, i + 1, out + t + seq![0x3Au32]);
        assert(a.subrange(i, 8).drop_first() =~= a.subrange(i + 1, 8));
        assert(out + t + seq![0x3Au32] + hex_text(a.subrange(i + 1, 8)) =~= out + hex_text(a.subrange(i, 8)));
    }
}

/// The IPv6 serializer's output: all eight pieces separated by ":", or,
/// with a compressed run of zeros at `c`, the pieces before it (each
/// followed by ":"), ":" (or "::" if `c` is 0), and the pieces after the
/// run.
pub proof fn lemma_ipv6_serializer_text(a: Seq<nat>)
    requires
        a.len() == 8,
    ensures
        match find_ipv6_compressed_piece_index(a) {
            None => ipv6_serializer(a) == hex_text(a),
            Some(c) => 0 <= c < 8 && a[c] == 0 && ipv6_serializer(a) == hex_text_colons(a.subrange(0, c)) + (if c == 0 {
                seq![0x3Au32, 0x3A]
            } else {
                seq![0x3Au32]
            }) + hex_text(a.subrange(c + zero_run_len(a, c), 8)),
        },
{
    lemma_find_compressed_loop(a, 0, None, 1, None, 0);
    match find_ipv6_compressed_piece_index(a) {
        None => {
            lemma_serializer_list(a, None, false, 0, seq![]);
            assert(a.subrange(0, 8) =~= a);
            assert(Seq::<u32>::empty() + hex_text(a) =~= hex_text(a));
        },
        Some(c) => {
            let comp = Some(c);
            lemma_serializer_colons(a, comp, 0, c, seq![]);
            let out1 = Seq::<u32>::empty() + hex_text_colons(a.subrange(0, c));
            let sep = if c == 0 {
                seq![0x3Au32, 0x3A]
            } else {
                seq![0x3Au32]
            };
            assert(ipv6_serializer_loop(a, comp, false, c as nat, out1) == ipv6_serializer_loop(a, comp, true, (c + 1) as nat, out1 + sep));
            lemma_zero_run(a, c);
            lemma_zero_run(a, c + 1);
            lemma_serializer_skip(a, comp, c + 1, out1 + sep);
            let m = c + zero_run_len(a, c);
            assert(zero_run_len(a, c) == 1 + zero_run_len(a, c + 1));
            lemma_serializer_list(a, comp, true, m, out1 + sep);
            assert(out1 =~= hex_text_colons(a.subrange(0, c)));
        },
    }
}

} // verus!
