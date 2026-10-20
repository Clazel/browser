//! Executable Normalization Form C, proven equal to [`super::spec::nfc`]
//! (relative to the tables). Each function mirrors the spec function of
//! the same name.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Canonical_Combining_Class.
pub fn ccc_exec(c: u32) -> (r: u8)
    ensures
        r == ccc(c),
{
    match super::tables::combining_class_find_exec(c) {
        Some(i) => super::data::combining_class_at_exec(i).class,
        None => 0,
    }
}

/// D68 for one code point, appended to `out`.
fn push_full_decomposition(out: &mut Vec<u32>, c: u32)
    ensures
        final(out)@ == old(out)@ + full_decomposition(c),
{
    if (0xAC00..0xAC00 + 11172).contains(&c) {
        // Never wrap: 0xAC00 <= c < 0xAC00 + 11172.
        let s_index = c.saturating_sub(0xAC00);
        let l_part = (s_index / 588).saturating_add(0x1100);
        let v_part = (s_index % 588 / 28).saturating_add(0x1161);
        let t_index = s_index % 28;
        let ghost before = out@;
        out.push(l_part);
        out.push(v_part);
        if t_index != 0 {
            out.push(t_index.saturating_add(0x11A7));
        }
        assert(out@ =~= before + hangul_decomposition(c));
    } else {
        match super::tables::decomposition_find_exec(c) {
            Some(i) => {
                let row = super::data::decomposition_at_exec(i);
                super::tables::push_decomposition_data(out, row.start, row.len);
            },
            None => out.push(c),
        }
    }
}

/// The full canonical decomposition of each code point, in order.
pub fn decompose_exec(s: &[u32]) -> (out: Vec<u32>)
    ensures
        out@ == decompose(s@),
{
    let mut out: Vec<u32> = Vec::new();
    let mut i: usize = 0;
    while i < s.len()
        invariant
            i <= s.len(),
            out@ == decompose(s@.subrange(0, i as int)),
        decreases s.len() - i
    {
        proof {
            let next = s@.subrange(0, i as int + 1);
            assert(next.drop_last() =~= s@.subrange(0, i as int));
        }
        if let Some(&c) = s.get(i) {
            push_full_decomposition(&mut out, c);
        }
        i = i.saturating_add(1);
    }
    assert(s@.subrange(0, s.len() as int) =~= s@);
    out
}

/// D109 for one code point: `done` becomes `insert_ordered(done, c)`.
fn insert_ordered_exec(done: &mut Vec<u32>, c: u32)
    ensures
        final(done)@ == insert_ordered(old(done)@, c),
{
    let ghost old_done = old(done)@;
    let cc = ccc_exec(c);
    if cc == 0 {
        done.push(c);
        return;
    }
    let mut j = done.len();
    assert(old_done.subrange(0, j as int) =~= old_done);
    assert(old_done.subrange(j as int, j as int) =~= Seq::<u32>::empty());
    while j > 0
        invariant
            j <= done.len(),
            done@ == old_done,
            cc == ccc(c),
            cc != 0,
            insert_ordered(old_done, c) == insert_ordered(old_done.subrange(0, j as int), c) + old_done.subrange(
                j as int,
                old_done.len() as int,
            ),
        ensures
            j <= done.len(),
            done@ == old_done,
            j == 0 || ccc(old_done[j - 1]) <= cc,
            insert_ordered(old_done, c) == insert_ordered(old_done.subrange(0, j as int), c) + old_done.subrange(
                j as int,
                old_done.len() as int,
            ),
        decreases j
    {
        let prev = j.saturating_sub(1);
        let d = match done.get(prev) {
            Some(&p) => ccc_exec(p),
            None => 0,
        };
        if d <= cc {
            break;
        }
        proof {
            let p = old_done.subrange(0, j as int);
            assert(p.drop_last() =~= old_done.subrange(0, prev as int));
            assert(p.last() == old_done[prev as int]);
            assert(old_done.subrange(prev as int, old_done.len() as int) =~= seq![p.last()] + old_done.subrange(
                j as int,
                old_done.len() as int,
            ));
            assert(insert_ordered(p, c) == insert_ordered(p.drop_last(), c).push(p.last()));
            assert(insert_ordered(p.drop_last(), c).push(p.last()) + old_done.subrange(j as int, old_done.len() as int)
                =~= insert_ordered(p.drop_last(), c) + old_done.subrange(prev as int, old_done.len() as int));
        }
        j = prev;
    }
    proof {
        let p = old_done.subrange(0, j as int);
        if j > 0 {
            assert(p.last() == old_done[j - 1]);
        }
        assert(insert_ordered(p, c) == p.push(c));
    }
    done.insert(j, c);
    assert(done@ =~= old_done.subrange(0, j as int).push(c) + old_done.subrange(j as int, old_done.len() as int));
}

/// D109, the Canonical Ordering Algorithm.
pub fn canonical_order_exec(s: &[u32]) -> (out: Vec<u32>)
    ensures
        out@ == canonical_order(s@),
{
    let mut out: Vec<u32> = Vec::new();
    let mut i: usize = 0;
    while i < s.len()
        invariant
            i <= s.len(),
            out@ == canonical_order(s@.subrange(0, i as int)),
        decreases s.len() - i
    {
        proof {
            let next = s@.subrange(0, i as int + 1);
            assert(next.drop_last() =~= s@.subrange(0, i as int));
        }
        if let Some(&c) = s.get(i) {
            insert_ordered_exec(&mut out, c);
        }
        i = i.saturating_add(1);
    }
    assert(s@.subrange(0, s.len() as int) =~= s@);
    out
}

/// D117 R1: the last starter of `done`.
fn last_starter_exec(done: &[u32]) -> (r: Option<usize>)
    ensures
        match r {
            Some(l) => last_starter(done@) == Some(l as nat) && l < done.len(),
            None => last_starter(done@) is None,
        },
{
    let mut j = done.len();
    assert(done@.subrange(0, j as int) =~= done@);
    while j > 0
        invariant
            j <= done.len(),
            last_starter(done@) == last_starter(done@.subrange(0, j as int)),
        decreases j
    {
        let prev = j.saturating_sub(1);
        proof {
            let p = done@.subrange(0, j as int);
            assert(p.drop_last() =~= done@.subrange(0, prev as int));
        }
        match done.get(prev) {
            Some(&c) if ccc_exec(c) == 0 => return Some(prev),
            _ => {},
        }
        j = prev;
    }
    None
}

/// D115 from position `b`.
fn blocked_from_exec(done: &[u32], b: usize, c: u32) -> (r: bool)
    ensures
        r == blocked_from(done@, b as nat, c),
{
    let cc = ccc_exec(c);
    let mut k = b;
    while k < done.len()
        invariant
            cc == ccc(c),
            blocked_from(done@, b as nat, c) == blocked_from(done@, k as nat, c),
        decreases done.len() - k
    {
        if let Some(&d) = done.get(k) {
            let dc = ccc_exec(d);
            if dc == 0 || dc >= cc {
                return true;
            }
        }
        k = k.saturating_add(1);
    }
    false
}

/// The Primary Composite canonically equivalent to `<l, c>`.
fn primary_composite_exec(l: u32, c: u32) -> (r: Option<u32>)
    ensures
        r == primary_composite(l, c),
{
    if (0x1100..0x1100 + 19).contains(&l) && (0x1161..0x1161 + 21).contains(&c) {
        // Never wrap: l - LBase < 19 and c - VBase < 21.
        let l_index = l.saturating_sub(0x1100);
        let v_index = c.saturating_sub(0x1161);
        Some(l_index.saturating_mul(588).saturating_add(v_index.saturating_mul(28)).saturating_add(0xAC00))
    } else if (0xAC00..0xAC00 + 11172).contains(&l) && l.saturating_sub(0xAC00).is_multiple_of(28) && 0x11A7 < c && c
        < 0x11A7 + 28 {
        // Never wrap: c - TBase < 28 and l < SBase + SCount.
        Some(l.saturating_add(c.saturating_sub(0x11A7)))
    } else {
        let i = super::tables::composition_find_exec(l, c)?;
        Some(super::data::composition_at_exec(i).composite)
    }
}

/// D117 for one code point: `done` becomes `compose_step(done, c)`.
fn compose_step_exec(done: &mut Vec<u32>, c: u32)
    ensures
        final(done)@ == compose_step(old(done)@, c),
{
    match last_starter_exec(done) {
        Some(l) => {
            if !blocked_from_exec(done, l.saturating_add(1), c) {
                let starter = match done.get(l) {
                    Some(&s) => s,
                    None => 0,
                };
                match primary_composite_exec(starter, c) {
                    Some(p) => done.set(l, p),
                    None => done.push(c),
                }
            } else {
                done.push(c);
            }
        },
        None => done.push(c),
    }
}

/// D117, the Canonical Composition Algorithm.
pub fn compose_exec(s: &[u32]) -> (out: Vec<u32>)
    ensures
        out@ == compose(s@),
{
    let mut out: Vec<u32> = Vec::new();
    match s.first() {
        Some(&first) => out.push(first),
        None => return out,
    }
    let mut i: usize = 1;
    assert(s@.subrange(0, 1) =~= out@);
    while i < s.len()
        invariant
            1 <= i <= s.len(),
            out@ == compose(s@.subrange(0, i as int)),
        decreases s.len() - i
    {
        proof {
            let next = s@.subrange(0, i as int + 1);
            assert(next.drop_last() =~= s@.subrange(0, i as int));
        }
        if let Some(&c) = s.get(i) {
            compose_step_exec(&mut out, c);
        }
        i = i.saturating_add(1);
    }
    assert(s@.subrange(0, s.len() as int) =~= s@);
    out
}

/// Normalization Form C.
pub fn nfc(s: &[u32]) -> (out: Vec<u32>)
    ensures
        super::contract::nfc_ensures(s@, out@),
{
    let decomposed = decompose_exec(s);
    let ordered = canonical_order_exec(&decomposed);
    compose_exec(&ordered)
}

} // verus!

#[cfg(test)]
mod tests {
    use super::nfc;

    fn run(s: &str) -> String {
        let input: Vec<u32> = s.chars().map(u32::from).collect();
        nfc(&input).into_iter().filter_map(char::from_u32).collect()
    }

    #[test]
    fn examples() {
        assert_eq!(run("a\u{300}"), "\u{E0}");
        assert_eq!(run("\u{E0}"), "\u{E0}");
        // Hangul L + V + T composes to one syllable.
        assert_eq!(run("\u{1100}\u{1161}\u{11A8}"), "\u{AC01}");
        // Reordering: dot below (220) before dot above (230), then
        // composition with both.
        assert_eq!(run("s\u{307}\u{323}"), "\u{1E69}");
        // A composition exclusion stays decomposed.
        assert_eq!(run("\u{958}"), "\u{915}\u{93C}");
        // Singleton: Ohm sign to Omega.
        assert_eq!(run("\u{2126}"), "\u{3A9}");
        assert_eq!(run(""), "");
    }
}
