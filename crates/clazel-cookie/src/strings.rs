//! Executable string helpers shared by the cookie algorithms, over octets.
//! Each is proven equal to its spec definition in [`crate::ascii`].

#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// A copy of `s`.
pub fn copy(s: &[u8]) -> (out: Vec<u8>)
    ensures
        out@ == s@,
{
    vstd::slice::slice_to_vec(s)
}

/// The octets of `s` from `start` up to, but not including, `end`.
pub fn sub(s: &[u8], start: usize, end: usize) -> (out: Vec<u8>)
    requires
        start <= end <= s.len(),
    ensures
        out@ == s@.subrange(start as int, end as int),
{
    copy(vstd::slice::slice_subrange(s, start, end))
}

/// Append `s` to `out`.
pub fn append(out: &mut Vec<u8>, s: &[u8])
    ensures
        final(out)@ == old(out)@ + s@,
{
    let ghost start = out@;
    let mut i: usize = 0;
    while i < s.len()
        invariant
            i <= s.len(),
            out@ == start + s@.subrange(0, i as int),
        decreases s.len() - i,
    {
        if let Some(c) = s.get(i) {
            out.push(*c);
        }
        assert(s@.subrange(0, i as int).push(s@[i as int]) =~= s@.subrange(0, i as int + 1));
        // Never saturates: i < s.len().
        i = i.saturating_add(1);
    }
    assert(s@.subrange(0, s.len() as int) =~= s@);
}

/// The octet at `position`, if `position` is not past the end.
pub fn at(input: &[u8], position: usize) -> (r: Option<u8>)
    ensures
        position < input.len() ==> r == Some(input@[position as int]),
        position >= input.len() ==> r is None,
{
    if let Some(c) = input.get(position) {
        return Some(*c);
    }
    None
}

/// Are `a` and `b` the same string?
pub fn slice_eq(a: &[u8], b: &[u8]) -> (r: bool)
    ensures
        r == (a@ == b@),
{
    if a.len() != b.len() {
        return false;
    }
    let mut i: usize = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            a.len() == b.len(),
            forall|k: int| 0 <= k < i ==> a@[k] == b@[k],
        decreases a.len() - i,
    {
        if at(a, i) != at(b, i) {
            return false;
        }
        // Never saturates: i < a.len().
        i = i.saturating_add(1);
    }
    assert(a@ =~= b@);
    true
}

/// [`crate::ascii::is_digit`].
pub fn is_digit_exec(c: u8) -> (r: bool)
    ensures
        r == crate::ascii::is_digit(c),
{
    (0x30..=0x39).contains(&c)
}

/// [`crate::ascii::is_wsp`].
pub fn is_wsp_exec(c: u8) -> (r: bool)
    ensures
        r == crate::ascii::is_wsp(c),
{
    c == 0x20 || c == 0x09
}

/// [`crate::ascii::ascii_lowercase_octet`].
pub fn ascii_lowercase_octet_exec(c: u8) -> (r: u8)
    ensures
        r == crate::ascii::ascii_lowercase_octet(c),
{
    // Never saturates: c <= 0x5A here.
    if (0x41..=0x5A).contains(&c) { c.saturating_add(0x20) } else { c }
}

/// The ASCII lowercase of `s`.
pub fn ascii_lowercase_exec(s: &[u8]) -> (out: Vec<u8>)
    ensures
        out@ == crate::ascii::ascii_lowercase(s@),
{
    let mut out: Vec<u8> = Vec::new();
    let mut i: usize = 0;
    while i < s.len()
        invariant
            i <= s.len(),
            out@ == crate::ascii::ascii_lowercase(s@).subrange(0, i as int),
        decreases s.len() - i,
    {
        if let Some(c) = s.get(i) {
            out.push(ascii_lowercase_octet_exec(*c));
        }
        assert(crate::ascii::ascii_lowercase(s@).subrange(0, i as int + 1) =~= out@);
        // Never saturates: i < s.len().
        i = i.saturating_add(1);
    }
    assert(crate::ascii::ascii_lowercase(s@).subrange(0, s.len() as int) =~= crate::ascii::ascii_lowercase(s@));
    out
}

/// "case-insensitively match" (§2.3).
pub fn case_insensitive_match_exec(a: &[u8], b: &[u8]) -> (r: bool)
    ensures
        r == crate::ascii::case_insensitive_match(a@, b@),
{
    let la = ascii_lowercase_exec(a);
    let lb = ascii_lowercase_exec(b);
    slice_eq(la.as_slice(), lb.as_slice())
}

/// "begins with a case-insensitive match for the string" `prefix`.
pub fn begins_with_case_insensitive_match_exec(s: &[u8], prefix: &[u8]) -> (r: bool)
    ensures
        r == crate::ascii::begins_with_case_insensitive_match(s@, prefix@),
{
    if s.len() < prefix.len() {
        return false;
    }
    let head = vstd::slice::slice_subrange(s, 0, prefix.len());
    case_insensitive_match_exec(head, prefix)
}

/// The index of the first `c` in `s` at or after `from`, or `s.len()`.
pub fn find_octet_exec(s: &[u8], c: u8, from: usize) -> (r: usize)
    ensures
        r == crate::ascii::find_octet(s@, c, from as nat),
{
    let mut i = from;
    while i < s.len()
        invariant
            crate::ascii::find_octet(s@, c, from as nat) == crate::ascii::find_octet(s@, c, i as nat),
        decreases s.len() - i,
    {
        if at(s, i) == Some(c) {
            return i;
        }
        // Never saturates: i < s.len().
        i = i.saturating_add(1);
    }
    s.len()
}

/// Is `s[i]` WSP?
fn is_wsp_at(s: &[u8], i: usize) -> (r: bool)
    requires
        i < s.len(),
    ensures
        r == crate::ascii::is_wsp(s@[i as int]),
{
    match s.get(i) {
        Some(c) => is_wsp_exec(*c),
        None => false,
    }
}

/// Remove any trailing WSP from `s`.
pub fn remove_trailing_wsp_exec(s: &[u8]) -> (out: Vec<u8>)
    ensures
        out@ == crate::ascii::remove_trailing_wsp(s@),
{
    let mut end = s.len();
    assert(s@.subrange(0, end as int) =~= s@);
    // Never saturates: end > 0.
    while end > 0 && is_wsp_at(s, end.saturating_sub(1))
        invariant
            end <= s.len(),
            crate::ascii::remove_trailing_wsp(s@) == crate::ascii::remove_trailing_wsp(s@.subrange(0, end as int)),
        decreases end,
    {
        let last = end.saturating_sub(1);
        assert(s@.subrange(0, end as int).last() == s@[last as int]);
        assert(s@.subrange(0, end as int).drop_last() =~= s@.subrange(0, last as int));
        end = last;
    }
    if end > 0 {
        assert(s@.subrange(0, end as int).last() == s@[end - 1]);
    }
    let out = sub(s, 0, end);
    assert(out@ == crate::ascii::remove_trailing_wsp(out@));
    out
}

/// Remove any leading and trailing WSP from `s`.
pub fn remove_leading_and_trailing_wsp_exec(s: &[u8]) -> (out: Vec<u8>)
    ensures
        out@ == crate::ascii::remove_leading_and_trailing_wsp(s@),
{
    let mut start: usize = 0;
    assert(s@.subrange(0, s.len() as int) =~= s@);
    while start < s.len() && is_wsp_at(s, start)
        invariant
            start <= s.len(),
            crate::ascii::remove_leading_wsp(s@) == crate::ascii::remove_leading_wsp(s@.subrange(start as int, s.len() as int)),
        decreases s.len() - start,
    {
        assert(s@.subrange(start as int, s.len() as int)[0] == s@[start as int]);
        assert(s@.subrange(start as int, s.len() as int).skip(1) =~= s@.subrange(start as int + 1, s.len() as int));
        // Never saturates: start < s.len().
        start = start.saturating_add(1);
    }
    if start < s.len() {
        assert(s@.subrange(start as int, s.len() as int)[0] == s@[start as int]);
    }
    let rest = vstd::slice::slice_subrange(s, start, s.len());
    assert(rest@ == crate::ascii::remove_leading_wsp(rest@));
    remove_trailing_wsp_exec(rest)
}

} // verus!
