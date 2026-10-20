//! The executable MIME type record, and the string helpers the other exec
//! modules share. Each helper is proven equal to its spec definition.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// A MIME type record (MIME Sniffing §4.1), viewed as
/// [`MimeTypeRecord`]. Strings are scalar values as `u32`.
pub struct MimeType {
    /// The type.
    pub type_: Vec<u32>,
    /// The subtype.
    pub subtype: Vec<u32>,
    /// The parameters: an ordered map, as its (name, value) entries in order.
    pub parameters: Vec<(Vec<u32>, Vec<u32>)>,
}

/// The spec view of a parameters list.
pub open spec fn parameters_view(p: Seq<(Vec<u32>, Vec<u32>)>) -> OrderedMap {
    p.map_values(|e: (Vec<u32>, Vec<u32>)| (e.0@, e.1@))
}

impl View for MimeType {
    type V = MimeTypeRecord;

    open spec fn view(&self) -> MimeTypeRecord {
        MimeTypeRecord {
            type_: self.type_@,
            subtype: self.subtype@,
            parameters: parameters_view(self.parameters@),
        }
    }
}

/// The view of an optional MIME type; `None` is failure.
pub open spec fn option_view(m: Option<MimeType>) -> Option<MimeTypeRecord> {
    match m {
        Some(m) => Some(m@),
        None => None,
    }
}

impl MimeType {
    /// The essence of this MIME type (§4.2).
    pub fn essence(&self) -> (output: Vec<u32>)
        ensures
            super::contract::essence_ensures(self@, output@),
    {
        let mut out = copy(self.type_.as_slice());
        out.push(0x2F);
        append(&mut out, self.subtype.as_slice());
        assert(out@ =~= essence(self@));
        out
    }
}

/// A copy of `s`.
pub fn copy(s: &[u32]) -> (out: Vec<u32>)
    ensures
        out@ == s@,
{
    vstd::slice::slice_to_vec(s)
}

/// Append `s` to `out`.
pub fn append(out: &mut Vec<u32>, s: &[u32])
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

/// The code point at `position`, if `position` is not past the end.
pub fn at(input: &[u32], position: usize) -> (r: Option<u32>)
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
pub fn slice_eq(a: &[u32], b: &[u32]) -> (r: bool)
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

/// ASCII lowercase (Infra §4.7).
pub fn ascii_lowercase_exec(s: &[u32]) -> (out: Vec<u32>)
    ensures
        out@ == ascii_lowercase(s@),
{
    let mut out: Vec<u32> = Vec::new();
    let mut i: usize = 0;
    while i < s.len()
        invariant
            i <= s.len(),
            out@ == ascii_lowercase(s@).subrange(0, i as int),
        decreases s.len() - i,
    {
        if let Some(c) = s.get(i) {
            let c = *c;
            // Never saturates: c <= 0x5A here.
            out.push(if (0x41..=0x5A).contains(&c) { c.saturating_add(0x20) } else { c });
        }
        assert(ascii_lowercase(s@).subrange(0, i as int + 1) =~= out@);
        // Never saturates: i < s.len().
        i = i.saturating_add(1);
    }
    assert(ascii_lowercase(s@).subrange(0, s.len() as int) =~= ascii_lowercase(s@));
    out
}

/// Is `c` an HTTP token code point (MIME Sniffing §3)?
pub fn is_http_token_code_point_exec(c: u32) -> (r: bool)
    ensures
        r == is_http_token_code_point(c),
{
    matches!(c, 0x21 | 0x23 | 0x24 | 0x25 | 0x26 | 0x27 | 0x2A | 0x2B | 0x2D | 0x2E | 0x5E | 0x5F | 0x60 | 0x7C | 0x7E)
        || (0x30..=0x39).contains(&c) || (0x41..=0x5A).contains(&c) || (0x61..=0x7A).contains(&c)
}

/// Does `s` solely contain HTTP token code points?
pub fn solely_http_token_code_points_exec(s: &[u32]) -> (r: bool)
    ensures
        r == solely_http_token_code_points(s@),
{
    proof {
        super::lemmas::lemma_solely_token(s@);
    }
    let mut i: usize = 0;
    while i < s.len()
        invariant
            i <= s.len(),
            forall|k: int| 0 <= k < i ==> is_http_token_code_point(#[trigger] s@[k]),
        decreases s.len() - i,
    {
        let ok = match s.get(i) {
            Some(c) => is_http_token_code_point_exec(*c),
            None => true,
        };
        if !ok {
            {
                proof {
                    super::lemmas::lemma_solely_token(s@);
                }
                assert(!is_http_token_code_point(s@[i as int]));
                return false;
            }
        }
        // Never saturates: i < s.len().
        i = i.saturating_add(1);
    }
    true
}

/// Does `s` solely contain HTTP quoted-string token code points?
pub fn solely_http_quoted_string_token_code_points_exec(s: &[u32]) -> (r: bool)
    ensures
        r == solely_http_quoted_string_token_code_points(s@),
{
    proof {
        super::lemmas::lemma_solely_quoted_string_token(s@);
    }
    let mut i: usize = 0;
    while i < s.len()
        invariant
            i <= s.len(),
            forall|k: int| 0 <= k < i ==> is_http_quoted_string_token_code_point(#[trigger] s@[k]),
        decreases s.len() - i,
    {
        let ok = match s.get(i) {
            Some(c) => *c == 0x09 || (0x20..=0x7E).contains(c) || (0x80..=0xFF).contains(c),
            None => true,
        };
        if !ok {
            {
                proof {
                    super::lemmas::lemma_solely_quoted_string_token(s@);
                }
                assert(!is_http_quoted_string_token_code_point(s@[i as int]));
                return false;
            }
        }
        // Never saturates: i < s.len().
        i = i.saturating_add(1);
    }
    true
}

/// Is `c` HTTP whitespace (Fetch §2.2)?
pub fn is_http_whitespace_exec(c: u32) -> (r: bool)
    ensures
        r == is_http_whitespace(c),
{
    c == 0x0A || c == 0x0D || c == 0x09 || c == 0x20
}

/// Is `s[i]` HTTP whitespace?
fn is_http_whitespace_at(s: &[u32], i: usize) -> (r: bool)
    requires
        i < s.len(),
    ensures
        r == is_http_whitespace(s@[i as int]),
{
    match s.get(i) {
        Some(c) => is_http_whitespace_exec(*c),
        None => false,
    }
}

/// Remove any trailing HTTP whitespace from `s`.
pub fn remove_trailing_http_whitespace_exec(s: &[u32]) -> (out: Vec<u32>)
    ensures
        out@ == remove_trailing_http_whitespace(s@),
{
    let mut end = s.len();
    assert(s@.subrange(0, end as int) =~= s@);
    // Never saturates: end > 0.
    while end > 0 && is_http_whitespace_at(s, end.saturating_sub(1))
        invariant
            end <= s.len(),
            remove_trailing_http_whitespace(s@) == remove_trailing_http_whitespace(s@.subrange(0, end as int)),
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
    let out = copy(vstd::slice::slice_subrange(s, 0, end));
    assert(out@ =~= s@.subrange(0, end as int));
    assert(out@ == remove_trailing_http_whitespace(out@));
    out
}

/// Remove any leading and trailing HTTP whitespace from `s`.
pub fn remove_leading_and_trailing_http_whitespace_exec(s: &[u32]) -> (out: Vec<u32>)
    ensures
        out@ == remove_leading_and_trailing_http_whitespace(s@),
{
    let mut start: usize = 0;
    assert(s@.subrange(0, s.len() as int) =~= s@);
    while start < s.len() && is_http_whitespace_at(s, start)
        invariant
            start <= s.len(),
            remove_leading_http_whitespace(s@) == remove_leading_http_whitespace(s@.subrange(start as int, s.len() as int)),
        decreases s.len() - start,
    {
        assert(s@.subrange(start as int, s.len() as int)[0] == s@[start as int]);
        assert(s@.subrange(start as int, s.len() as int).drop_first() =~= s@.subrange(start as int + 1, s.len() as int));
        // Never saturates: start < s.len().
        start = start.saturating_add(1);
    }
    if start < s.len() {
        assert(s@.subrange(start as int, s.len() as int)[0] == s@[start as int]);
    }
    let rest = vstd::slice::slice_subrange(s, start, s.len());
    assert(rest@ == remove_leading_http_whitespace(rest@));
    remove_trailing_http_whitespace_exec(rest)
}

} // verus!
