//! Executable path operations (URL §4.2): appending a segment, shortening
//! a path, and Windows drive letters. Each is proven equal to its spec
//! definition.

use super::record::{ParsedPath, ParsedUrl, is_file, segments_view};
use crate::host::record::at32;
#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The view of a list with one more segment.
pub proof fn lemma_segments_push(v: Seq<Vec<u32>>, s: Vec<u32>)
    ensures
        segments_view(v.push(s)) == segments_view(v).push(s@),
{
    assert(segments_view(v.push(s)) =~= segments_view(v).push(s@)) by {
        assert forall|k: int| 0 <= k < v.len() + 1 implies #[trigger] segments_view(v.push(s))[k] == segments_view(
            v,
        ).push(s@)[k] by {
            if k < v.len() {
                assert(v.push(s)[k] == v[k]);
            }
        }
    }
}

/// The view of a list with its last segment removed.
pub proof fn lemma_segments_drop_last(v: Seq<Vec<u32>>)
    requires
        v.len() > 0,
    ensures
        segments_view(v.drop_last()) == segments_view(v).drop_last(),
{
    assert(segments_view(v.drop_last()) =~= segments_view(v).drop_last());
}

/// "Append" `segment` to a path that is a list.
pub fn path_append_exec(path: &mut ParsedPath, segment: Vec<u32>)
    ensures
        final(path)@ == path_append(old(path)@, segment@),
{
    match path {
        ParsedPath::List(l) => {
            proof {
                lemma_segments_push(l@, segment);
            }
            l.push(segment);
        },
        ParsedPath::Opaque(_) => {},
    }
}

/// Append `s` to an opaque path.
pub fn opaque_path_append_exec(path: &mut ParsedPath, s: &[u32])
    ensures
        final(path)@ == opaque_path_append(old(path)@, s@),
{
    match path {
        ParsedPath::Opaque(o) => crate::host::record::append(o, s),
        ParsedPath::List(_) => {},
    }
}

/// Append `s` to a query or fragment.
pub fn opt_append_exec(o: &mut Option<Vec<u32>>, s: &[u32])
    ensures
        crate::host::record::opt_seq(*final(o)) == query_append(crate::host::record::opt_seq(*old(o)), s@),
        crate::host::record::opt_seq(*final(o)) == fragment_append(crate::host::record::opt_seq(*old(o)), s@),
{
    match o {
        Some(v) => crate::host::record::append(v, s),
        None => {
            *o = Some(crate::host::record::copy(s));
        },
    }
}

/// A Windows drive letter (URL §4.2).
pub fn is_windows_drive_letter_exec(s: &[u32]) -> (r: bool)
    ensures
        r == is_windows_drive_letter(s@),
{
    s.len() == 2 && super::machine::is_ascii_alpha_exec(at32(s, 0)) && (at32(s, 1) == 0x3A || at32(s, 1) == 0x7C)
}

/// A normalized Windows drive letter (URL §4.2).
pub fn is_normalized_windows_drive_letter_exec(s: &[u32]) -> (r: bool)
    ensures
        r == is_normalized_windows_drive_letter(s@),
{
    is_windows_drive_letter_exec(s) && at32(s, 1) == 0x3A
}

/// The code point substring of `input` from `p` to the end starts with a
/// Windows drive letter (URL §4.2).
pub fn starts_with_windows_drive_letter_at(input: &[u32], p: usize) -> (r: bool)
    requires
        p <= input.len(),
    ensures
        r == starts_with_windows_drive_letter(input@.subrange(p as int, input@.len() as int)),
{
    let ghost s = input@.subrange(p as int, input@.len() as int);
    let n = input.len() - p;
    if n < 2 {
        return false;
    }
    let c0 = at32(input, p);
    let c1 = at32(input, p + 1);
    assert(s.subrange(0, 2) =~= seq![c0, c1]);
    if !(super::machine::is_ascii_alpha_exec(c0) && (c1 == 0x3A || c1 == 0x7C)) {
        return false;
    }
    if n == 2 {
        return true;
    }
    let c2 = at32(input, p + 2);
    assert(s[2] == c2);
    c2 == 0x2F || c2 == 0x5C || c2 == 0x3F || c2 == 0x23
}

/// "Shorten url's path" (URL §4.2).
pub fn shorten_exec(url: &mut ParsedUrl)
    ensures
        final(url)@ == shorten(old(url)@),
{
    let file = is_file(url.scheme.as_slice());
    match &mut url.path {
        ParsedPath::Opaque(_) => {},
        ParsedPath::List(l) => {
            let keep = file && l.len() == 1 && is_normalized_windows_drive_letter_exec(l[0].as_slice());
            if !keep && l.len() > 0 {
                proof {
                    lemma_segments_drop_last(l@);
                }
                l.pop();
            }
        },
    }
}

} // verus!
