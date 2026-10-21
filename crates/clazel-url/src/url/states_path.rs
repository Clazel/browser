//! The executable path start, path and opaque path states (URL §4.4),
//! each proven to do what its spec function does
//! ([`super::machine::flow_ok`]). The step comments live in
//! [`super::spec`].

use super::machine::{ExecMachine, Flow, advance, back, c_at_exec};
use super::path_ops::{
    is_windows_drive_letter_exec, opaque_path_append_exec, path_append_exec, shorten_exec,
};
use super::record::{ParsedPath, is_file, is_special_scheme_exec};
#[allow(unused_imports)]
use super::spec::*;
use crate::host::record::{append, at32, copy};
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The ASCII lowercase of a string has the same length, and lowercases
/// each code point.
pub proof fn lemma_ascii_lowercase_string(s: Seq<u32>)
    ensures
        ascii_lowercase_string(s).len() == s.len(),
        forall|k: int| 0 <= k < s.len() ==> #[trigger] ascii_lowercase_string(s)[k] == ascii_lowercase(s[k]),
    decreases s.len(),
{
    if s.len() > 0 {
        lemma_ascii_lowercase_string(s.drop_last());
        assert forall|k: int| 0 <= k < s.len() implies #[trigger] ascii_lowercase_string(s)[k] == ascii_lowercase(s[k]) by {
            if k < s.len() - 1 {
                assert(s.drop_last()[k] == s[k]);
            }
        }
    }
}

/// Whether `s` is an ASCII case-insensitive match for `t` (Infra §4.7).
fn ascii_case_insensitive_match(s: &[u32], t: &[u32]) -> (r: bool)
    ensures
        r == is_ascii_case_insensitive_match(s@, t@),
{
    proof {
        lemma_ascii_lowercase_string(s@);
        lemma_ascii_lowercase_string(t@);
    }
    if s.len() != t.len() {
        return false;
    }
    let mut i: usize = 0;
    while i < s.len()
        invariant
            i <= s.len(),
            s.len() == t.len(),
            ascii_lowercase_string(s@).len() == s.len(),
            ascii_lowercase_string(t@).len() == t.len(),
            forall|k: int| 0 <= k < s.len() ==> #[trigger] ascii_lowercase_string(s@)[k] == ascii_lowercase(s@[k]),
            forall|k: int| 0 <= k < t.len() ==> #[trigger] ascii_lowercase_string(t@)[k] == ascii_lowercase(t@[k]),
            forall|k: int| 0 <= k < i ==> ascii_lowercase_string(s@)[k] == ascii_lowercase_string(t@)[k],
        decreases s.len() - i,
    {
        if super::machine::ascii_lowercase_exec(at32(s, i)) != super::machine::ascii_lowercase_exec(at32(t, i)) {
            assert(ascii_lowercase_string(s@)[i as int] != ascii_lowercase_string(t@)[i as int]);
            return false;
        }
        // Never saturates: i is below a length.
        i = i.saturating_add(1);
    }
    assert(ascii_lowercase_string(s@) =~= ascii_lowercase_string(t@));
    true
}

/// The string of three code points.
fn lit3(a: u32, b: u32, c: u32) -> (v: Vec<u32>)
    ensures
        v@ == seq![a, b, c],
{
    let a: [u32; 3] = [a, b, c];
    let v = copy(&a);
    assert(v@ =~= seq![a[0], a[1], a[2]]);
    v
}

/// The string of four code points.
fn lit4(a: u32, b: u32, c: u32, d: u32) -> (v: Vec<u32>)
    ensures
        v@ == seq![a, b, c, d],
{
    let mut v = lit3(a, b, c);
    v.push(d);
    assert(v@ =~= seq![a, b, c, d]);
    v
}

/// The string of six code points.
fn lit6(a: u32, b: u32, c: u32, d: u32, e: u32, f: u32) -> (v: Vec<u32>)
    ensures
        v@ == seq![a, b, c, d, e, f],
{
    let mut v = lit4(a, b, c, d);
    v.push(e);
    v.push(f);
    assert(v@ =~= seq![a, b, c, d, e, f]);
    v
}

/// A single-dot URL path segment (URL §4.1).
fn is_single_dot_segment_exec(s: &[u32]) -> (r: bool)
    ensures
        r == is_single_dot_segment(s@),
{
    let dot = s.len() == 1 && at32(s, 0) == 0x2E;
    if dot {
        assert(s@ =~= seq![0x2Eu32]);
    }
    proof {
        if s@ == seq![0x2Eu32] {
            assert(s@[0] == 0x2E);
        }
    }
    dot || ascii_case_insensitive_match(s, lit3(0x25, 0x32, 0x65).as_slice())
}

/// A double-dot URL path segment (URL §4.1).
fn is_double_dot_segment_exec(s: &[u32]) -> (r: bool)
    ensures
        r == is_double_dot_segment(s@),
{
    let dots = s.len() == 2 && at32(s, 0) == 0x2E && at32(s, 1) == 0x2E;
    if dots {
        assert(s@ =~= seq![0x2Eu32, 0x2E]);
    }
    proof {
        if s@ == seq![0x2Eu32, 0x2E] {
            assert(s@[0] == 0x2E && s@[1] == 0x2E);
        }
    }
    dots || ascii_case_insensitive_match(s, lit4(0x2E, 0x25, 0x32, 0x65).as_slice())
        || ascii_case_insensitive_match(s, lit4(0x25, 0x32, 0x65, 0x2E).as_slice())
        || ascii_case_insensitive_match(s, lit6(0x25, 0x32, 0x65, 0x25, 0x32, 0x65).as_slice())
}

/// "path start state" (no state override)
pub fn path_start_state(input: &[u32], Ghost(base): Ghost<Option<Url>>, m: &mut ExecMachine) -> (flow: Flow)
    requires
        super::machine::wf(super::machine::ctx_of(input@, base), old(m)@),
        old(m).state is PathStart,
    ensures
        super::machine::flow_ok(super::machine::ctx_of(input@, base), super::spec::path_start_state(super::machine::ctx_of(input@, base), old(m)@), final(m)@, flow),
{
    let c = c_at_exec(input, m.pointer);
    if is_special_scheme_exec(m.url.scheme.as_slice()) {
        // 1.
        m.state = State::Path;
        if c != Some(0x2Fu32) && c != Some(0x5Cu32) {
            back()
        } else {
            advance(m, input.len())
        }
    } else if c == Some(0x3Fu32) {
        // 2.
        m.url.query = Some(Vec::new());
        assert(crate::host::record::opt_seq(m.url.query) == Some(Seq::<u32>::empty()));
        m.state = State::Query;
        advance(m, input.len())
    } else if c == Some(0x23u32) {
        // 3.
        m.url.fragment = Some(Vec::new());
        assert(crate::host::record::opt_seq(m.url.fragment) == Some(Seq::<u32>::empty()));
        m.state = State::Fragment;
        advance(m, input.len())
    } else if c.is_some() {
        // 4.
        m.state = State::Path;
        if c != Some(0x2Fu32) {
            back()
        } else {
            advance(m, input.len())
        }
    } else {
        advance(m, input.len())
    }
}

/// "path state" (no state override)
pub fn path_state(input: &[u32], Ghost(base): Ghost<Option<Url>>, m: &mut ExecMachine) -> (flow: Flow)
    requires
        super::machine::wf(super::machine::ctx_of(input@, base), old(m)@),
        old(m).state is Path,
    ensures
        super::machine::flow_ok(super::machine::ctx_of(input@, base), super::spec::path_state(super::machine::ctx_of(input@, base), old(m)@), final(m)@, flow),
{
    let c = c_at_exec(input, m.pointer);
    let special = is_special_scheme_exec(m.url.scheme.as_slice());
    let slash = c == Some(0x2Fu32) || (special && c == Some(0x5Cu32));
    if c.is_none() || slash || c == Some(0x3Fu32) || c == Some(0x23u32) {
        // 1.
        if is_double_dot_segment_exec(m.buffer.as_slice()) {
            // 1.2.1
            shorten_exec(&mut m.url);
            if !slash {
                // 1.2.2
                let empty: Vec<u32> = Vec::new();
                assert(empty@ =~= Seq::<u32>::empty());
                path_append_exec(&mut m.url.path, empty);
            }
        } else if is_single_dot_segment_exec(m.buffer.as_slice()) {
            if !slash {
                // 1.3
                let empty: Vec<u32> = Vec::new();
                assert(empty@ =~= Seq::<u32>::empty());
                path_append_exec(&mut m.url.path, empty);
            }
        } else {
            // 1.4.1
            let mut buffer = copy(m.buffer.as_slice());
            let empty = match &m.url.path {
                ParsedPath::List(l) => l.is_empty(),
                ParsedPath::Opaque(_) => false,
            };
            assert(empty == (m.url.path@ == UrlPath::List(seq![]))) by {
                if m.url.path@ == UrlPath::List(seq![]) {
                    assert(super::record::segments_view(m.url.path->List_0@).len() == 0);
                }
                if empty {
                    assert(super::record::segments_view(m.url.path->List_0@) =~= Seq::<Seq<u32>>::empty());
                }
            }
            if is_file(m.url.scheme.as_slice()) && empty && is_windows_drive_letter_exec(buffer.as_slice()) {
                buffer.set(1, 0x3A);
            }
            // 1.4.2
            path_append_exec(&mut m.url.path, buffer);
        }
        // 1.5
        m.buffer = Vec::new();
        assert(m.buffer@ =~= seq![]);
        if c == Some(0x3Fu32) {
            // 1.6
            m.url.query = Some(Vec::new());
            assert(crate::host::record::opt_seq(m.url.query) == Some(Seq::<u32>::empty()));
            m.state = State::Query;
        } else if c == Some(0x23u32) {
            // 1.7
            m.url.fragment = Some(Vec::new());
            assert(crate::host::record::opt_seq(m.url.fragment) == Some(Seq::<u32>::empty()));
            m.state = State::Fragment;
        }
        advance(m, input.len())
    } else {
        // 2.3
        let c = at32(input, m.pointer);
        assert(clazel_encoding::utf8::spec::is_scalar_value(input@[m.pointer as int]));
        let encoded = clazel_percent::encode::utf8_percent_encode_code_point(c, clazel_percent::spec::PercentEncodeSet::Path);
        append(&mut m.buffer, encoded.as_slice());
        advance(m, input.len())
    }
}

/// "opaque path state"
pub fn opaque_path_state(input: &[u32], Ghost(base): Ghost<Option<Url>>, m: &mut ExecMachine) -> (flow: Flow)
    requires
        super::machine::wf(super::machine::ctx_of(input@, base), old(m)@),
        old(m).state is OpaquePath,
    ensures
        super::machine::flow_ok(super::machine::ctx_of(input@, base), super::spec::opaque_path_state(super::machine::ctx_of(input@, base), old(m)@), final(m)@, flow),
{
    let c = c_at_exec(input, m.pointer);
    if c == Some(0x3Fu32) {
        // 1.
        m.url.query = Some(Vec::new());
        assert(crate::host::record::opt_seq(m.url.query) == Some(Seq::<u32>::empty()));
        m.state = State::Query;
    } else if c == Some(0x23u32) {
        // 2.
        m.url.fragment = Some(Vec::new());
        assert(crate::host::record::opt_seq(m.url.fragment) == Some(Seq::<u32>::empty()));
        m.state = State::Fragment;
    } else if c == Some(0x20u32) {
        // 3.
        if super::machine::remaining_starts_with_exec(input, m.pointer, 0x3F)
            || super::machine::remaining_starts_with_exec(input, m.pointer, 0x23) {
            // 3.2
            opaque_path_append_exec(&mut m.url.path, lit3(0x25, 0x32, 0x30).as_slice());
        } else {
            // 3.3
            let space: [u32; 1] = [0x20];
            assert(space@ =~= seq![0x20u32]);
            opaque_path_append_exec(&mut m.url.path, &space);
        }
    } else if let Some(c) = c {
        // 4.3
        assert(clazel_encoding::utf8::spec::is_scalar_value(input@[m.pointer as int]));
        let encoded = clazel_percent::encode::utf8_percent_encode_code_point(c, clazel_percent::spec::PercentEncodeSet::C0Control);
        opaque_path_append_exec(&mut m.url.path, encoded.as_slice());
    }
    advance(m, input.len())
}

} // verus!
