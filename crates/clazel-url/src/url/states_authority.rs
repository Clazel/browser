//! The executable relative, authority, host, port and file states (URL
//! §4.4), each proven to do what its spec function does
//! ([`super::machine::flow_ok`]). The step comments live in
//! [`super::spec`].

use super::machine::{ExecMachine, Flow, advance, back, c_at_exec, skip};
use super::path_ops::{
    is_normalized_windows_drive_letter_exec, is_windows_drive_letter_exec, path_append_exec,
    shorten_exec, starts_with_windows_drive_letter_at,
};
use super::record::{
    ParsedPath, ParsedUrl, clone_opt_host, clone_opt_str, clone_path, clone_url, default_port_exec,
    is_file, is_special_scheme_exec, new_url_exec,
};
#[allow(unused_imports)]
use super::spec::*;
use crate::host::record::{ParsedHost, append, at32, copy};
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// base, or a new URL if base is null ([`base_of`]).
fn base_url(base: Option<&ParsedUrl>) -> (b: ParsedUrl)
    ensures
        b@ == base_of(super::machine::ctx_of(Seq::empty(), super::record::opt_ref_url_view(base), None)),
{
    match base {
        Some(b) => clone_url(b),
        None => new_url_exec(),
    }
}

/// "file", as a string.
fn file_vec() -> (v: Vec<u32>)
    ensures
        v@ == file_str(),
{
    let a: [u32; 4] = [0x66, 0x69, 0x6C, 0x65];
    let v = copy(&a);
    assert(v@ =~= file_str());
    v
}

/// Whether `s` is "localhost".
fn is_localhost(s: &[u32]) -> (r: bool)
    ensures
        r == (s@ == localhost_str()),
{
    let r = s.len() == 9 && at32(s, 0) == 0x6C && at32(s, 1) == 0x6F && at32(s, 2) == 0x63 && at32(s, 3) == 0x61
        && at32(s, 4) == 0x6C && at32(s, 5) == 0x68 && at32(s, 6) == 0x6F && at32(s, 7) == 0x73 && at32(s, 8)
        == 0x74;
    if r {
        assert(s@ =~= localhost_str());
    }
    proof {
        if s@ == localhost_str() {
            assert(s@[0] == 0x6C && s@[1] == 0x6F && s@[2] == 0x63 && s@[3] == 0x61 && s@[4] == 0x6C);
            assert(s@[5] == 0x68 && s@[6] == 0x6F && s@[7] == 0x73 && s@[8] == 0x74);
        }
    }
    r
}

/// [`ends_authority`]: c is the EOF code point, U+002F (/), U+003F (?) or
/// U+0023 (#), or url is special and c is U+005C (\).
fn ends_authority_exec(c: Option<u32>, special: bool) -> (r: bool)
    ensures
        r == (c is None || c == Some(0x2Fu32) || c == Some(0x3Fu32) || c == Some(0x23u32) || (special && c == Some(
            0x5Cu32,
        ))),
{
    match c {
        None => true,
        Some(c) => c == 0x2F || c == 0x3F || c == 0x23 || (special && c == 0x5C),
    }
}

/// "special relative or authority state"
pub fn special_relative_or_authority_state(input: &[u32], Ghost(base): Ghost<Option<Url>>, Ghost(so): Ghost<Option<State>>, m: &mut ExecMachine) -> (flow: Flow)
    requires
        super::machine::wf(super::machine::ctx_of(input@, base, so), old(m)@),
        old(m).state is SpecialRelativeOrAuthority,
    ensures
        super::machine::flow_ok(super::machine::ctx_of(input@, base, so), super::spec::special_relative_or_authority_state(super::machine::ctx_of(input@, base, so), old(m)@), old(m)@, final(m)@, flow),
{
    if c_at_exec(input, m.pointer) == Some(0x2Fu32) && super::machine::remaining_starts_with_exec(input, m.pointer, 0x2F) {
        m.state = State::SpecialAuthorityIgnoreSlashes;
        skip(m, Ghost(input.len() as nat))
    } else {
        m.state = State::Relative;
        back()
    }
}

/// "path or authority state"
pub fn path_or_authority_state(input: &[u32], Ghost(base): Ghost<Option<Url>>, Ghost(so): Ghost<Option<State>>, m: &mut ExecMachine) -> (flow: Flow)
    requires
        super::machine::wf(super::machine::ctx_of(input@, base, so), old(m)@),
        old(m).state is PathOrAuthority,
    ensures
        super::machine::flow_ok(super::machine::ctx_of(input@, base, so), super::spec::path_or_authority_state(super::machine::ctx_of(input@, base, so), old(m)@), old(m)@, final(m)@, flow),
{
    if c_at_exec(input, m.pointer) == Some(0x2Fu32) {
        m.state = State::Authority;
        advance(m, input.len())
    } else {
        m.state = State::Path;
        back()
    }
}

/// "relative state"
pub fn relative_state(input: &[u32], base: Option<&ParsedUrl>, Ghost(so): Ghost<Option<State>>, m: &mut ExecMachine) -> (flow: Flow)
    requires
        super::machine::wf(super::machine::ctx_of(input@, super::record::opt_ref_url_view(base), so), old(m)@),
        old(m).state is Relative,
    ensures
        super::machine::flow_ok(super::machine::ctx_of(input@, super::record::opt_ref_url_view(base), so), super::spec::relative_state(super::machine::ctx_of(input@, super::record::opt_ref_url_view(base), so), old(m)@), old(m)@, final(m)@, flow),
{
    let b = base_url(base);
    // 2.
    m.url.scheme = b.scheme;
    let c = c_at_exec(input, m.pointer);
    if c == Some(0x2Fu32) {
        // 3.
        m.state = State::RelativeSlash;
        return advance(m, input.len());
    }
    if is_special_scheme_exec(m.url.scheme.as_slice()) && c == Some(0x5Cu32) {
        // 4.
        m.state = State::RelativeSlash;
        return advance(m, input.len());
    }
    // 5.1
    m.url.username = b.username;
    m.url.password = b.password;
    m.url.host = b.host;
    m.url.port = b.port;
    m.url.path = b.path;
    m.url.query = b.query;
    if c == Some(0x3Fu32) {
        // 5.2
        m.url.query = Some(Vec::new());
        assert(crate::host::record::opt_seq(m.url.query) == Some(Seq::<u32>::empty()));
        m.state = State::Query;
        advance(m, input.len())
    } else if c == Some(0x23u32) {
        // 5.3
        m.url.fragment = Some(Vec::new());
        assert(crate::host::record::opt_seq(m.url.fragment) == Some(Seq::<u32>::empty()));
        m.state = State::Fragment;
        advance(m, input.len())
    } else if c.is_some() {
        // 5.4
        m.url.query = None;
        shorten_exec(&mut m.url);
        m.state = State::Path;
        back()
    } else {
        advance(m, input.len())
    }
}

/// "relative slash state"
pub fn relative_slash_state(input: &[u32], base: Option<&ParsedUrl>, Ghost(so): Ghost<Option<State>>, m: &mut ExecMachine) -> (flow: Flow)
    requires
        super::machine::wf(super::machine::ctx_of(input@, super::record::opt_ref_url_view(base), so), old(m)@),
        old(m).state is RelativeSlash,
    ensures
        super::machine::flow_ok(super::machine::ctx_of(input@, super::record::opt_ref_url_view(base), so), super::spec::relative_slash_state(super::machine::ctx_of(input@, super::record::opt_ref_url_view(base), so), old(m)@), old(m)@, final(m)@, flow),
{
    let c = c_at_exec(input, m.pointer);
    let special = is_special_scheme_exec(m.url.scheme.as_slice());
    if special && (c == Some(0x2Fu32) || c == Some(0x5Cu32)) {
        // 1.
        m.state = State::SpecialAuthorityIgnoreSlashes;
        advance(m, input.len())
    } else if c == Some(0x2Fu32) {
        // 2.
        m.state = State::Authority;
        advance(m, input.len())
    } else {
        // 3.
        let b = base_url(base);
        m.url.username = b.username;
        m.url.password = b.password;
        m.url.host = b.host;
        m.url.port = b.port;
        m.state = State::Path;
        back()
    }
}

/// "special authority slashes state"
pub fn special_authority_slashes_state(input: &[u32], Ghost(base): Ghost<Option<Url>>, Ghost(so): Ghost<Option<State>>, m: &mut ExecMachine) -> (flow: Flow)
    requires
        super::machine::wf(super::machine::ctx_of(input@, base, so), old(m)@),
        old(m).state is SpecialAuthoritySlashes,
    ensures
        super::machine::flow_ok(super::machine::ctx_of(input@, base, so), super::spec::special_authority_slashes_state(super::machine::ctx_of(input@, base, so), old(m)@), old(m)@, final(m)@, flow),
{
    m.state = State::SpecialAuthorityIgnoreSlashes;
    if c_at_exec(input, m.pointer) == Some(0x2Fu32) && super::machine::remaining_starts_with_exec(input, m.pointer, 0x2F) {
        skip(m, Ghost(input.len() as nat))
    } else {
        back()
    }
}

/// "special authority ignore slashes state"
pub fn special_authority_ignore_slashes_state(input: &[u32], Ghost(base): Ghost<Option<Url>>, Ghost(so): Ghost<Option<State>>, m: &mut ExecMachine) -> (flow: Flow)
    requires
        super::machine::wf(super::machine::ctx_of(input@, base, so), old(m)@),
        old(m).state is SpecialAuthorityIgnoreSlashes,
    ensures
        super::machine::flow_ok(super::machine::ctx_of(input@, base, so), super::spec::special_authority_ignore_slashes_state(super::machine::ctx_of(input@, base, so), old(m)@), old(m)@, final(m)@, flow),
{
    let c = c_at_exec(input, m.pointer);
    if c != Some(0x2Fu32) && c != Some(0x5Cu32) {
        m.state = State::Authority;
        back()
    } else {
        advance(m, input.len())
    }
}

/// Authority state step 1.4, "For each codePoint in buffer", appending to
/// url's username and password.
fn authority_code_points_exec(buffer: &[u32], url: &mut ParsedUrl, password_token_seen: bool) -> (pts: bool)
    requires
        clazel_encoding::utf8::spec::all_scalar_values(buffer@),
    ensures
        (final(url)@, pts) == authority_code_points(buffer@, 0, old(url)@, password_token_seen),
{
    let ghost target = authority_code_points(buffer@, 0, url@, password_token_seen);
    let mut pts = password_token_seen;
    let mut i: usize = 0;
    while i < buffer.len()
        invariant
            i <= buffer.len(),
            clazel_encoding::utf8::spec::all_scalar_values(buffer@),
            target == authority_code_points(buffer@, i as nat, url@, pts),
        decreases buffer.len() - i,
    {
        let code_point = at32(buffer, i);
        if code_point == 0x3A && !pts {
            // 1.4.1
            pts = true;
        } else {
            // 1.4.2
            let encoded = clazel_percent::encode::utf8_percent_encode_code_point(
                code_point,
                clazel_percent::spec::PercentEncodeSet::Userinfo,
            );
            if pts {
                // 1.4.3
                append(&mut url.password, encoded.as_slice());
            } else {
                // 1.4.4
                append(&mut url.username, encoded.as_slice());
            }
        }
        // Never saturates: i is below a length.
        i = i.saturating_add(1);
    }
    pts
}

/// "authority state"
pub fn authority_state(input: &[u32], Ghost(base): Ghost<Option<Url>>, Ghost(so): Ghost<Option<State>>, m: &mut ExecMachine) -> (flow: Flow)
    requires
        super::machine::wf(super::machine::ctx_of(input@, base, so), old(m)@),
        old(m).state is Authority,
    ensures
        super::machine::flow_ok(super::machine::ctx_of(input@, base, so), super::spec::authority_state(super::machine::ctx_of(input@, base, so), old(m)@), old(m)@, final(m)@, flow),
{
    let c = c_at_exec(input, m.pointer);
    let special = is_special_scheme_exec(m.url.scheme.as_slice());
    if c == Some(0x40u32) {
        // 1.2
        let buffer = if m.at_sign_seen {
            let mut b: Vec<u32> = Vec::new();
            b.push(0x25);
            b.push(0x34);
            b.push(0x30);
            append(&mut b, m.buffer.as_slice());
            assert(b@ =~= seq![0x25u32, 0x34, 0x30] + m.buffer@);
            b
        } else {
            copy(m.buffer.as_slice())
        };
        assert(clazel_encoding::utf8::spec::all_scalar_values(buffer@)) by {
            assert forall|k: int| 0 <= k < buffer@.len() implies clazel_encoding::utf8::spec::is_scalar_value(
                #[trigger] buffer@[k],
            ) by {
                if m.at_sign_seen && k >= 3 {
                    assert(buffer@[k] == m.buffer@[k - 3]);
                }
            }
        }
        // 1.4
        let pts = authority_code_points_exec(buffer.as_slice(), &mut m.url, m.password_token_seen);
        // 1.3, 1.5
        m.at_sign_seen = true;
        m.password_token_seen = pts;
        m.buffer = Vec::new();
        assert(m.buffer@ =~= seq![]);
        advance(m, input.len())
    } else if ends_authority_exec(c, special) {
        if m.at_sign_seen && m.buffer.is_empty() {
            // 2.1
            Flow::Failure
        } else {
            // 2.2: the next run is at pointer − buffer's length.
            let length = m.buffer.len();
            m.buffer = Vec::new();
            assert(m.buffer@ =~= seq![]);
            m.state = State::Host;
            // Never saturates: wf says buffer is no longer than pointer.
            m.pointer = m.pointer.saturating_sub(length);
            Flow::Next
        }
    } else {
        // 3.
        if let Some(c) = c {
            m.buffer.push(c);
        }
        advance(m, input.len())
    }
}

/// "host state" (no state override, so not the hostname state)
pub fn host_state(input: &[u32], Ghost(base): Ghost<Option<Url>>, so: &Option<State>, m: &mut ExecMachine) -> (flow: Flow)
    requires
        super::machine::wf(super::machine::ctx_of(input@, base, *so), old(m)@),
        old(m).state is Host || old(m).state is Hostname,
    ensures
        super::machine::flow_ok(super::machine::ctx_of(input@, base, *so), super::spec::host_state(super::machine::ctx_of(input@, base, *so), old(m)@), old(m)@, final(m)@, flow),
{
    let c = c_at_exec(input, m.pointer);
    let special = is_special_scheme_exec(m.url.scheme.as_slice());
    if so.is_some() && is_file(m.url.scheme.as_slice()) {
        // 1.
        m.state = State::FileHost;
        back()
    } else if c == Some(0x3Au32) && !m.inside_brackets {
        if m.buffer.is_empty() {
            // 2.1
            return Flow::Failure;
        }
        if super::machine::is_hostname_override(so) {
            // 2.2
            return Flow::Failure;
        }
        // 2.3
        match crate::host::parse::host_parser_full(m.buffer.as_slice(), !special) {
            // 2.4
            None => Flow::Failure,
            Some(h) => {
                // 2.5
                m.url.host = Some(h);
                m.buffer = Vec::new();
                assert(m.buffer@ =~= seq![]);
                m.state = State::Port;
                advance(m, input.len())
            },
        }
    } else if ends_authority_exec(c, special) {
        if special && m.buffer.is_empty() {
            // 3.1
            return Flow::Failure;
        }
        if so.is_some() && m.buffer.is_empty() && (!m.url.username.is_empty() || !m.url.password.is_empty()
            || m.url.port.is_some()) {
            // 3.2
            return Flow::Failure;
        }
        // 3.3
        match crate::host::parse::host_parser_full(m.buffer.as_slice(), !special) {
            // 3.4
            None => Flow::Failure,
            Some(h) => {
                // 3.5
                m.url.host = Some(h);
                if so.is_some() {
                    // 3.6
                    return Flow::Return;
                }
                m.buffer = Vec::new();
                assert(m.buffer@ =~= seq![]);
                m.state = State::PathStart;
                back()
            },
        }
    } else {
        // 4.
        if c == Some(0x5Bu32) {
            m.inside_brackets = true;
        } else if c == Some(0x5Du32) {
            m.inside_brackets = false;
        }
        if let Some(c) = c {
            m.buffer.push(c);
        }
        advance(m, input.len())
    }
}

/// `decimal_value` of a prefix is at most that of the whole (for digits).
proof fn lemma_decimal_value_prefix(s: Seq<u32>, i: int)
    requires
        0 <= i <= s.len(),
        super::machine::all_ascii_digits(s),
    ensures
        decimal_value(s.subrange(0, i)) <= decimal_value(s),
    decreases s.len(),
{
    if i < s.len() {
        let t = s.drop_last();
        assert(super::machine::all_ascii_digits(t)) by {
            assert forall|k: int| 0 <= k < t.len() implies crate::host::spec::is_ascii_digit(#[trigger] t[k]) by {
                assert(t[k] == s[k]);
            }
        }
        assert(s.subrange(0, i) =~= t.subrange(0, i));
        lemma_decimal_value_prefix(t, i);
        assert(crate::host::spec::is_ascii_digit(s[s.len() - 1]));
        assert(decimal_value(t) <= decimal_value(t) * 10) by (nonlinear_arith);
    } else {
        assert(s.subrange(0, i) =~= s);
    }
}

/// Port state step 2.1.1 and 2.1.2: the port buffer represents, or
/// `None` if that is not a 16-bit unsigned integer.
fn port_value(buffer: &[u32]) -> (r: Option<u16>)
    requires
        super::machine::all_ascii_digits(buffer@),
    ensures
        match r {
            Some(p) => decimal_value(buffer@) == p as nat,
            None => decimal_value(buffer@) > 0xFFFF,
        },
{
    let mut v: u32 = 0;
    let mut i: usize = 0;
    assert(buffer@.subrange(0, 0) =~= seq![]);
    while i < buffer.len()
        invariant
            i <= buffer.len(),
            super::machine::all_ascii_digits(buffer@),
            v as nat == decimal_value(buffer@.subrange(0, i as int)),
            v <= 0xFFFF,
        decreases buffer.len() - i,
    {
        let d = at32(buffer, i);
        assert(crate::host::spec::is_ascii_digit(buffer@[i as int]));
        // Never saturates: v <= 0xFFFF and d is an ASCII digit.
        let next = v.saturating_mul(10).saturating_add(d.saturating_sub(0x30));
        assert(buffer@.subrange(0, i + 1).drop_last() =~= buffer@.subrange(0, i as int));
        assert(next as nat == decimal_value(buffer@.subrange(0, i + 1)));
        // Never saturates: i is below a length.
        i = i.saturating_add(1);
        if next > 0xFFFF {
            proof {
                lemma_decimal_value_prefix(buffer@, i as int);
            }
            return None;
        }
        v = next;
    }
    assert(buffer@.subrange(0, buffer@.len() as int) =~= buffer@);
    Some(v as u16)
}

/// "port state" (no state override)
pub fn port_state(input: &[u32], Ghost(base): Ghost<Option<Url>>, so: &Option<State>, m: &mut ExecMachine) -> (flow: Flow)
    requires
        super::machine::wf(super::machine::ctx_of(input@, base, *so), old(m)@),
        old(m).state is Port,
    ensures
        super::machine::flow_ok(super::machine::ctx_of(input@, base, *so), super::spec::port_state(super::machine::ctx_of(input@, base, *so), old(m)@), old(m)@, final(m)@, flow),
{
    let c = c_at_exec(input, m.pointer);
    let special = is_special_scheme_exec(m.url.scheme.as_slice());
    match c {
        Some(d) if (0x30..=0x39).contains(&d) => {
            // 1.
            m.buffer.push(d);
            return advance(m, input.len());
        },
        _ => {},
    }
    if ends_authority_exec(c, special) || so.is_some() {
        if !m.buffer.is_empty() {
            // 2.1.1, 2.1.2
            match port_value(m.buffer.as_slice()) {
                None => Flow::Failure,
                Some(port) => {
                    // 2.1.3
                    let default = default_port_exec(m.url.scheme.as_slice());
                    let is_default = match default {
                        Some(d) => d == port,
                        None => false,
                    };
                    if is_default {
                        m.url.port = None;
                    } else {
                        m.url.port = Some(port);
                    }
                    if so.is_some() {
                        // 2.1.5
                        return Flow::Return;
                    }
                    // 2.1.4
                    m.buffer = Vec::new();
                    assert(m.buffer@ =~= seq![]);
                    // 2.3
                    m.state = State::PathStart;
                    back()
                },
            }
        } else if so.is_some() {
            // 2.2
            Flow::Failure
        } else {
            // 2.3
            m.state = State::PathStart;
            back()
        }
    } else {
        // 3.
        Flow::Failure
    }
}

/// "file state"
pub fn file_state(input: &[u32], base: Option<&ParsedUrl>, Ghost(so): Ghost<Option<State>>, m: &mut ExecMachine) -> (flow: Flow)
    requires
        super::machine::wf(super::machine::ctx_of(input@, super::record::opt_ref_url_view(base), so), old(m)@),
        old(m).state is File,
    ensures
        super::machine::flow_ok(super::machine::ctx_of(input@, super::record::opt_ref_url_view(base), so), super::spec::file_state(super::machine::ctx_of(input@, super::record::opt_ref_url_view(base), so), old(m)@), old(m)@, final(m)@, flow),
{
    // 1., 2.
    m.url.scheme = file_vec();
    m.url.host = Some(ParsedHost::Empty);
    let c = c_at_exec(input, m.pointer);
    if c == Some(0x2Fu32) || c == Some(0x5Cu32) {
        // 3.
        m.state = State::FileSlash;
        return advance(m, input.len());
    }
    match base {
        Some(b) if is_file(b.scheme.as_slice()) => {
        // 4.1
        m.url.host = clone_opt_host(&b.host);
        m.url.path = clone_path(&b.path);
        m.url.query = clone_opt_str(&b.query);
        if c == Some(0x3Fu32) {
            // 4.2
            m.url.query = Some(Vec::new());
            assert(crate::host::record::opt_seq(m.url.query) == Some(Seq::<u32>::empty()));
            m.state = State::Query;
            return advance(m, input.len());
        } else if c == Some(0x23u32) {
            // 4.3
            m.url.fragment = Some(Vec::new());
            assert(crate::host::record::opt_seq(m.url.fragment) == Some(Seq::<u32>::empty()));
            m.state = State::Fragment;
            return advance(m, input.len());
        } else if c.is_some() {
            // 4.4.1
            m.url.query = None;
            if !starts_with_windows_drive_letter_at(input, m.pointer) {
                // 4.4.2
                shorten_exec(&mut m.url);
            } else {
                // 4.4.3
                m.url.path = ParsedPath::List(Vec::new());
                assert(super::record::segments_view(Seq::<Vec<u32>>::empty()) =~= Seq::<Seq<u32>>::empty());
            }
            // 4.4.4
            m.state = State::Path;
            return back();
        } else {
            return advance(m, input.len());
        }
        },
        _ => {},
    }
    // 5.
    m.state = State::Path;
    back()
}

/// A copy of `path`[0], if `path` is a list whose first segment is a
/// normalized Windows drive letter (file slash state step 2.1.2).
fn first_normalized_windows_drive_letter(path: &ParsedPath) -> (r: Option<Vec<u32>>)
    ensures
        match r {
            Some(s) => path@ matches UrlPath::List(p) && p.len() > 0 && is_normalized_windows_drive_letter(p[0]) && s@ == p[0],
            None => !(path@ matches UrlPath::List(p) && p.len() > 0 && is_normalized_windows_drive_letter(p[0])),
        },
{
    let ParsedPath::List(l) = path else {
        return None;
    };
    let first = super::record::segment(l.as_slice(), 0)?;
    assert(super::record::segments_view(l@).len() == l@.len());
    if !l.is_empty() {
        assert(super::record::segments_view(l@)[0] == l@[0]@);
    }
    if is_normalized_windows_drive_letter_exec(first.as_slice()) {
        Some(copy(first.as_slice()))
    } else {
        None
    }
}

/// "file slash state"
pub fn file_slash_state(input: &[u32], base: Option<&ParsedUrl>, Ghost(so): Ghost<Option<State>>, m: &mut ExecMachine) -> (flow: Flow)
    requires
        super::machine::wf(super::machine::ctx_of(input@, super::record::opt_ref_url_view(base), so), old(m)@),
        old(m).state is FileSlash,
    ensures
        super::machine::flow_ok(super::machine::ctx_of(input@, super::record::opt_ref_url_view(base), so), super::spec::file_slash_state(super::machine::ctx_of(input@, super::record::opt_ref_url_view(base), so), old(m)@), old(m)@, final(m)@, flow),
{
    let c = c_at_exec(input, m.pointer);
    if c == Some(0x2Fu32) || c == Some(0x5Cu32) {
        // 1.
        m.state = State::FileHost;
        return advance(m, input.len());
    }
    // 2.1
    match base {
        Some(b) if is_file(b.scheme.as_slice()) => {
            // 2.1.1
            m.url.host = clone_opt_host(&b.host);
            // 2.1.2
            let first = if !starts_with_windows_drive_letter_at(input, m.pointer) {
                first_normalized_windows_drive_letter(&b.path)
            } else {
                None
            };
            if let Some(first) = first {
                path_append_exec(&mut m.url.path, first);
            }
        },
        _ => {},
    }
    // 2.2
    m.state = State::Path;
    back()
}

/// "file host state" (no state override)
pub fn file_host_state(input: &[u32], Ghost(base): Ghost<Option<Url>>, so: &Option<State>, m: &mut ExecMachine) -> (flow: Flow)
    requires
        super::machine::wf(super::machine::ctx_of(input@, base, *so), old(m)@),
        old(m).state is FileHost,
    ensures
        super::machine::flow_ok(super::machine::ctx_of(input@, base, *so), super::spec::file_host_state(super::machine::ctx_of(input@, base, *so), old(m)@), old(m)@, final(m)@, flow),
{
    let c = c_at_exec(input, m.pointer);
    if c.is_none() || c == Some(0x2Fu32) || c == Some(0x5Cu32) || c == Some(0x3Fu32) || c == Some(0x23u32) {
        if so.is_none() && is_windows_drive_letter_exec(m.buffer.as_slice()) {
            // 1.1
            m.state = State::Path;
            back()
        } else if m.buffer.is_empty() {
            // 1.2.1
            m.url.host = Some(ParsedHost::Empty);
            if so.is_some() {
                // 1.2.2
                return Flow::Return;
            }
            // 1.2.3
            m.state = State::PathStart;
            back()
        } else {
            // 1.3.1
            let special = is_special_scheme_exec(m.url.scheme.as_slice());
            match crate::host::parse::host_parser_full(m.buffer.as_slice(), !special) {
                // 1.3.2
                None => Flow::Failure,
                Some(h) => {
                    // 1.3.3
                    let h = match h {
                        ParsedHost::Domain(d) => if is_localhost(d.as_slice()) {
                            ParsedHost::Empty
                        } else {
                            ParsedHost::Domain(d)
                        },
                        other => other,
                    };
                    // 1.3.4
                    m.url.host = Some(h);
                    if so.is_some() {
                        // 1.3.5
                        return Flow::Return;
                    }
                    // 1.3.6
                    m.buffer = Vec::new();
                    assert(m.buffer@ =~= seq![]);
                    m.state = State::PathStart;
                    back()
                },
            }
        }
    } else {
        // 2.
        if let Some(c) = c {
            m.buffer.push(c);
        }
        advance(m, input.len())
    }
}

} // verus!
