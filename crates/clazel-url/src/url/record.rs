//! The executable URL record (URL §4.1), and the string helpers the URL
//! parser and serializer share. Each helper is proven equal to its spec
//! definition.

#[allow(unused_imports)]
use super::spec::*;
use crate::host::record::{ParsedHost, append, at32, copy};
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// A URL path (URL §4.1), viewed as [`UrlPath`].
pub enum ParsedPath {
    /// An opaque path (a URL path segment).
    Opaque(Vec<u32>),
    /// A list of URL path segments.
    List(Vec<Vec<u32>>),
}

/// The spec view of a list of strings.
pub open spec fn segments_view(v: Seq<Vec<u32>>) -> Seq<Seq<u32>> {
    v.map_values(|s: Vec<u32>| s@)
}

impl View for ParsedPath {
    type V = UrlPath;

    open spec fn view(&self) -> UrlPath {
        match self {
            ParsedPath::Opaque(s) => UrlPath::Opaque(s@),
            ParsedPath::List(l) => UrlPath::List(segments_view(l@)),
        }
    }
}

/// A URL (URL §4.1), viewed as [`Url`]. Strings are code points as `u32`.
pub struct ParsedUrl {
    /// scheme
    pub scheme: Vec<u32>,
    /// username
    pub username: Vec<u32>,
    /// password
    pub password: Vec<u32>,
    /// host (`None` is null)
    pub host: Option<ParsedHost>,
    /// port (`None` is null)
    pub port: Option<u16>,
    /// path
    pub path: ParsedPath,
    /// query (`None` is null)
    pub query: Option<Vec<u32>>,
    /// fragment (`None` is null)
    pub fragment: Option<Vec<u32>>,
}

/// The view of an optional port.
pub open spec fn port_view(p: Option<u16>) -> Option<nat> {
    match p {
        Some(p) => Some(p as nat),
        None => None,
    }
}

impl View for ParsedUrl {
    type V = Url;

    open spec fn view(&self) -> Url {
        Url {
            scheme: self.scheme@,
            username: self.username@,
            password: self.password@,
            host: crate::host::record::option_view(self.host),
            port: port_view(self.port),
            path: self.path@,
            query: crate::host::record::opt_seq(self.query),
            fragment: crate::host::record::opt_seq(self.fragment),
        }
    }
}

/// The view of an optional URL; `None` is failure (or null).
pub open spec fn opt_url_view(u: Option<ParsedUrl>) -> Option<Url> {
    match u {
        Some(u) => Some(u@),
        None => None,
    }
}

/// The view of an optional borrowed URL.
pub open spec fn opt_ref_url_view(u: Option<&ParsedUrl>) -> Option<Url> {
    match u {
        Some(u) => Some(u@),
        None => None,
    }
}

/// A new URL (URL §4.1).
pub fn new_url_exec() -> (out: ParsedUrl)
    ensures
        out@ == new_url(),
{
    let out = ParsedUrl {
        scheme: Vec::new(),
        username: Vec::new(),
        password: Vec::new(),
        host: None,
        port: None,
        path: ParsedPath::List(Vec::new()),
        query: None,
        fragment: None,
    };
    assert(segments_view(Seq::<Vec<u32>>::empty()) =~= Seq::<Seq<u32>>::empty());
    assert(out@.scheme =~= seq![]);
    out
}

/// A copy of a host.
pub fn clone_host(h: &ParsedHost) -> (out: ParsedHost)
    ensures
        out@ == h@,
{
    match h {
        ParsedHost::Domain(s) => ParsedHost::Domain(copy(s.as_slice())),
        ParsedHost::Ipv4(a) => ParsedHost::Ipv4(*a),
        ParsedHost::Ipv6(a) => ParsedHost::Ipv6(*a),
        ParsedHost::Opaque(s) => ParsedHost::Opaque(copy(s.as_slice())),
        ParsedHost::Empty => ParsedHost::Empty,
    }
}

/// A copy of an optional host.
pub fn clone_opt_host(h: &Option<ParsedHost>) -> (out: Option<ParsedHost>)
    ensures
        crate::host::record::option_view(out) == crate::host::record::option_view(*h),
{
    let Some(h) = h else {
        return None;
    };
    Some(clone_host(h))
}

/// A copy of an optional string.
pub fn clone_opt_str(s: &Option<Vec<u32>>) -> (out: Option<Vec<u32>>)
    ensures
        crate::host::record::opt_seq(out) == crate::host::record::opt_seq(*s),
{
    let Some(s) = s else {
        return None;
    };
    Some(copy(s.as_slice()))
}

/// Segment `i` of `l`, if there is one.
pub fn segment(l: &[Vec<u32>], i: usize) -> (r: Option<&Vec<u32>>)
    ensures
        i < l@.len() ==> (r matches Some(s) && *s == l@[i as int]),
        i >= l@.len() ==> r is None,
{
    l.get(i)
}

/// A copy of a list of segments ("a clone of base's path").
pub fn clone_segments(l: &[Vec<u32>]) -> (out: Vec<Vec<u32>>)
    ensures
        segments_view(out@) == segments_view(l@),
{
    let mut out: Vec<Vec<u32>> = Vec::new();
    let mut i: usize = 0;
    while i < l.len()
        invariant
            i <= l.len(),
            segments_view(out@) =~= segments_view(l@).subrange(0, i as int),
        decreases l.len() - i,
    {
        let ghost before = out@;
        let Some(t) = l.get(i) else {
            return out;
        };
        let s = copy(t.as_slice());
        out.push(s);
        assert(out@ == before.push(s));
        assert(segments_view(before).len() == before.len());
        assert(before.len() == i);
        assert forall|k: int| 0 <= k < out@.len() implies #[trigger] segments_view(out@)[k] == segments_view(l@).subrange(0, i + 1)[k] by {
            if k < i {
                assert(segments_view(before)[k] == segments_view(l@).subrange(0, i as int)[k]);
                assert(out@[k] == before[k]);
            } else {
                assert(out@[k] == s);
                assert(segments_view(l@)[k] == l@[k]@);
            }
        }
        // Never saturates: i is below a length.
        i = i.saturating_add(1);
        assert(segments_view(out@) =~= segments_view(l@).subrange(0, i as int));
    }
    assert(segments_view(l@).subrange(0, l@.len() as int) =~= segments_view(l@));
    out
}

/// A copy of a path.
pub fn clone_path(p: &ParsedPath) -> (out: ParsedPath)
    ensures
        out@ == p@,
{
    match p {
        ParsedPath::Opaque(s) => ParsedPath::Opaque(copy(s.as_slice())),
        ParsedPath::List(l) => ParsedPath::List(clone_segments(l)),
    }
}

/// A copy of a URL.
pub fn clone_url(u: &ParsedUrl) -> (out: ParsedUrl)
    ensures
        out@ == u@,
{
    ParsedUrl {
        scheme: copy(u.scheme.as_slice()),
        username: copy(u.username.as_slice()),
        password: copy(u.password.as_slice()),
        host: clone_opt_host(&u.host),
        port: u.port,
        path: clone_path(&u.path),
        query: clone_opt_str(&u.query),
        fragment: clone_opt_str(&u.fragment),
    }
}

/// Whether two strings are equal.
pub fn eq_str(a: &[u32], b: &[u32]) -> (r: bool)
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
            a@.subrange(0, i as int) =~= b@.subrange(0, i as int),
        decreases a.len() - i,
    {
        if at32(a, i) != at32(b, i) {
            return false;
        }
        // Never saturates: i is below a length.
        i = i.saturating_add(1);
        assert(a@.subrange(0, i as int) =~= b@.subrange(0, i as int));
    }
    assert(a@ =~= a@.subrange(0, a@.len() as int));
    assert(b@ =~= b@.subrange(0, b@.len() as int));
    true
}

/// Whether `s` is "`file`".
pub fn is_file(s: &[u32]) -> (r: bool)
    ensures
        r == (s@ == file_str()),
{
    let r = s.len() == 4 && at32(s, 0) == 0x66 && at32(s, 1) == 0x69 && at32(s, 2) == 0x6C && at32(s, 3) == 0x65;
    if r {
        assert(s@ =~= file_str());
    }
    r
}

/// The special scheme `s` is, if any: 0 ftp, 1 file, 2 http, 3 https, 4
/// ws, 5 wss.
fn special_index(s: &[u32]) -> (r: Option<u8>)
    ensures
        r == Some(0u8) <==> s@ == ftp_str(),
        r == Some(1u8) <==> s@ == file_str(),
        r == Some(2u8) <==> s@ == http_str(),
        r == Some(3u8) <==> s@ == https_str(),
        r == Some(4u8) <==> s@ == ws_str(),
        r == Some(5u8) <==> s@ == wss_str(),
        r is None <==> !is_special_scheme(s@),
        r matches Some(i) ==> i <= 5,
{
    let n = s.len();
    let r = if n == 2 && at32(s, 0) == 0x77 && at32(s, 1) == 0x73 {
        assert(s@ =~= ws_str());
        Some(4u8)
    } else if n == 3 && at32(s, 0) == 0x66 && at32(s, 1) == 0x74 && at32(s, 2) == 0x70 {
        assert(s@ =~= ftp_str());
        Some(0u8)
    } else if n == 3 && at32(s, 0) == 0x77 && at32(s, 1) == 0x73 && at32(s, 2) == 0x73 {
        assert(s@ =~= wss_str());
        Some(5u8)
    } else if is_file(s) {
        Some(1u8)
    } else if n == 4 && at32(s, 0) == 0x68 && at32(s, 1) == 0x74 && at32(s, 2) == 0x74 && at32(s, 3) == 0x70 {
        assert(s@ =~= http_str());
        Some(2u8)
    } else if n == 5 && at32(s, 0) == 0x68 && at32(s, 1) == 0x74 && at32(s, 2) == 0x74 && at32(s, 3) == 0x70
        && at32(s, 4) == 0x73 {
        assert(s@ =~= https_str());
        Some(3u8)
    } else {
        None
    };
    // The six strings are pairwise different (by length or a code point).
    assert(ftp_str() != file_str() && ftp_str() != http_str() && ftp_str() != https_str() && ftp_str() != ws_str()
        && ftp_str() != wss_str()) by {
        assert(ftp_str().len() != file_str().len());
        assert(ftp_str().len() != http_str().len());
        assert(ftp_str().len() != https_str().len());
        assert(ftp_str().len() != ws_str().len());
        assert(ftp_str()[0] != wss_str()[0]);
    }
    assert(file_str() != http_str() && file_str() != https_str() && file_str() != ws_str() && file_str() != wss_str())
        by {
        assert(file_str()[0] != http_str()[0]);
        assert(file_str().len() != https_str().len());
        assert(file_str().len() != ws_str().len());
        assert(file_str().len() != wss_str().len());
    }
    assert(http_str() != https_str() && http_str() != ws_str() && http_str() != wss_str()) by {
        assert(http_str().len() != https_str().len());
        assert(http_str().len() != ws_str().len());
        assert(http_str().len() != wss_str().len());
    }
    assert(https_str() != ws_str() && https_str() != wss_str() && ws_str() != wss_str()) by {
        assert(https_str().len() != ws_str().len());
        assert(https_str().len() != wss_str().len());
        assert(ws_str().len() != wss_str().len());
    }
    proof {
        if r is None {
            if s@ == ftp_str() || s@ == wss_str() || s@ == ws_str() || s@ == http_str() || s@ == https_str() {
                assert(s@[0] == s@[0]);
                assert(s@.len() >= 2 ==> s@[1] == s@[1]);
                assert(s@.len() >= 3 ==> s@[2] == s@[2]);
            }
        }
    }
    r
}

/// Whether `s` is a special scheme (URL §4.2).
pub fn is_special_scheme_exec(s: &[u32]) -> (r: bool)
    ensures
        r == is_special_scheme(s@),
{
    special_index(s).is_some()
}

/// The default port of `s` (URL §4.2).
pub fn default_port_exec(s: &[u32]) -> (r: Option<u16>)
    ensures
        port_view(r) == default_port(s@),
{
    match special_index(s) {
        Some(0) => Some(21),
        Some(2) => Some(80),
        Some(3) => Some(443),
        Some(4) => Some(80),
        Some(5) => Some(443),
        _ => None,
    }
}

/// `s` with `t` appended.
pub fn concat(s: &[u32], t: &[u32]) -> (out: Vec<u32>)
    ensures
        out@ == s@ + t@,
{
    let mut out = copy(s);
    append(&mut out, t);
    out
}

} // verus!
