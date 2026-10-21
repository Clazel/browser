//! A second transcription of what the URL API setters accept and store,
//! from a different standard: the component grammar of RFC 3986, and
//! theorems that the setters (`spec.rs`) store a component exactly as
//! RFC 3986 reads it, on a precisely stated class of URLs and values.
//!
//! Source (pinned): RFC 3986, "Uniform Resource Identifier (URI): Generic
//! Syntax", January 2005, <https://www.rfc-editor.org/rfc/rfc3986>:
//! §2.1 (pct-encoded), §2.2 (sub-delims), §2.3 (unreserved), §3.1
//! (scheme), §3.2.1 (userinfo), §3.2.2 (reg-name), §3.2.3 (port), §3.3
//! (path-abempty), §3.4 (query), §3.5 (fragment), §6.2.2.1 (case
//! normalization of the scheme). The core rules (ALPHA, DIGIT, HEXDIG; RFC
//! 2234 via RFC 3986 §1.3) and `reg-name` are the ones item 1.9
//! transcribed in [`crate::host::independent`]. The definitions above the
//! theorems were written from the RFC, by the author of `spec.rs`
//! (independent in source, not authorship).
//!
//! What each setter is checked against, and on which class (the URL
//! Standard deliberately differs from RFC 3986 elsewhere, e.g. it
//! percent-encodes what the RFC forbids instead of failing):
//! - `protocol`: a value that is an RFC `scheme` becomes the scheme, in
//!   lowercase (§6.2.2.1), for a URL with a null port whose specialness
//!   the new scheme keeps, not switching to "file" with credentials, and
//!   not a "file" URL with an empty host.
//! - `username`, `password`: a value that is RFC `userinfo` without ":",
//!   ";" or "=" (which the URL Standard percent-encodes; ":" is also
//!   RFC's deprecated user:password delimiter) is stored as it is, for a
//!   URL that can have one.
//! - `host`, `hostname`: a non-empty RFC `reg-name` becomes an opaque host
//!   as it is, for a URL that is not special, not "file", and has no
//!   opaque path. (Special URLs run the domain parser, UTS #46, which
//!   RFC 3986 does not define.)
//! - `port`: a non-empty RFC `port` (`*DIGIT`) whose decimal value fits in
//!   16 bits becomes the port, or null if it is the scheme's default port
//!   (RFC 3986 §6.2.3 leaves defaults to each scheme; they are the URL
//!   Standard's table), for a URL that can have one.
//! - `pathname`: a `path-abempty` of one or more segments becomes the
//!   path, segment by segment, for a URL that is not "file" and has no
//!   opaque path, when no segment is a dot-segment or holds a
//!   `pct-encoded` (the URL Standard also reads "%2e" as "."; RFC 3986
//!   §6.2.2.2 normalizes it to "." too, but as a separate step).
//! - `search`: "?" followed by an RFC `query` becomes the query as it is
//!   (without "'" for a special URL, whose query set encodes it).
//! - `hash`: "#" followed by an RFC `fragment` becomes the fragment as it
//!   is.
//! - `href` is the basic URL parser, checked against RFC 3986 in
//!   `url/independent.rs`; nothing here.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// =====================================================================
// RFC 3986 transcription.
// =====================================================================

/// `unreserved = ALPHA / DIGIT / "-" / "." / "_" / "~"` (§2.3).
pub open spec fn is_unreserved(c: u32) -> bool {
    crate::host::independent::is_alpha(c) || crate::host::independent::is_digit(c) || c == 0x2D || c == 0x2E
        || c == 0x5F || c == 0x7E
}

/// `sub-delims = "!" / "$" / "&" / "'" / "(" / ")" / "*" / "+" / "," / ";"
/// / "="` (§2.2).
pub open spec fn is_sub_delim(c: u32) -> bool {
    c == 0x21 || c == 0x24 || c == 0x26 || c == 0x27 || c == 0x28 || c == 0x29 || c == 0x2A || c == 0x2B
        || c == 0x2C || c == 0x3B || c == 0x3D
}

/// `scheme = ALPHA *( ALPHA / DIGIT / "+" / "-" / "." )` (§3.1).
pub open spec fn is_scheme(s: Seq<u32>) -> bool {
    s.len() > 0 && crate::host::independent::is_alpha(s[0]) && forall|k: int| 1 <= k < s.len() ==> (
    crate::host::independent::is_alpha(#[trigger] s[k]) || crate::host::independent::is_digit(s[k]) || s[k]
        == 0x2B || s[k] == 0x2D || s[k] == 0x2E)
}

/// §6.2.2.1: the scheme "should be normalized to lowercase": every
/// uppercase ALPHA (%x41-5A) becomes its lowercase letter (%x61-7A).
pub open spec fn to_lower(c: u32) -> u32 {
    if 0x41 <= c <= 0x5A {
        (c + 0x20) as u32
    } else {
        c
    }
}

/// [`to_lower`] on each code point.
pub open spec fn lower(s: Seq<u32>) -> Seq<u32> {
    s.map_values(|c: u32| to_lower(c))
}

/// A `pct-encoded = "%" HEXDIG HEXDIG` at `i` (§2.1).
pub open spec fn pct_encoded_at(s: Seq<u32>, i: nat) -> bool {
    s[i as int] == 0x25 && i + 2 < s.len() && crate::host::independent::is_hexdig(s[i + 1int])
        && crate::host::independent::is_hexdig(s[i + 2int])
}

/// `userinfo = *( unreserved / pct-encoded / sub-delims / ":" )` (§3.2.1),
/// matched from `i` to the end.
pub open spec fn userinfo_from(s: Seq<u32>, i: nat) -> bool
    decreases s.len() - i
{
    if i >= s.len() {
        true
    } else if is_unreserved(s[i as int]) || is_sub_delim(s[i as int]) || s[i as int] == 0x3A {
        userinfo_from(s, i + 1)
    } else {
        pct_encoded_at(s, i) && userinfo_from(s, i + 3)
    }
}

/// `port = *DIGIT` (§3.2.3).
pub open spec fn is_port(s: Seq<u32>) -> bool {
    forall|k: int| 0 <= k < s.len() ==> crate::host::independent::is_digit(#[trigger] s[k])
}

/// "The port subcomponent of authority is designated by an optional port
/// number in decimal" (§3.2.3): the value of a `*DIGIT`, read from the
/// first digit on, `acc` being the value of the digits before `i`.
pub open spec fn decimal_from(s: Seq<u32>, i: nat, acc: nat) -> nat
    decreases s.len() - i
{
    if i >= s.len() {
        acc
    } else {
        decimal_from(s, i + 1, acc * 10 + crate::host::independent::digit_value(s[i as int]))
    }
}

/// `pchar = unreserved / pct-encoded / sub-delims / ":" / "@"` (§3.3),
/// and `query = *( pchar / "/" / "?" )` (§3.4), which is also `fragment`
/// (§3.5), matched from `i` to the end.
pub open spec fn query_from(s: Seq<u32>, i: nat) -> bool
    decreases s.len() - i
{
    if i >= s.len() {
        true
    } else if is_unreserved(s[i as int]) || is_sub_delim(s[i as int]) || s[i as int] == 0x3A || s[i as int]
        == 0x40 || s[i as int] == 0x2F || s[i as int] == 0x3F {
        query_from(s, i + 1)
    } else {
        pct_encoded_at(s, i) && query_from(s, i + 3)
    }
}

/// `pchar` other than `pct-encoded` (§3.3): unreserved, sub-delims, ":"
/// or "@".
pub open spec fn is_pchar_code_point(c: u32) -> bool {
    is_unreserved(c) || is_sub_delim(c) || c == 0x3A || c == 0x40
}

/// `segment = *pchar` (§3.3), with no `pct-encoded`.
pub open spec fn is_plain_segment(s: Seq<u32>) -> bool {
    forall|k: int| 0 <= k < s.len() ==> is_pchar_code_point(#[trigger] s[k])
}

/// "The path segments "." and "..", also known as dot-segments" (§3.3).
pub open spec fn is_dot_segment(s: Seq<u32>) -> bool {
    s == seq![0x2Eu32] || s == seq![0x2Eu32, 0x2E]
}

/// `path-abempty = *( "/" segment )` (§3.3): the path made of `segs`, each
/// preceded by "/".
pub open spec fn path_abempty(segs: Seq<Seq<u32>>) -> Seq<u32>
    decreases segs.len()
{
    if segs.len() == 0 {
        seq![]
    } else {
        seq![0x2Fu32] + segs[0] + path_abempty(segs.subrange(1, segs.len() as int))
    }
}

// =====================================================================
// Theorems: what the RFC transcription and the setters are proven to
// agree on. Everything above was written from RFC 3986; everything
// below relates it to `spec.rs`.
// =====================================================================

/// No ASCII tab or newline: basic URL parser step 3 leaves `s` alone.
proof fn lemma_no_tab_or_newline(s: Seq<u32>)
    requires
        forall|k: int| 0 <= k < s.len() ==> 0x21 <= #[trigger] s[k] <= 0x7E,
    ensures
        crate::url::spec::remove_ascii_tab_or_newline(s) == s,
    decreases s.len()
{
    if s.len() > 0 {
        lemma_no_tab_or_newline(s.drop_last());
        assert(s.drop_last().push(s.last()) =~= s);
    }
}

// ---------------------------------------------------------------------
// protocol
// ---------------------------------------------------------------------

/// The scheme state reads an RFC scheme's code points into buffer,
/// lowercased, up to the ":" after it.
proof fn lemma_scheme_buffer(v: Seq<u32>, i: nat)
    requires
        is_scheme(v),
        1 <= i <= v.len(),
    ensures
        super::lemmas::scheme_buffer(v.push(0x3Au32), i as int, lower(v.subrange(0, i as int))) == Some(lower(v)),
    decreases v.len() - i
{
    let s = v.push(0x3Au32);
    if i < v.len() {
        assert(s[i as int] == v[i as int]);
        assert(lower(v.subrange(0, i as int)).push(crate::url::spec::ascii_lowercase(v[i as int])) =~= lower(v.subrange(0, i + 1int)));
        lemma_scheme_buffer(v, i + 1);
    } else {
        assert(s[i as int] == 0x3A);
        assert(v.subrange(0, i as int) =~= v);
    }
}

/// `protocol`: an RFC scheme becomes the URL's scheme, lowercased, when
/// the URL has a null port, the new scheme is special exactly when the
/// URL is, a URL with credentials does not switch to "file", and the URL
/// is not a "file" URL with an empty host (scheme state steps 2.1.1 to
/// 2.1.4 return otherwise, leaving the URL as it is).
pub proof fn lemma_protocol_agrees(url: crate::url::spec::Url, v: Seq<u32>, dp: crate::host::spec::DomainParser)
    requires
        is_scheme(v),
        url.port is None,
        crate::url::spec::is_special_scheme(lower(v)) == crate::url::spec::is_special(url),
        crate::url::spec::includes_credentials(url) ==> lower(v) != crate::url::spec::file_str(),
        !(url.scheme == crate::url::spec::file_str() && url.host == Some(crate::host::spec::Host::Empty)),
    ensures
        protocol_setter(url, v, dp) == (crate::url::spec::Url { scheme: lower(v), ..url }),
{
    reveal(crate::url::spec::state_step);
    let s = v.push(0x3Au32);
    assert forall|k: int| 0 <= k < s.len() implies 0x21 <= #[trigger] s[k] <= 0x7E by {
        if k < v.len() {
            assert(s[k] == v[k]);
        }
    }
    lemma_no_tab_or_newline(s);
    let ctx = super::lemmas::in_place_ctx(s, crate::url::spec::State::SchemeStart, dp);
    assert(ctx.input == s);
    assert(s[0] == v[0]);
    let b0 = lower(v.subrange(0, 1));
    assert(b0 =~= seq![crate::url::spec::ascii_lowercase(v[0])]);
    assert(Seq::<u32>::empty().push(crate::url::spec::ascii_lowercase(v[0])) =~= b0);
    let m1 = crate::url::spec::Machine {
        buffer: b0,
        state: crate::url::spec::State::Scheme,
        pointer: 1,
        ..super::lemmas::in_place_machine(url, crate::url::spec::State::SchemeStart)
    };
    super::lemmas::lemma_scheme_run(ctx, m1);
    lemma_scheme_buffer(v, 1);
}

// ---------------------------------------------------------------------
// username, password
// ---------------------------------------------------------------------

/// Every code point of RFC `userinfo` without ":", ";" and "=" is
/// outside the userinfo percent-encode set.
proof fn lemma_userinfo_outside(s: Seq<u32>, i: nat)
    requires
        userinfo_from(s, i),
        forall|k: int| 0 <= k < s.len() ==> #[trigger] s[k] != 0x3A && s[k] != 0x3B && s[k] != 0x3D,
    ensures
        crate::url::runs::outside_between(s, i as int, s.len() as int, clazel_percent::spec::PercentEncodeSet::Userinfo),
    decreases s.len() - i
{
    if i < s.len() {
        if is_unreserved(s[i as int]) || is_sub_delim(s[i as int]) || s[i as int] == 0x3A {
            lemma_userinfo_outside(s, i + 1);
        } else {
            lemma_userinfo_outside(s, i + 3);
        }
    }
}

/// `username` and `password`: RFC `userinfo` without ":", ";" or "=" is
/// stored as it is, for a URL that can have a username and password.
pub proof fn lemma_userinfo_agrees(url: crate::url::spec::Url, v: Seq<u32>)
    requires
        userinfo_from(v, 0),
        forall|k: int| 0 <= k < v.len() ==> #[trigger] v[k] != 0x3A && v[k] != 0x3B && v[k] != 0x3D,
        !crate::url::spec::cannot_have_username_password_port(url),
    ensures
        username_setter(url, v) == (crate::url::spec::Url { username: v, ..url }),
        password_setter(url, v) == (crate::url::spec::Url { password: v, ..url }),
{
    lemma_userinfo_outside(v, 0);
    crate::url::runs::lemma_encode_identity(v, clazel_percent::spec::PercentEncodeSet::Userinfo);
}

// ---------------------------------------------------------------------
// host, hostname
// ---------------------------------------------------------------------

/// The host state with a state override reads a reg-name's code points
/// into buffer, and at its end sets the opaque host and returns.
proof fn lemma_host_run(ctx: crate::url::spec::Ctx, m: crate::url::spec::Machine)
    requires
        ctx.state_override is Some,
        m.state is Host || m.state is Hostname,
        !m.inside_brackets,
        !crate::url::spec::is_special(m.url),
        m.url.scheme != crate::url::spec::file_str(),
        0 <= m.pointer <= ctx.input.len(),
        m.buffer + ctx.input.subrange(m.pointer, ctx.input.len() as int) == ctx.input,
        ctx.input.len() > 0,
        crate::host::independent::reg_name(ctx.input),
    ensures
        crate::url::spec::run_in_place(ctx, m) == (crate::url::spec::Url { host: Some(crate::host::spec::Host::Opaque(ctx.input)), ..m.url }),
    decreases ctx.input.len() - m.pointer
{
    reveal(crate::url::spec::state_step);
    let len = ctx.input.len() as int;
    crate::host::independent::lemma_reg_name_code_points(ctx.input, 0);
    if m.pointer < len {
        let c = ctx.input[m.pointer];
        assert(c != 0x3A && c != 0x2F && c != 0x3F && c != 0x23 && c != 0x5B && c != 0x5D && c != 0x5C) by {
            assert(!crate::host::spec::is_forbidden_host_code_point(c));
        }
        let n = crate::url::spec::Machine { buffer: m.buffer.push(c), pointer: m.pointer + 1, ..m };
        assert(n.buffer + ctx.input.subrange(n.pointer, len) =~= m.buffer + ctx.input.subrange(m.pointer, len));
        lemma_host_run(ctx, n);
    } else {
        assert(m.buffer =~= ctx.input);
        crate::host::independent::lemma_reg_name_opaque_host(ctx.input);
    }
}

/// `host` and `hostname`: a non-empty RFC `reg-name` becomes an opaque
/// host as it is, for a URL that is not special, not "file", and has no
/// opaque path.
pub proof fn lemma_host_agrees(url: crate::url::spec::Url, v: Seq<u32>, dp: crate::host::spec::DomainParser)
    requires
        v.len() > 0,
        crate::host::independent::reg_name(v),
        !crate::url::spec::is_special(url),
        url.scheme != crate::url::spec::file_str(),
        !crate::url::spec::has_opaque_path(url),
    ensures
        host_setter(url, v, dp) == (crate::url::spec::Url { host: Some(crate::host::spec::Host::Opaque(v)), ..url }),
        hostname_setter(url, v, dp) == (crate::url::spec::Url { host: Some(crate::host::spec::Host::Opaque(v)), ..url }),
{
    crate::host::independent::lemma_reg_name_code_points(v, 0);
    lemma_no_tab_or_newline(v);
    assert(Seq::<u32>::empty() + v.subrange(0, v.len() as int) =~= v);
    lemma_host_run(super::lemmas::in_place_ctx(v, crate::url::spec::State::Host, dp), super::lemmas::in_place_machine(url, crate::url::spec::State::Host));
    lemma_host_run(super::lemmas::in_place_ctx(v, crate::url::spec::State::Hostname, dp), super::lemmas::in_place_machine(url, crate::url::spec::State::Hostname));
}

// ---------------------------------------------------------------------
// port
// ---------------------------------------------------------------------

/// The RFC's decimal value is the port state's (read from the last digit
/// back).
proof fn lemma_decimal_from(s: Seq<u32>, i: nat)
    requires
        i <= s.len(),
    ensures
        decimal_from(s, i, crate::url::spec::decimal_value(s.subrange(0, i as int))) == crate::url::spec::decimal_value(s),
    decreases s.len() - i
{
    if i < s.len() {
        assert(s.subrange(0, i + 1int).drop_last() =~= s.subrange(0, i as int));
        assert(s.subrange(0, i + 1int).last() == s[i as int]);
        lemma_decimal_from(s, i + 1);
    } else {
        assert(s.subrange(0, i as int) =~= s);
    }
}

/// The port state with a state override reads digits into buffer, and at
/// the end sets the port.
proof fn lemma_port_run(ctx: crate::url::spec::Ctx, m: crate::url::spec::Machine)
    requires
        ctx.state_override is Some,
        m.state is Port,
        0 <= m.pointer <= ctx.input.len(),
        m.buffer + ctx.input.subrange(m.pointer, ctx.input.len() as int) == ctx.input,
        ctx.input.len() > 0,
        is_port(ctx.input),
        crate::url::spec::decimal_value(ctx.input) <= 0xFFFF,
    ensures
        crate::url::spec::run_in_place(ctx, m) == (crate::url::spec::Url {
            port: if crate::url::spec::default_port(m.url.scheme) == Some(crate::url::spec::decimal_value(ctx.input)) {
                None
            } else {
                Some(crate::url::spec::decimal_value(ctx.input))
            },
            ..m.url
        }),
    decreases ctx.input.len() - m.pointer
{
    reveal(crate::url::spec::state_step);
    let len = ctx.input.len() as int;
    if m.pointer < len {
        let c = ctx.input[m.pointer];
        let n = crate::url::spec::Machine { buffer: m.buffer.push(c), pointer: m.pointer + 1, ..m };
        assert(n.buffer + ctx.input.subrange(n.pointer, len) =~= m.buffer + ctx.input.subrange(m.pointer, len));
        lemma_port_run(ctx, n);
    } else {
        assert(m.buffer =~= ctx.input);
    }
}

/// `port`: a non-empty RFC `port` whose value fits in 16 bits becomes the
/// port, or null if it is the scheme's default port, for a URL that can
/// have one.
pub proof fn lemma_port_agrees(url: crate::url::spec::Url, v: Seq<u32>, dp: crate::host::spec::DomainParser)
    requires
        v.len() > 0,
        is_port(v),
        decimal_from(v, 0, 0) <= 0xFFFF,
        !crate::url::spec::cannot_have_username_password_port(url),
    ensures
        port_setter(url, v, dp) == (crate::url::spec::Url {
            port: if crate::url::spec::default_port(url.scheme) == Some(decimal_from(v, 0, 0)) {
                None
            } else {
                Some(decimal_from(v, 0, 0))
            },
            ..url
        }),
{
    lemma_decimal_from(v, 0);
    assert(v.subrange(0, 0) =~= Seq::<u32>::empty());
    assert forall|k: int| 0 <= k < v.len() implies 0x21 <= #[trigger] v[k] <= 0x7E by {
        assert(crate::host::independent::is_digit(v[k]));
    }
    lemma_no_tab_or_newline(v);
    assert(Seq::<u32>::empty() + v.subrange(0, v.len() as int) =~= v);
    lemma_port_run(super::lemmas::in_place_ctx(v, crate::url::spec::State::Port, dp), super::lemmas::in_place_machine(url, crate::url::spec::State::Port));
}

// ---------------------------------------------------------------------
// search, hash
// ---------------------------------------------------------------------

/// Every code point of an RFC `query` (or `fragment`) is printable ASCII
/// other than space, U+0022 ("), U+0023 (#), U+003C (<), U+003E (>),
/// U+0060 (`).
proof fn lemma_query_code_points(s: Seq<u32>, i: nat)
    requires
        query_from(s, i),
    ensures
        forall|k: int| i <= k < s.len() ==> 0x21 <= #[trigger] s[k] <= 0x7E && s[k] != 0x22 && s[k] != 0x23 && s[k]
            != 0x3C && s[k] != 0x3E && s[k] != 0x60,
    decreases s.len() - i
{
    if i < s.len() {
        if is_unreserved(s[i as int]) || is_sub_delim(s[i as int]) || s[i as int] == 0x3A || s[i as int] == 0x40
            || s[i as int] == 0x2F || s[i as int] == 0x3F {
            lemma_query_code_points(s, i + 1);
        } else {
            lemma_query_code_points(s, i + 3);
        }
    }
}

/// The query state with a state override appends buffer and the rest of
/// the input to the query, unchanged, when they are outside its set.
proof fn lemma_query_run(ctx: crate::url::spec::Ctx, m: crate::url::spec::Machine, q: Seq<u32>)
    requires
        ctx.state_override is Some,
        m.state is Query,
        0 <= m.pointer <= ctx.input.len(),
        m.url.query == Some(q),
        crate::url::runs::outside_all(m.buffer, crate::url::runs::query_set(m.url)),
        crate::url::runs::outside_between(ctx.input, m.pointer, ctx.input.len() as int, crate::url::runs::query_set(m.url)),
    ensures
        crate::url::spec::run_in_place(ctx, m) == (crate::url::spec::Url { query: Some(q + m.buffer + ctx.input.subrange(m.pointer, ctx.input.len() as int)), ..m.url }),
    decreases ctx.input.len() - m.pointer
{
    reveal(crate::url::spec::state_step);
    let len = ctx.input.len() as int;
    if m.pointer < len {
        let c = ctx.input[m.pointer];
        let n = crate::url::spec::Machine { buffer: m.buffer.push(c), pointer: m.pointer + 1, ..m };
        assert(crate::url::runs::outside_all(n.buffer, crate::url::runs::query_set(m.url))) by {
            assert forall|k: int| 0 <= k < n.buffer.len() implies crate::url::runs::outside(#[trigger] n.buffer[k], crate::url::runs::query_set(m.url)) by {
                if k < m.buffer.len() {
                    assert(n.buffer[k] == m.buffer[k]);
                }
            }
        }
        lemma_query_run(ctx, n, q);
        assert(n.buffer + ctx.input.subrange(n.pointer, len) =~= m.buffer + ctx.input.subrange(m.pointer, len));
        assert(q + n.buffer + ctx.input.subrange(n.pointer, len) =~= q + m.buffer + ctx.input.subrange(m.pointer, len));
    } else {
        let set = if crate::url::spec::is_special(m.url) {
            clazel_percent::spec::PercentEncodeSet::SpecialQuery
        } else {
            clazel_percent::spec::PercentEncodeSet::Query
        };
        crate::url::runs::lemma_encode_identity(m.buffer, set);
        assert(ctx.input.subrange(m.pointer, len) =~= Seq::<u32>::empty());
        assert(m.buffer + ctx.input.subrange(m.pointer, len) =~= m.buffer);
        assert(Seq::<u32>::empty() + m.buffer =~= m.buffer);
    }
}

/// `search`: "?" followed by an RFC `query` becomes the query as it is
/// (for a special URL, a query without "'").
pub proof fn lemma_search_agrees(url: crate::url::spec::Url, q: Seq<u32>, dp: crate::host::spec::DomainParser)
    requires
        query_from(q, 0),
        crate::url::spec::is_special(url) ==> forall|k: int| 0 <= k < q.len() ==> #[trigger] q[k] != 0x27,
    ensures
        search_setter(url, seq![0x3Fu32] + q, dp) == (crate::url::spec::Url { query: Some(q), ..url }),
{
    let v = seq![0x3Fu32] + q;
    assert(remove_single_leading(v, 0x3F) =~= q);
    lemma_query_code_points(q, 0);
    lemma_no_tab_or_newline(q);
    let u = crate::url::spec::Url { query: Some(seq![]), ..url };
    assert(crate::url::runs::outside_between(q, 0, q.len() as int, crate::url::runs::query_set(u))) by {
        assert forall|k: int| 0 <= k < q.len() implies crate::url::runs::outside(#[trigger] q[k], crate::url::runs::query_set(u)) by {
            assert(0x21 <= q[k] <= 0x7E);
        }
    }
    lemma_query_run(super::lemmas::in_place_ctx(q, crate::url::spec::State::Query, dp), super::lemmas::in_place_machine(u, crate::url::spec::State::Query), seq![]);
    assert(Seq::<u32>::empty() + Seq::<u32>::empty() + q.subrange(0, q.len() as int) =~= q);
}

/// `hash`: "#" followed by an RFC `fragment` becomes the fragment as it
/// is.
pub proof fn lemma_hash_agrees(url: crate::url::spec::Url, f: Seq<u32>, dp: crate::host::spec::DomainParser)
    requires
        query_from(f, 0),
    ensures
        hash_setter(url, seq![0x23u32] + f, dp) == (crate::url::spec::Url { fragment: Some(f), ..url }),
{
    let v = seq![0x23u32] + f;
    assert(remove_single_leading(v, 0x23) =~= f);
    lemma_query_code_points(f, 0);
    lemma_no_tab_or_newline(f);
    let u = crate::url::spec::Url { fragment: Some(seq![]), ..url };
    let ctx = super::lemmas::in_place_ctx(f, crate::url::spec::State::Fragment, dp);
    let m = super::lemmas::in_place_machine(u, crate::url::spec::State::Fragment);
    assert(crate::url::runs::outside_between(f, 0, f.len() as int, clazel_percent::spec::PercentEncodeSet::Fragment)) by {
        assert forall|k: int| 0 <= k < f.len() implies crate::url::runs::outside(#[trigger] f[k], clazel_percent::spec::PercentEncodeSet::Fragment) by {
            assert(0x21 <= f[k] <= 0x7E);
        }
    }
    crate::url::runs::lemma_fragment_run(ctx, m, seq![]);
    super::lemmas::lemma_run_in_place_agrees(ctx, m);
    assert(Seq::<u32>::empty() + f.subrange(0, f.len() as int) =~= f);
}

// ---------------------------------------------------------------------
// pathname
// ---------------------------------------------------------------------

/// The path state with a state override, on input with no "?" or "#"
/// ahead, does what it does without one.
proof fn lemma_path_bridge(ctx: crate::url::spec::Ctx, m: crate::url::spec::Machine)
    requires
        ctx.state_override is Some,
        m.state is Path,
        0 <= m.pointer <= ctx.input.len(),
        forall|k: int| m.pointer <= k < ctx.input.len() ==> #[trigger] ctx.input[k] != 0x3F && ctx.input[k] != 0x23,
    ensures
        crate::url::spec::run(crate::url::spec::Ctx { state_override: None, ..ctx }, m) == Some(crate::url::spec::run_in_place(ctx, m)),
    decreases ctx.input.len() - m.pointer
{
    reveal(crate::url::spec::state_step);
    let cn = crate::url::spec::Ctx { state_override: None, ..ctx };
    assert(crate::url::spec::path_state(ctx, m) == crate::url::spec::path_state(cn, m));
    if let crate::url::spec::Step::Continue(next) = crate::url::spec::path_state(ctx, m) {
        if next.pointer < ctx.input.len() {
            lemma_path_bridge(ctx, crate::url::spec::Machine { pointer: next.pointer + 1, ..next });
        }
    }
}

/// `path-abempty` of one or more segments is "/" and the segments joined
/// with "/".
proof fn lemma_path_abempty_join(segs: Seq<Seq<u32>>)
    requires
        segs.len() > 0,
    ensures
        path_abempty(segs) == seq![0x2Fu32] + crate::url::runs::join(segs),
    decreases segs.len()
{
    let rest = segs.subrange(1, segs.len() as int);
    assert(path_abempty(segs) == seq![0x2Fu32] + segs[0] + path_abempty(rest));
    if segs.len() == 1 {
        assert(rest =~= Seq::<Seq<u32>>::empty());
        assert(path_abempty(rest) == Seq::<u32>::empty());
        assert(crate::url::runs::join(segs) == segs[0]);
        assert(seq![0x2Fu32] + segs[0] + Seq::<u32>::empty() =~= seq![0x2Fu32] + segs[0]);
    } else {
        assert(crate::url::runs::join(segs) == segs[0] + seq![0x2Fu32] + crate::url::runs::join(rest));
        lemma_path_abempty_join(rest);
        assert(seq![0x2Fu32] + segs[0] + (seq![0x2Fu32] + crate::url::runs::join(rest)) =~= seq![0x2Fu32] + (segs[0]
            + seq![0x2Fu32] + crate::url::runs::join(rest)));
    }
}

/// A plain segment that is not a dot-segment is a segment the path state
/// appends as it is (the URL Standard's single-dot and double-dot
/// segments other than "." and ".." all hold "%").
proof fn lemma_plain_segment(s: Seq<u32>, special: bool)
    requires
        is_plain_segment(s),
        !is_dot_segment(s),
    ensures
        crate::url::round_trip::round_trip_segment(s, special),
{
    assert forall|k: int| 0 <= k < s.len() implies crate::url::runs::path_char(#[trigger] s[k], special) by {
        assert(is_pchar_code_point(s[k]));
    }
    crate::url::states_path::lemma_ascii_lowercase_string(s);
    let p = 0x25u32;
    let t1 = seq![p, 0x32, 0x65];
    let t2 = seq![0x2Eu32, p, 0x32, 0x65];
    let t3 = seq![p, 0x32, 0x65, 0x2E];
    let t4 = seq![p, 0x32, 0x65, p, 0x32, 0x65];
    crate::url::states_path::lemma_ascii_lowercase_string(t1);
    crate::url::states_path::lemma_ascii_lowercase_string(t2);
    crate::url::states_path::lemma_ascii_lowercase_string(t3);
    crate::url::states_path::lemma_ascii_lowercase_string(t4);
    let ls = crate::url::spec::ascii_lowercase_string(s);
    if ls == crate::url::spec::ascii_lowercase_string(t1) || ls == crate::url::spec::ascii_lowercase_string(t3)
        || ls == crate::url::spec::ascii_lowercase_string(t4) {
        assert(ls[0] == p);
        assert(is_pchar_code_point(s[0]));
    }
    if ls == crate::url::spec::ascii_lowercase_string(t2) {
        assert(ls[1] == p);
        assert(is_pchar_code_point(s[1]));
    }
}

/// `pathname`: a `path-abempty` of one or more plain segments, none of
/// them a dot-segment, becomes the path, segment by segment, for a URL
/// that is not "file" and has no opaque path.
pub proof fn lemma_pathname_agrees(url: crate::url::spec::Url, segs: Seq<Seq<u32>>, dp: crate::host::spec::DomainParser)
    requires
        segs.len() > 0,
        forall|i: int| 0 <= i < segs.len() ==> is_plain_segment(#[trigger] segs[i]) && !is_dot_segment(segs[i]),
        url.scheme != crate::url::spec::file_str(),
        !crate::url::spec::has_opaque_path(url),
    ensures
        pathname_setter(url, path_abempty(segs), dp) == (crate::url::spec::Url { path: crate::url::spec::UrlPath::List(segs), ..url }),
{
    reveal(crate::url::spec::state_step);
    let special = crate::url::spec::is_special(url);
    assert forall|i: int| 0 <= i < segs.len() implies crate::url::round_trip::round_trip_segment(#[trigger] segs[i], special) by {
        lemma_plain_segment(segs[i], special);
    }
    assert forall|i: int| 0 <= i < segs.len() implies crate::url::runs::path_segment_ok(#[trigger] segs[i], special) by {
        assert(crate::url::round_trip::round_trip_segment(segs[i], special));
    }
    crate::url::round_trip::lemma_join_plain(segs, special);
    crate::url::round_trip::lemma_path_model_plain(seq![], segs, special);
    lemma_path_abempty_join(segs);
    let j = crate::url::runs::join(segs);
    let v = path_abempty(segs);
    assert forall|k: int| 0 <= k < v.len() implies 0x21 <= #[trigger] v[k] <= 0x7E && v[k] != 0x3F && v[k] != 0x23 by {
        if k > 0 {
            assert(v[k] == j[k - 1]);
            assert(crate::url::runs::path_char(j[k - 1], special) || j[k - 1] == 0x2F);
        }
    }
    lemma_no_tab_or_newline(v);
    let ctx = super::lemmas::in_place_ctx(v, crate::url::spec::State::PathStart, dp);
    assert(ctx.input == v);
    let e = crate::url::spec::Url { path: crate::url::spec::UrlPath::List(seq![]), ..url };
    let m1 = crate::url::spec::Machine { state: crate::url::spec::State::Path, pointer: 1, ..super::lemmas::in_place_machine(e, crate::url::spec::State::PathStart) };
    lemma_path_bridge(ctx, m1);
    let cn = crate::url::spec::Ctx { state_override: None, ..ctx };
    assert(v.subrange(1, 1 + j.len() as int) =~= j);
    assert(crate::url::runs::plain_path_url(m1.url));
    crate::url::runs::lemma_path_run(cn, m1, seq![], segs);
    assert(Seq::<Seq<u32>>::empty() + segs =~= segs);
}

} // verus!
