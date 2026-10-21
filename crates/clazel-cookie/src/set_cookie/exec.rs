//! The executable Set-Cookie parser, proven to meet [`super::contract`].
//!
//! The code mirrors the spec: [`parse_attributes_exec`] is the
//! "unparsed-attributes" loop of §5.6, [`process_attribute_exec`] step 7
//! with §5.6.1 to §5.6.7, and [`parse_a_set_cookie_string`] steps 1 to 6.
//! Each is proven equal to its spec function, so the step comments live
//! in [`super::spec`].

use super::spec::*;
use crate::strings::{
    ascii_lowercase_exec, at, begins_with_case_insensitive_match_exec, case_insensitive_match_exec, find_octet_exec,
    remove_leading_and_trailing_wsp_exec, sub,
};
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// An attribute of the cookie-attribute-list, viewed as [`Attribute`].
/// Times are seconds since 1601-01-01T00:00:00Z.
pub enum AttributeExec {
    /// "Expires", with the expiry-time.
    Expires(u64),
    /// "Max-Age", with the expiry-time.
    MaxAge(u64),
    /// "Domain", with the cookie-domain.
    Domain(Vec<u8>),
    /// "Path", with the cookie-path.
    Path(Vec<u8>),
    /// "Secure".
    Secure,
    /// "HttpOnly".
    HttpOnly,
    /// "SameSite", with the enforcement.
    SameSite(SameSite),
}

impl View for AttributeExec {
    type V = Attribute;

    open spec fn view(&self) -> Attribute {
        match self {
            AttributeExec::Expires(t) => Attribute::Expires(*t as int),
            AttributeExec::MaxAge(t) => Attribute::MaxAge(*t as int),
            AttributeExec::Domain(d) => Attribute::Domain(d@),
            AttributeExec::Path(p) => Attribute::Path(p@),
            AttributeExec::Secure => Attribute::Secure,
            AttributeExec::HttpOnly => Attribute::HttpOnly,
            AttributeExec::SameSite(s) => Attribute::SameSite(*s),
        }
    }
}

/// The view of an attribute list.
pub open spec fn attributes_view(v: Seq<AttributeExec>) -> Seq<Attribute> {
    v.map_values(|a: AttributeExec| a@)
}

/// What the user agent receives from a Set-Cookie header field, viewed as
/// [`SetCookie`].
pub struct SetCookieRecord {
    /// cookie-name.
    pub name: Vec<u8>,
    /// cookie-value.
    pub value: Vec<u8>,
    /// cookie-attribute-list.
    pub attributes: Vec<AttributeExec>,
}

impl View for SetCookieRecord {
    type V = SetCookie;

    open spec fn view(&self) -> SetCookie {
        SetCookie { name: self.name@, value: self.value@, attributes: attributes_view(self.attributes@) }
    }
}

/// The view of an optional attribute; `None` is "ignore the cookie-av".
pub open spec fn attribute_option_view(a: Option<AttributeExec>) -> Option<Attribute> {
    match a {
        Some(a) => Some(a@),
        None => None,
    }
}

/// The view of an optional cookie; `None` is "ignore entirely".
pub open spec fn cookie_option_view(c: Option<SetCookieRecord>) -> Option<SetCookie> {
    match c {
        Some(c) => Some(c@),
        None => None,
    }
}

// ---------------------------------------------------------------------
// String literals.
// ---------------------------------------------------------------------

/// "Expires"
fn lit_expires_exec() -> (r: Vec<u8>)
    ensures
        r@ == lit_expires(),
{
    let r = vec![0x45u8, 0x78, 0x70, 0x69, 0x72, 0x65, 0x73];
    assert(r@ =~= lit_expires());
    r
}

/// "Max-Age"
fn lit_max_age_exec() -> (r: Vec<u8>)
    ensures
        r@ == lit_max_age(),
{
    let r = vec![0x4Du8, 0x61, 0x78, 0x2D, 0x41, 0x67, 0x65];
    assert(r@ =~= lit_max_age());
    r
}

/// "Domain"
fn lit_domain_exec() -> (r: Vec<u8>)
    ensures
        r@ == lit_domain(),
{
    let r = vec![0x44u8, 0x6F, 0x6D, 0x61, 0x69, 0x6E];
    assert(r@ =~= lit_domain());
    r
}

/// "Path"
fn lit_path_exec() -> (r: Vec<u8>)
    ensures
        r@ == lit_path(),
{
    let r = vec![0x50u8, 0x61, 0x74, 0x68];
    assert(r@ =~= lit_path());
    r
}

/// "Secure"
fn lit_secure_exec() -> (r: Vec<u8>)
    ensures
        r@ == lit_secure(),
{
    let r = vec![0x53u8, 0x65, 0x63, 0x75, 0x72, 0x65];
    assert(r@ =~= lit_secure());
    r
}

/// "HttpOnly"
fn lit_http_only_exec() -> (r: Vec<u8>)
    ensures
        r@ == lit_http_only(),
{
    let r = vec![0x48u8, 0x74, 0x74, 0x70, 0x4F, 0x6E, 0x6C, 0x79];
    assert(r@ =~= lit_http_only());
    r
}

/// "SameSite"
fn lit_same_site_exec() -> (r: Vec<u8>)
    ensures
        r@ == lit_same_site(),
{
    let r = vec![0x53u8, 0x61, 0x6D, 0x65, 0x53, 0x69, 0x74, 0x65];
    assert(r@ =~= lit_same_site());
    r
}

/// "None"
fn lit_none_exec() -> (r: Vec<u8>)
    ensures
        r@ == lit_none(),
{
    let r = vec![0x4Eu8, 0x6F, 0x6E, 0x65];
    assert(r@ =~= lit_none());
    r
}

/// "Strict"
fn lit_strict_exec() -> (r: Vec<u8>)
    ensures
        r@ == lit_strict(),
{
    let r = vec![0x53u8, 0x74, 0x72, 0x69, 0x63, 0x74];
    assert(r@ =~= lit_strict());
    r
}

/// "Lax"
fn lit_lax_exec() -> (r: Vec<u8>)
    ensures
        r@ == lit_lax(),
{
    let r = vec![0x4Cu8, 0x61, 0x78];
    assert(r@ =~= lit_lax());
    r
}

/// "__Secure-"
fn lit_secure_prefix_exec() -> (r: Vec<u8>)
    ensures
        r@ == lit_secure_prefix(),
{
    let r = vec![0x5Fu8, 0x5F, 0x53, 0x65, 0x63, 0x75, 0x72, 0x65, 0x2D];
    assert(r@ =~= lit_secure_prefix());
    r
}

/// "__Host-"
fn lit_host_prefix_exec() -> (r: Vec<u8>)
    ensures
        r@ == lit_host_prefix(),
{
    let r = vec![0x5Fu8, 0x5F, 0x48, 0x6F, 0x73, 0x74, 0x2D];
    assert(r@ =~= lit_host_prefix());
    r
}

// ---------------------------------------------------------------------
// §5.6.1 to §5.6.7.
// ---------------------------------------------------------------------

/// §5.6.1: process an Expires attribute-value.
fn process_expires_exec(attribute_value: &[u8], now: u64) -> (r: Option<AttributeExec>)
    requires
        super::contract::now_in_range(now as int),
    ensures
        attribute_option_view(r) == process_expires(attribute_value@, now as int),
{
    proof {
        crate::date::lemmas::lemma_parsed_date_in_range(attribute_value@);
    }
    let date = crate::date::exec::parse_a_cookie_date(attribute_value)?;
    let expiry_time = date.seconds_since_1601();
    let limit = now.saturating_add(34560000);
    let expiry_time = if expiry_time > limit { limit } else { expiry_time };
    Some(AttributeExec::Expires(expiry_time))
}

/// The most a Max-Age number is counted to: far above the lifetime limit,
/// so that capping before the limit changes nothing.
const NUMBER_CAP: u64 = 1_000_000_000;

/// §5.6.2 steps 1 to 3: is the attribute-value acceptable?
fn max_age_value_acceptable_exec(v: &[u8]) -> (r: bool)
    ensures
        r == max_age_value_acceptable(v@),
{
    let first = match at(v, 0) {
        Some(c) => c,
        None => return false,
    };
    if !(crate::strings::is_digit_exec(first)
        || (first == 0x2D && match at(v, 1) {
            Some(c) => crate::strings::is_digit_exec(c),
            None => false,
        }))
    {
        return false;
    }
    let mut i: usize = 1;
    while i < v.len()
        invariant
            1 <= i <= v.len(),
            forall|k: int| 1 <= k < i ==> crate::ascii::is_digit(#[trigger] v@[k]),
        decreases v.len() - i,
    {
        match at(v, i) {
            Some(c) => {
                if !crate::strings::is_digit_exec(c) {
                    return false;
                }
            },
            None => return false,
        }
        // Never saturates: i < v.len().
        i = i.saturating_add(1);
    }
    true
}

/// The number the digits of `s` from `start` denote, counted up to
/// [`NUMBER_CAP`].
fn capped_digits_value(s: &[u8], start: usize) -> (r: u64)
    requires
        start <= s.len(),
        forall|k: int| start <= k < s.len() ==> crate::ascii::is_digit(#[trigger] s@[k]),
    ensures
        r as int == (if crate::ascii::digits_value(s@.subrange(start as int, s.len() as int)) < NUMBER_CAP as nat {
            crate::ascii::digits_value(s@.subrange(start as int, s.len() as int)) as int
        } else {
            NUMBER_CAP as int
        }),
{
    let mut acc: u64 = 0;
    let mut i = start;
    assert(s@.subrange(start as int, start as int) =~= Seq::<u8>::empty());
    while i < s.len()
        invariant
            start <= i <= s.len(),
            forall|k: int| start <= k < s.len() ==> crate::ascii::is_digit(#[trigger] s@[k]),
            acc <= NUMBER_CAP,
            acc as int == (if crate::ascii::digits_value(s@.subrange(start as int, i as int)) < NUMBER_CAP as nat {
                crate::ascii::digits_value(s@.subrange(start as int, i as int)) as int
            } else {
                NUMBER_CAP as int
            }),
        decreases s.len() - i,
    {
        let d = match at(s, i) {
            Some(c) => c.saturating_sub(0x30),
            None => 0,
        };
        assert(s@.subrange(start as int, i as int + 1).drop_last() =~= s@.subrange(start as int, i as int));
        assert(s@.subrange(start as int, i as int + 1).last() == s@[i as int]);
        let next = acc.saturating_mul(10).saturating_add(d as u64);
        acc = if next > NUMBER_CAP { NUMBER_CAP } else { next };
        // Never saturates: i < s.len().
        i = i.saturating_add(1);
    }
    assert(s@.subrange(start as int, s.len() as int) == s@.subrange(start as int, i as int));
    acc
}

/// §5.6.2: process a Max-Age attribute-value.
fn process_max_age_exec(attribute_value: &[u8], now: u64) -> (r: Option<AttributeExec>)
    requires
        super::contract::now_in_range(now as int),
    ensures
        attribute_option_view(r) == process_max_age(attribute_value@, now as int),
{
    if !max_age_value_acceptable_exec(attribute_value) {
        return None;
    }
    let negative = at(attribute_value, 0) == Some(0x2D);
    let start: usize = if negative { 1 } else { 0 };
    proof {
        assert(attribute_value@.subrange(0, attribute_value@.len() as int) =~= attribute_value@);
        if !negative {
            assert(crate::ascii::is_digit(attribute_value@[0]));
        }
        assert(attribute_value@.skip(1) =~= attribute_value@.subrange(1, attribute_value@.len() as int));
    }
    let magnitude = capped_digits_value(attribute_value, start);
    // delta-seconds is -magnitude when negative, else magnitude; capped at
    // the lifetime limit.
    let delta: u64 = if negative || magnitude == 0 {
        0
    } else if magnitude < 34560000 {
        magnitude
    } else {
        34560000
    };
    let expiry_time = if delta == 0 { 0 } else { now.saturating_add(delta) };
    Some(AttributeExec::MaxAge(expiry_time))
}

/// §5.6.3: process a Domain attribute-value.
fn process_domain_exec(attribute_value: &[u8]) -> (r: Option<AttributeExec>)
    ensures
        attribute_option_view(r) == process_domain(attribute_value@),
{
    let cookie_domain = if at(attribute_value, 0) == Some(0x2E) {
        vstd::slice::slice_subrange(attribute_value, 1, attribute_value.len())
    } else {
        attribute_value
    };
    assert(cookie_domain@ =~= if attribute_value@.len() > 0 && attribute_value@[0] == 0x2E {
        attribute_value@.skip(1)
    } else {
        attribute_value@
    });
    Some(AttributeExec::Domain(ascii_lowercase_exec(cookie_domain)))
}

/// §5.6.4: process a Path attribute-value.
fn process_path_exec(attribute_value: &[u8], uri_path: &[u8]) -> (r: Option<AttributeExec>)
    ensures
        attribute_option_view(r) == process_path(attribute_value@, uri_path@),
{
    if attribute_value.is_empty() || at(attribute_value, 0) != Some(0x2F) {
        Some(AttributeExec::Path(crate::matching::exec::default_path(uri_path)))
    } else {
        Some(AttributeExec::Path(crate::strings::copy(attribute_value)))
    }
}

/// §5.6.7: process a SameSite attribute-value.
fn process_same_site_exec(attribute_value: &[u8]) -> (r: Option<AttributeExec>)
    ensures
        attribute_option_view(r) == process_same_site(attribute_value@),
{
    let none = lit_none_exec();
    let strict = lit_strict_exec();
    let lax = lit_lax_exec();
    let enforcement = if case_insensitive_match_exec(attribute_value, none.as_slice()) {
        SameSite::None
    } else if case_insensitive_match_exec(attribute_value, strict.as_slice()) {
        SameSite::Strict
    } else if case_insensitive_match_exec(attribute_value, lax.as_slice()) {
        SameSite::Lax
    } else {
        SameSite::Default
    };
    Some(AttributeExec::SameSite(enforcement))
}

/// §5.6 step 7: process an attribute-name and attribute-value.
pub fn process_attribute_exec(attribute_name: &[u8], attribute_value: &[u8], uri_path: &[u8], now: u64) -> (r: Option<
    AttributeExec,
>)
    requires
        super::contract::now_in_range(now as int),
    ensures
        attribute_option_view(r) == process_attribute(attribute_name@, attribute_value@, uri_path@, now as int),
{
    if case_insensitive_match_exec(attribute_name, lit_expires_exec().as_slice()) {
        process_expires_exec(attribute_value, now)
    } else if case_insensitive_match_exec(attribute_name, lit_max_age_exec().as_slice()) {
        process_max_age_exec(attribute_value, now)
    } else if case_insensitive_match_exec(attribute_name, lit_domain_exec().as_slice()) {
        process_domain_exec(attribute_value)
    } else if case_insensitive_match_exec(attribute_name, lit_path_exec().as_slice()) {
        process_path_exec(attribute_value, uri_path)
    } else if case_insensitive_match_exec(attribute_name, lit_secure_exec().as_slice()) {
        Some(AttributeExec::Secure)
    } else if case_insensitive_match_exec(attribute_name, lit_http_only_exec().as_slice()) {
        Some(AttributeExec::HttpOnly)
    } else if case_insensitive_match_exec(attribute_name, lit_same_site_exec().as_slice()) {
        process_same_site_exec(attribute_value)
    } else {
        None
    }
}

// ---------------------------------------------------------------------
// §5.6 the algorithm.
// ---------------------------------------------------------------------

/// The (name, value) halves of `s` around its first "=": the whole string
/// is the name when there is none and `whole_is_value` is false.
fn split_at_equals(s: &[u8]) -> (r: (Vec<u8>, Vec<u8>, bool))
    ensures
        r.2 == (crate::ascii::find_octet(s@, 0x3D, 0) < s@.len()),
        r.2 ==> (r.0@ == s@.take(crate::ascii::find_octet(s@, 0x3D, 0) as int)
            && r.1@ == s@.skip(crate::ascii::find_octet(s@, 0x3D, 0) as int + 1)),
        !r.2 ==> (r.0@ == s@ && r.1@ == Seq::<u8>::empty()),
{
    let equals = find_octet_exec(s, 0x3D, 0);
    proof {
        super::termination::lemma_find_octet_bounds(s@, 0x3D, 0);
    }
    if equals < s.len() {
        let name = sub(s, 0, equals);
        // Never saturates: equals < s.len().
        let value = sub(s, equals.saturating_add(1), s.len());
        assert(name@ =~= s@.take(equals as int));
        assert(value@ =~= s@.skip(equals as int + 1));
        (name, value, true)
    } else {
        (crate::strings::copy(s), Vec::new(), false)
    }
}

/// §5.6, "parse the unparsed-attributes", from the ";" at `pos`.
pub fn parse_attributes_exec(s: &[u8], pos: usize, uri_path: &[u8], now: u64) -> (out: Vec<AttributeExec>)
    requires
        super::contract::now_in_range(now as int),
        pos <= s.len(),
    ensures
        attributes_view(out@) == parse_attributes(s@, pos as nat, uri_path@, now as int, seq![]),
{
    let mut list: Vec<AttributeExec> = Vec::new();
    let mut position = pos;
    let ghost start = pos as nat;
    assert(attributes_view(list@) =~= Seq::<Attribute>::empty());
    while position < s.len()
        invariant
            position <= s.len(),
            super::contract::now_in_range(now as int),
            parse_attributes(s@, start, uri_path@, now as int, seq![]) == parse_attributes(
                s@,
                position as nat,
                uri_path@,
                now as int,
                attributes_view(list@),
            ),
        decreases s.len() - position,
    {
        proof {
            super::termination::lemma_find_octet_bounds(s@, 0x3B, (position + 1) as nat);
        }
        // Never saturates: position < s.len().
        let av_start = position.saturating_add(1);
        let end = find_octet_exec(s, 0x3B, av_start);
        let cookie_av = sub(s, av_start, end);
        let (name, value, _) = split_at_equals(cookie_av.as_slice());
        let attribute_name = remove_leading_and_trailing_wsp_exec(name.as_slice());
        let attribute_value = remove_leading_and_trailing_wsp_exec(value.as_slice());
        let ghost list_before = attributes_view(list@);
        // 6. A value longer than 1024 octets ignores the cookie-av.
        let processed = if attribute_value.len() <= 1024 {
            process_attribute_exec(attribute_name.as_slice(), attribute_value.as_slice(), uri_path, now)
        } else {
            None
        };
        if let Some(attribute) = processed {
            let ghost attribute_view = attribute@;
            list.push(attribute);
            assert(attributes_view(list@) =~= list_before.push(attribute_view));
        }
        reveal_with_fuel(parse_attributes, 2);
        position = end;
    }
    list
}

/// §5.6 "parse a set-cookie-string", for a request whose URL has path
/// `uri_path`, at time `now` (seconds since 1601-01-01T00:00:00Z). `None`
/// is "ignore the set-cookie-string entirely".
pub fn parse_a_set_cookie_string(s: &[u8], uri_path: &[u8], now: u64) -> (output: Option<SetCookieRecord>)
    requires
        super::contract::parse_a_set_cookie_string_requires(s@, uri_path@, now as int),
    ensures
        super::contract::parse_a_set_cookie_string_ensures(s@, uri_path@, now as int, cookie_option_view(output)),
{
    // 1.
    if contains_ctl_exec(s) {
        return None;
    }
    // 2.
    let semicolon = find_octet_exec(s, 0x3B, 0);
    proof {
        super::termination::lemma_find_octet_bounds(s@, 0x3B, 0);
    }
    let name_value_pair = sub(s, 0, semicolon);
    // 3.
    let (first, second, has_equals) = split_at_equals(name_value_pair.as_slice());
    // "If the name-value-pair string lacks a %x3D ("=") character, then the
    // name string is empty, and the value string is the value of
    // name-value-pair."
    let (name_string, value_string) = if has_equals { (first, second) } else { (Vec::new(), first) };
    assert(name_value_pair@ == s@.subrange(0, semicolon as int));
    // 4.
    let name_string = remove_leading_and_trailing_wsp_exec(name_string.as_slice());
    let value_string = remove_leading_and_trailing_wsp_exec(value_string.as_slice());
    // 5.
    if name_string.len().saturating_add(value_string.len()) > 4096 {
        return None;
    }
    // 6.
    let attributes = parse_attributes_exec(s, semicolon, uri_path, now);
    Some(SetCookieRecord { name: name_string, value: value_string, attributes })
}

/// `s` contains a CTL character excluding HTAB (§5.6 step 1).
fn contains_ctl_exec(s: &[u8]) -> (r: bool)
    ensures
        r == contains_ctl_excluding_htab(s@),
{
    let mut i: usize = 0;
    while i < s.len()
        invariant
            i <= s.len(),
            forall|k: int| 0 <= k < i ==> !is_ctl_excluding_htab(#[trigger] s@[k]),
        decreases s.len() - i,
    {
        let c = at(s, i).unwrap_or(0x20);
        if c <= 0x08 || (0x0A..=0x1F).contains(&c) || c == 0x7F {
            assert(is_ctl_excluding_htab(s@[i as int]));
            return true;
        }
        // Never saturates: i < s.len().
        i = i.saturating_add(1);
    }
    false
}

// ---------------------------------------------------------------------
// §5.4 name prefixes.
// ---------------------------------------------------------------------

/// §5.4 and §5.7 steps 20 to 22: the cookie name prefix requirements.
pub fn name_prefix_requirements_met(cookie: &SetCookieRecord, secure_only_flag: bool, host_only_flag: bool) -> (output: bool)
    ensures
        super::contract::name_prefix_requirements_met_ensures(cookie@, secure_only_flag, host_only_flag, output),
{
    let secure_prefix = lit_secure_prefix_exec();
    let host_prefix = lit_host_prefix_exec();
    let name_secure = begins_with_case_insensitive_match_exec(cookie.name.as_slice(), secure_prefix.as_slice());
    let name_host = begins_with_case_insensitive_match_exec(cookie.name.as_slice(), host_prefix.as_slice());
    let value_secure = begins_with_case_insensitive_match_exec(cookie.value.as_slice(), secure_prefix.as_slice());
    let value_host = begins_with_case_insensitive_match_exec(cookie.value.as_slice(), host_prefix.as_slice());
    // 20.
    if name_secure && !secure_only_flag {
        return false;
    }
    // 21.
    if name_host && !(secure_only_flag && host_only_flag && last_path_is_root(cookie.attributes.as_slice())) {
        return false;
    }
    // 22.
    !(cookie.name.is_empty() && (value_secure || value_host))
}

/// Is the last Path attribute's value "/"?
fn last_path_is_root(attributes: &[AttributeExec]) -> (r: bool)
    ensures
        r == (last_path_attribute(attributes_view(attributes@)) == Some(seq![0x2Fu8])),
{
    let mut end = attributes.len();
    assert(attributes_view(attributes@).subrange(0, end as int) =~= attributes_view(attributes@));
    while end > 0
        invariant
            end <= attributes.len(),
            last_path_attribute(attributes_view(attributes@)) == last_path_attribute(
                attributes_view(attributes@).subrange(0, end as int),
            ),
        decreases end,
    {
        // Never saturates: end > 0.
        let last = end.saturating_sub(1);
        let ghost prefix = attributes_view(attributes@).subrange(0, end as int);
        assert(prefix.last() == attributes@[last as int]@);
        assert(prefix.drop_last() =~= attributes_view(attributes@).subrange(0, last as int));
        if let Some(AttributeExec::Path(p)) = attributes.get(last) {
            assert(attributes@[last as int]@ == Attribute::Path(p@));
            let is_root = p.len() == 1 && at(p.as_slice(), 0) == Some(0x2F);
            if is_root {
                assert(p@ =~= seq![0x2Fu8]);
            }
            return is_root;
        }
        end = last;
    }
    false
}

} // verus!
