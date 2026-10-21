//! Facts proven about [`super::spec`]. They are evidence that the
//! transcription is right (for example that no instant exceeds the lifetime
//! limit), not part of what the implementation must meet.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// §5.5: the limit is 400 days, 34 560 000 seconds.
pub proof fn lemma_cookie_age_limit_is_400_days()
    ensures
        cookie_age_limit() == 400 * 86400,
{
}

/// The earliest representable instant is that of 1601-01-01T00:00:00Z.
pub proof fn lemma_earliest_is_1601()
    ensures
        earliest_representable() == crate::date::spec::seconds_since_1601(
            crate::date::spec::CookieDate { year: 1601, month: 1, day_of_month: 1, hour: 0, minute: 0, second: 0 },
        ),
{
    crate::date::lemmas::lemma_epoch_is_zero();
}

/// §5.1.1 steps 3 to 7 and §5.6.1 step 4: an Expires attribute is never
/// later than now plus the limit, and never earlier than the earliest
/// representable instant.
pub proof fn lemma_expires_limited(value: Seq<u8>, now: int)
    requires
        now >= 0,
    ensures
        process_expires(value, now) matches Some(a) ==> (a is Expires && earliest_representable() <= a->Expires_0
            <= now + cookie_age_limit()),
{
    crate::date::lemmas::lemma_parsed_date_in_range(value);
    if let Some(d) = crate::date::spec::parse_a_cookie_date(value) {
        crate::date::lemmas::lemma_seconds_nonnegative(d);
    }
}

/// §5.6.2 steps 4 to 8: a Max-Age attribute is either the earliest
/// representable instant, or between now and now plus the limit.
pub proof fn lemma_max_age_limited(value: Seq<u8>, now: int)
    requires
        now >= 0,
    ensures
        process_max_age(value, now) matches Some(a) ==> (a is MaxAge && (a->MaxAge_0 == earliest_representable() || (now
            < a->MaxAge_0 <= now + cookie_age_limit()))),
{
}

/// §5.6.3: a Domain attribute is lower case, at every index.
pub proof fn lemma_domain_is_lowercase(value: Seq<u8>, i: int)
    ensures
        process_domain(value) matches Some(a) ==> (a is Domain && (0 <= i < a->Domain_0.len() ==> !(0x41
            <= a->Domain_0[i] <= 0x5A))),
{
    if let Some(Attribute::Domain(d)) = process_domain(value) {
        let cookie_domain = if value.len() > 0 && value[0] == 0x2E { value.skip(1) } else { value };
        assert(d == crate::ascii::ascii_lowercase(cookie_domain));
        if 0 <= i < d.len() {
            assert(d[i] == crate::ascii::ascii_lowercase_octet(cookie_domain[i]));
        }
    }
}

/// §5.6.3 step 2: a leading "." is removed.
pub proof fn lemma_domain_strips_leading_dot(rest: Seq<u8>)
    ensures
        process_domain(seq![0x2Eu8] + rest) == Some(Attribute::Domain(crate::ascii::ascii_lowercase(rest))),
{
    assert((seq![0x2Eu8] + rest).skip(1) =~= rest);
}

/// §5.6.4: every Path attribute starts with "/".
pub proof fn lemma_path_is_absolute(value: Seq<u8>, uri_path: Seq<u8>)
    ensures
        process_path(value, uri_path) matches Some(a) ==> (a is Path && a->Path_0.len() > 0 && a->Path_0[0] == 0x2F),
{
    crate::matching::lemmas::lemma_default_path_shape(uri_path);
}

/// §5.6.7: "None" in any case is the None enforcement.
pub proof fn lemma_same_site_none(value: Seq<u8>)
    requires
        crate::ascii::case_insensitive_match(value, lit_none()),
    ensures
        process_same_site(value) == Some(Attribute::SameSite(SameSite::None)),
{
}

/// §5.6 step 1: DEL and the C0 controls except HTAB are CTL characters.
pub proof fn lemma_ctl_characters()
    ensures
        is_ctl_excluding_htab(0x7F),
        is_ctl_excluding_htab(0x00),
        is_ctl_excluding_htab(0x0A),
        !is_ctl_excluding_htab(0x09),
        !is_ctl_excluding_htab(0x20),
{
}

/// §5.6 step 5: a cookie the parser returns has a name and value of at
/// most 4096 octets in all.
pub proof fn lemma_name_and_value_bounded(s: Seq<u8>, uri_path: Seq<u8>, now: int)
    ensures
        parse_a_set_cookie_string(s, uri_path, now) matches Some(c) ==> c.name.len() + c.value.len() <= 4096,
{
}

/// §5.6 steps 7 and 8: the attribute list only grows.
pub proof fn lemma_attributes_extend(s: Seq<u8>, pos: nat, uri_path: Seq<u8>, now: int, list: Seq<Attribute>)
    ensures
        list.is_prefix_of(parse_attributes(s, pos, uri_path, now, list)),
    decreases s.len() - pos
{
    if pos < s.len() {
        super::termination::lemma_find_octet_bounds(s, 0x3B, (pos + 1) as nat);
        let end = crate::ascii::find_octet(s, 0x3B, pos + 1);
        let cookie_av = s.subrange((pos + 1) as int, end as int);
        let equals = crate::ascii::find_octet(cookie_av, 0x3D, 0);
        let (n, v) = if equals < cookie_av.len() {
            (cookie_av.take(equals as int), cookie_av.skip(equals as int + 1))
        } else {
            (cookie_av, seq![])
        };
        let n = crate::ascii::remove_leading_and_trailing_wsp(n);
        let v = crate::ascii::remove_leading_and_trailing_wsp(v);
        if v.len() > 1024 {
            lemma_attributes_extend(s, end, uri_path, now, list);
        } else {
            match process_attribute(n, v, uri_path, now) {
                Some(a) => {
                    lemma_attributes_extend(s, end, uri_path, now, list.push(a));
                    assert(list.is_prefix_of(list.push(a))) by {
                        assert(list.push(a).subrange(0, list.len() as int) =~= list);
                    }
                    assert forall|i: int| 0 <= i < list.len() implies parse_attributes(s, pos, uri_path, now, list)[i]
                        == list[i] by {
                        let r = parse_attributes(s, end, uri_path, now, list.push(a));
                        assert(r.subrange(0, list.push(a).len() as int) =~= list.push(a));
                    }
                },
                None => lemma_attributes_extend(s, end, uri_path, now, list),
            }
        }
    } else {
        assert(list.subrange(0, list.len() as int) =~= list);
    }
}

/// §5.6 steps 7 and 8: no attribute already in the list is changed or
/// dropped, at every index.
pub proof fn lemma_attributes_keep(s: Seq<u8>, pos: nat, uri_path: Seq<u8>, now: int, list: Seq<Attribute>, i: int)
    ensures
        0 <= i < list.len() ==> (i < parse_attributes(s, pos, uri_path, now, list).len() && parse_attributes(
            s,
            pos,
            uri_path,
            now,
            list,
        )[i] == list[i]),
{
    lemma_attributes_extend(s, pos, uri_path, now, list);
    let result = parse_attributes(s, pos, uri_path, now, list);
    if 0 <= i < list.len() {
        assert(result.subrange(0, list.len() as int)[i] == list[i]);
    }
}

/// §5.4: a cookie whose name begins "__Secure-" in any case is ignored
/// without the secure-only-flag.
pub proof fn lemma_secure_prefix_needs_secure(cookie: SetCookie, host_only_flag: bool)
    requires
        crate::ascii::begins_with_case_insensitive_match(cookie.name, lit_secure_prefix()),
    ensures
        !name_prefix_requirements_met(cookie, false, host_only_flag),
{
}

/// §5.4: a cookie whose name begins "__Host-" in any case is kept only
/// with the secure-only-flag, the host-only-flag, and a Path attribute of
/// "/".
pub proof fn lemma_host_prefix_needs_all(cookie: SetCookie, secure_only_flag: bool, host_only_flag: bool)
    requires
        crate::ascii::begins_with_case_insensitive_match(cookie.name, lit_host_prefix()),
        name_prefix_requirements_met(cookie, secure_only_flag, host_only_flag),
    ensures
        secure_only_flag && host_only_flag && last_path_attribute(cookie.attributes) == Some(seq![0x2Fu8]),
{
}

} // verus!
