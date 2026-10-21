//! Contracts the executable Set-Cookie functions must be proven to meet.
//! Each exec function's `ensures` clause is exactly one of these
//! predicates, so reviewing these (and [`super::spec`]) is enough to know
//! what the implementation guarantees.
//!
//! Strings are octets (`&[u8]`). An exec cookie is viewed as a
//! [`SetCookie`]; `None` is "ignore the set-cookie-string entirely". Time
//! is seconds since 1601-01-01T00:00:00Z (`u64`).

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The times `parse_a_set_cookie_string` accepts for "now": from the
/// earliest representable date to the end of year 9999 (in seconds since
/// 1601), which keeps every instant it computes (now plus the lifetime
/// limit) within a `u64`.
pub open spec fn now_in_range(now: int) -> bool {
    earliest_representable() <= now <= 265046774399
}

/// Precondition of `parse_a_set_cookie_string(&[u8], &[u8], u64) ->
/// Option<SetCookie>`.
pub open spec fn parse_a_set_cookie_string_requires(s: Seq<u8>, uri_path: Seq<u8>, now: int) -> bool {
    now_in_range(now)
}

/// Contract for `parse_a_set_cookie_string(&[u8], &[u8], u64) ->
/// Option<SetCookie>`: equals "parse a set-cookie-string" (§5.6), for a
/// request whose URL has path `uri_path`, at time `now`.
pub open spec fn parse_a_set_cookie_string_ensures(
    s: Seq<u8>,
    uri_path: Seq<u8>,
    now: int,
    output: Option<SetCookie>,
) -> bool {
    output == parse_a_set_cookie_string(s, uri_path, now)
}

/// Contract for `name_prefix_requirements_met(&SetCookie, bool, bool) ->
/// bool`: equals the spec predicate (§5.4, §5.7 steps 20 to 22).
pub open spec fn name_prefix_requirements_met_ensures(
    cookie: SetCookie,
    secure_only_flag: bool,
    host_only_flag: bool,
    output: bool,
) -> bool {
    output == name_prefix_requirements_met(cookie, secure_only_flag, host_only_flag)
}

} // verus!
