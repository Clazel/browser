//! Contracts the executable cookie-date functions must be proven to meet.
//! Each exec function's `ensures` clause is exactly one of these
//! predicates, so reviewing these (and [`super::spec`]) is enough to know
//! what the implementation guarantees.
//!
//! Strings are octets (`&[u8]`). An exec date is viewed as a
//! [`CookieDate`]; `None` is failure.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Contract for `parse_a_cookie_date(&[u8]) -> Option<DateRecord>`: equals
/// "parse a cookie-date" (§5.1.1).
pub open spec fn parse_a_cookie_date_ensures(input: Seq<u8>, output: Option<CookieDate>) -> bool {
    output == parse_a_cookie_date(input)
}

/// Precondition of `DateRecord::seconds_since_1601(&self) -> u64`: a year
/// from 1601 to 9999 and the fields of a date (a record
/// `parse_a_cookie_date` returns meets it,
/// `lemmas::lemma_parsed_date_in_range`).
pub open spec fn seconds_since_1601_requires(d: CookieDate) -> bool {
    1601 <= d.year <= 9999 && 1 <= d.month <= 12 && 1 <= d.day_of_month <= 31 && d.hour <= 23 && d.minute <= 59
        && d.second <= 59
}

/// Contract for `DateRecord::seconds_since_1601(&self) -> u64`: equals
/// [`seconds_since_1601`].
pub open spec fn seconds_since_1601_ensures(d: CookieDate, output: u64) -> bool {
    output as int == seconds_since_1601(d)
}

} // verus!
