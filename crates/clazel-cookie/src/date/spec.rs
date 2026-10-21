//! RFC 6265bis §5.1.1, "Dates": the cookie-date parser, transcribed. Nothing
//! here runs; it defines what "correct" means. Each `// N.` comment is the
//! step number in the cited algorithm.
//!
//! Source (pinned; a review is against exactly this text):
//! - draft-ietf-httpbis-rfc6265bis-22, "Cookies: HTTP State Management
//!   Mechanism", 1 December 2025 (the latest revision on 21 October 2026;
//!   it has not been published as an RFC),
//!   <https://www.ietf.org/archive/id/draft-ietf-httpbis-rfc6265bis-22.txt>:
//!   §5.1.1 Dates.
//!
//! Modelling choices (each one a deliberate deviation in form, never in
//! meaning):
//! - A string is a `Seq<u8>` of octets (see [`crate::ascii`]).
//! - Step 1 divides the cookie-date into date-tokens by its grammar:
//!   `cookie-date = *delimiter date-token-list *delimiter`, where the
//!   tokens are the maximal runs of non-delimiters. [`date_tokens`] reads
//!   the octets once, left to right, collecting a run until a delimiter. A
//!   cookie-date with no token at all does not match the grammar; here it
//!   has no tokens, so step 5 fails it because no flag is set. The result
//!   is the same: failure.
//! - Step 2 is a left fold over the tokens, carrying the four "found-"
//!   flags and values as [`DateState`]: a flag is set exactly when its
//!   `Option` is `Some`, holding the value.
//! - "matches the time production" (and likewise day-of-month, month,
//!   year) is a prefix test: each production is a run of digits or a name,
//!   then optionally a non-digit followed by any octets, so the token
//!   matches when the digit run found at the start has the allowed length
//!   (the run is maximal, and the next octet, if any, is then a non-digit).
//! - Numbers are `nat`. The widest field is a year of four digits.
//! - Step 6's "the date whose ... (in UTC) are ..." is the record
//!   [`CookieDate`]; "if no such date exists" is the day exceeding the
//!   month's length in the proleptic Gregorian calendar. [`seconds_since_1601`]
//!   converts a date to seconds since 1601-01-01T00:00:00Z (the earliest
//!   instant a cookie-date denotes, so every instant is non-negative); the standard never
//!   needs the conversion itself, the Set-Cookie algorithm (§5.6.1) does
//!   when it compares an expiry time to "now".
//! - Read literally, the grammar's `month` has no case rule, but ABNF
//!   quoted strings are case-insensitive (RFC 5234 §2.3), so "JAN" and
//!   "jan" both match.

#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// "The parsed-cookie-date": the day-of-month, month (1 to 12), year, hour,
/// minute and second of a date in UTC.
pub struct CookieDate {
    /// year-value.
    pub year: nat,
    /// month-value, 1 for January.
    pub month: nat,
    /// day-of-month-value.
    pub day_of_month: nat,
    /// hour-value.
    pub hour: nat,
    /// minute-value.
    pub minute: nat,
    /// second-value.
    pub second: nat,
}

// ---------------------------------------------------------------------
// Step 1: the grammar.
// ---------------------------------------------------------------------

/// `delimiter = %x09 / %x20-2F / %x3B-40 / %x5B-60 / %x7B-7E`
pub open spec fn is_delimiter(c: u8) -> bool {
    c == 0x09 || (0x20 <= c <= 0x2F) || (0x3B <= c <= 0x40) || (0x5B <= c <= 0x60) || (0x7B <= c <= 0x7E)
}

/// `non-delimiter = %x00-08 / %x0A-1F / DIGIT / ":" / ALPHA / %x7F-FF`
pub open spec fn is_non_delimiter(c: u8) -> bool {
    c <= 0x08 || (0x0A <= c <= 0x1F) || crate::ascii::is_digit(c) || c == 0x3A || crate::ascii::is_alpha(c) || c >= 0x7F
}

/// `non-digit = %x00-2F / %x3A-FF`
pub open spec fn is_non_digit(c: u8) -> bool {
    c <= 0x2F || c >= 0x3A
}

/// Step 1's division into date-tokens, `tokens_loop`: `current` is the
/// run being collected and `done` the tokens so far.
pub open spec fn tokens_loop(s: Seq<u8>, current: Seq<u8>, done: Seq<Seq<u8>>) -> Seq<Seq<u8>>
    decreases s.len()
{
    if s.len() == 0 {
        if current.len() > 0 { done.push(current) } else { done }
    } else if is_non_delimiter(s[0]) {
        tokens_loop(s.skip(1), current.push(s[0]), done)
    } else {
        tokens_loop(s.skip(1), seq![], if current.len() > 0 { done.push(current) } else { done })
    }
}

/// 1. "Using the grammar below, divide the cookie-date into date-tokens."
pub open spec fn date_tokens(input: Seq<u8>) -> Seq<Seq<u8>> {
    tokens_loop(input, seq![], seq![])
}

/// The number of consecutive DIGITs of `s` from index `start`.
pub open spec fn digit_run(s: Seq<u8>, start: nat) -> nat
    decreases s.len() - start
{
    if start < s.len() && crate::ascii::is_digit(s[start as int]) { 1 + digit_run(s, start + 1) } else { 0 }
}

/// `time-field = 1*2DIGIT` at `start`: its value and length.
pub open spec fn time_field(s: Seq<u8>, start: nat) -> Option<(nat, nat)> {
    let n = digit_run(s, start);
    if 1 <= n <= 2 { Some((crate::ascii::digits_value(s.subrange(start as int, (start + n) as int)), n)) } else { None }
}

/// `time = hms-time [ non-digit *OCTET ]`, `hms-time = time-field ":"
/// time-field ":" time-field`: the (hour, minute, second) of a token that
/// matches it.
pub open spec fn match_time(token: Seq<u8>) -> Option<(nat, nat, nat)> {
    match time_field(token, 0) {
        None => None,
        Some((h, n1)) => if !(n1 < token.len() && token[n1 as int] == 0x3A) {
            None
        } else {
            match time_field(token, n1 + 1) {
                None => None,
                Some((m, n2)) => if !(n1 + 1 + n2 < token.len() && token[(n1 + 1 + n2) as int] == 0x3A) {
                    None
                } else {
                    match time_field(token, n1 + n2 + 2) {
                        None => None,
                        Some((s, _)) => Some((h, m, s)),
                    }
                },
            }
        },
    }
}

/// `day-of-month = 1*2DIGIT [ non-digit *OCTET ]`: the number of a token
/// that matches it.
pub open spec fn match_day_of_month(token: Seq<u8>) -> Option<nat> {
    let n = digit_run(token, 0);
    if 1 <= n <= 2 { Some(crate::ascii::digits_value(token.subrange(0, n as int))) } else { None }
}

/// `year = 2*4DIGIT [ non-digit *OCTET ]`: the number of a token that
/// matches it.
pub open spec fn match_year(token: Seq<u8>) -> Option<nat> {
    let n = digit_run(token, 0);
    if 2 <= n <= 4 { Some(crate::ascii::digits_value(token.subrange(0, n as int))) } else { None }
}

/// The month an abbreviation names ("jan" to "dec", any case), 1 to 12.
pub open spec fn month_of_abbreviation(s: Seq<u8>) -> Option<nat> {
    let l = crate::ascii::ascii_lowercase(s);
    if l == seq![0x6Au8, 0x61, 0x6E] { Some(1) }       // jan
    else if l == seq![0x66u8, 0x65, 0x62] { Some(2) }  // feb
    else if l == seq![0x6Du8, 0x61, 0x72] { Some(3) }  // mar
    else if l == seq![0x61u8, 0x70, 0x72] { Some(4) }  // apr
    else if l == seq![0x6Du8, 0x61, 0x79] { Some(5) }  // may
    else if l == seq![0x6Au8, 0x75, 0x6E] { Some(6) }  // jun
    else if l == seq![0x6Au8, 0x75, 0x6C] { Some(7) }  // jul
    else if l == seq![0x61u8, 0x75, 0x67] { Some(8) }  // aug
    else if l == seq![0x73u8, 0x65, 0x70] { Some(9) }  // sep
    else if l == seq![0x6Fu8, 0x63, 0x74] { Some(10) } // oct
    else if l == seq![0x6Eu8, 0x6F, 0x76] { Some(11) } // nov
    else if l == seq![0x64u8, 0x65, 0x63] { Some(12) } // dec
    else { None }
}

/// `month = ( "jan" / ... / "dec" ) *OCTET`: the month of a token that
/// matches it.
pub open spec fn match_month(token: Seq<u8>) -> Option<nat> {
    if token.len() >= 3 { month_of_abbreviation(token.subrange(0, 3)) } else { None }
}

// ---------------------------------------------------------------------
// Step 2: process each date-token.
// ---------------------------------------------------------------------

/// The found-time, found-day-of-month, found-month and found-year flags
/// with the values set with them: a flag is set when its field is `Some`.
pub struct DateState {
    /// found-time, with (hour-value, minute-value, second-value).
    pub time: Option<(nat, nat, nat)>,
    /// found-day-of-month, with day-of-month-value.
    pub day_of_month: Option<nat>,
    /// found-month, with month-value.
    pub month: Option<nat>,
    /// found-year, with year-value.
    pub year: Option<nat>,
}

/// All four flags "not set".
pub open spec fn initial_state() -> DateState {
    DateState { time: None, day_of_month: None, month: None, year: None }
}

/// 2. Process one date-token.
pub open spec fn process_token(state: DateState, token: Seq<u8>) -> DateState {
    if state.time is None && match_time(token) is Some {
        // 2.1 "If the found-time flag is not set and the token matches the
        //     time production, set the found-time flag and set the hour-
        //     value, minute-value, and second-value to the numbers denoted
        //     by the digits in the date-token, respectively. Skip the
        //     remaining sub-steps and continue to the next date-token."
        DateState { time: match_time(token), ..state }
    } else if state.day_of_month is None && match_day_of_month(token) is Some {
        // 2.2 day-of-month, likewise.
        DateState { day_of_month: match_day_of_month(token), ..state }
    } else if state.month is None && match_month(token) is Some {
        // 2.3 month, likewise.
        DateState { month: match_month(token), ..state }
    } else if state.year is None && match_year(token) is Some {
        // 2.4 year, likewise.
        DateState { year: match_year(token), ..state }
    } else {
        // No sub-step applies: the token is skipped.
        state
    }
}

/// 2. "Process each date-token sequentially in the order the date-tokens
/// appear in the cookie-date", from token `i` on.
pub open spec fn process_tokens(tokens: Seq<Seq<u8>>, i: nat, state: DateState) -> DateState
    decreases tokens.len() - i
{
    if i >= tokens.len() { state } else { process_tokens(tokens, i + 1, process_token(state, tokens[i as int])) }
}

// ---------------------------------------------------------------------
// Calendar (step 6, "if no such date exists").
// ---------------------------------------------------------------------

/// A leap year of the proleptic Gregorian calendar.
pub open spec fn is_leap_year(y: nat) -> bool {
    y % 4 == 0 && (y % 100 != 0 || y % 400 == 0)
}

/// The number of days in month `m` (1 to 12) of year `y`.
pub open spec fn days_in_month(y: nat, m: nat) -> nat {
    if m == 2 {
        if is_leap_year(y) { 29 } else { 28 }
    } else if m == 4 || m == 6 || m == 9 || m == 11 {
        30
    } else {
        31
    }
}

// ---------------------------------------------------------------------
// The algorithm.
// ---------------------------------------------------------------------

/// §5.1.1 steps 3 and 4, on a year-value.
pub open spec fn two_digit_year_pivot(year_value: nat) -> nat {
    // 3. "If the year-value is greater than or equal to 70 and less than or
    //    equal to 99, increment the year-value by 1900."
    let year_value = if 70 <= year_value <= 99 { year_value + 1900 } else { year_value };
    // 4. "If the year-value is greater than or equal to 0 and less than or
    //    equal to 69, increment the year-value by 2000."
    if year_value <= 69 { year_value + 2000 } else { year_value }
}

/// §5.1.1 "parse a cookie-date": the date, or failure (`None`).
pub open spec fn parse_a_cookie_date(input: Seq<u8>) -> Option<CookieDate> {
    // 1. Divide into date-tokens. 2. Process each date-token.
    let state = process_tokens(date_tokens(input), 0, initial_state());
    // 5, first bullet: "at least one of the found-day-of-month,
    // found-month, found-year, or found-time flags is not set". (Checked
    // here, ahead of steps 3 and 4, which need the year-value; they change
    // nothing when a flag is missing, because the result is failure.)
    match (state.time, state.day_of_month, state.month, state.year) {
        (Some((hour, minute, second)), Some(day_of_month), Some(month), Some(year_value)) => {
            // 3. and 4.: the two-digit year pivot.
            let year_value = two_digit_year_pivot(year_value);
            // 5. "Abort this algorithm and fail to parse the cookie-date if:
            //    ... the day-of-month-value is less than 1 or greater than
            //    31, the year-value is less than 1601, the hour-value is
            //    greater than 23, the minute-value is greater than 59, or
            //    the second-value is greater than 59."
            if day_of_month < 1 || day_of_month > 31 || year_value < 1601 || hour > 23 || minute > 59 || second > 59 {
                None
            // 6. "Let the parsed-cookie-date be the date whose ... If no
            //    such date exists, abort this algorithm and fail to parse
            //    the cookie-date."
            } else if day_of_month > days_in_month(year_value, month) {
                None
            } else {
                // 7. "Return the parsed-cookie-date as the result of this
                //    algorithm."
                Some(CookieDate { year: year_value, month, day_of_month, hour, minute, second })
            }
        },
        _ => None,
    }
}

// ---------------------------------------------------------------------
// Instants.
// ---------------------------------------------------------------------

/// Days from 1601-01-01 to January 1 of year `y` (for `y >= 1601`): 365 per
/// year since 1601, plus the leap days in between. `(y - 1) / 4 - (y - 1)
/// / 100 + (y - 1) / 400` counts the leap years before `y`.
pub open spec fn days_before_year(y: int) -> int {
    // 388 is the leap years before 1601: 1600 / 4 - 1600 / 100 + 1600 / 400.
    365 * (y - 1601) + ((y - 1) / 4 - (y - 1) / 100 + (y - 1) / 400) - 388
}

/// Days from January 1 to the first of month `m` (1 to 12) of year `y`.
pub open spec fn days_before_month(y: nat, m: nat) -> int {
    let cumulative: int = if m == 1 { 0 }
        else if m == 2 { 31 }
        else if m == 3 { 59 }
        else if m == 4 { 90 }
        else if m == 5 { 120 }
        else if m == 6 { 151 }
        else if m == 7 { 181 }
        else if m == 8 { 212 }
        else if m == 9 { 243 }
        else if m == 10 { 273 }
        else if m == 11 { 304 }
        else { 334 };
    cumulative + if m > 2 && is_leap_year(y) { 1int } else { 0int }
}

/// Seconds since 1601-01-01T00:00:00Z of a date in UTC (for a year from
/// 1601).
pub open spec fn seconds_since_1601(d: CookieDate) -> int {
    (days_before_year(d.year as int) + days_before_month(d.year, d.month) + (d.day_of_month as int - 1)) * 86400
        + d.hour as int * 3600 + d.minute as int * 60 + d.second as int
}

} // verus!
