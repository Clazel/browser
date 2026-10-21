//! Facts proven about [`super::spec`]. They are evidence that the
//! transcription is right (for example that the calendar arithmetic counts
//! days), not part of what the implementation must meet.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------
// The grammar.
// ---------------------------------------------------------------------

/// §5.1.1 step 1's `delimiter` and `non-delimiter` productions are
/// complements: every octet is exactly one of them, as the tokenizer
/// assumes.
pub proof fn lemma_delimiter_complement(c: u8)
    ensures
        is_delimiter(c) != is_non_delimiter(c),
{
}

// ---------------------------------------------------------------------
// Ranges of what the parser returns.
// ---------------------------------------------------------------------

/// `10^n`.
pub open spec fn pow10(n: nat) -> nat
    decreases n
{
    if n == 0 { 1 } else { 10 * pow10((n - 1) as nat) }
}

/// A string of `n` digits denotes a number below `10^n`.
pub proof fn lemma_digits_value_bound(s: Seq<u8>)
    requires
        forall|i: int| 0 <= i < s.len() ==> crate::ascii::is_digit(#[trigger] s[i]),
    ensures
        crate::ascii::digits_value(s) < pow10(s.len()),
    decreases s.len()
{
    if s.len() > 0 {
        let t = s.drop_last();
        assert forall|i: int| 0 <= i < t.len() implies crate::ascii::is_digit(#[trigger] t[i]) by {
            assert(t[i] == s[i]);
        }
        lemma_digits_value_bound(t);
    }
}

/// The numbers `match_*` return are at most 9999 (four digits at most).
pub proof fn lemma_match_year_bound(token: Seq<u8>)
    ensures
        match_year(token) matches Some(y) ==> y <= 9999,
        match_day_of_month(token) matches Some(d) ==> d <= 99,
{
    let n = digit_run(token, 0);
    lemma_digit_run_all_digits(token, 0);
    if 1 <= n <= 4 {
        let digits = token.subrange(0, n as int);
        assert forall|i: int| 0 <= i < digits.len() implies crate::ascii::is_digit(#[trigger] digits[i]) by {
            assert(digits[i] == token[i]);
        }
        lemma_digits_value_bound(digits);
        reveal_with_fuel(pow10, 5);
    }
}

/// The octets `digit_run` counts are digits.
pub proof fn lemma_digit_run_all_digits(s: Seq<u8>, start: nat)
    ensures
        forall|k: int| start <= k < start + digit_run(s, start) ==> crate::ascii::is_digit(#[trigger] s[k]),
        start + digit_run(s, start) <= s.len() || digit_run(s, start) == 0,
    decreases s.len() - start
{
    if start < s.len() && crate::ascii::is_digit(s[start as int]) {
        lemma_digit_run_all_digits(s, start + 1);
    }
}

/// The month an abbreviation names is from 1 to 12.
pub proof fn lemma_month_range(s: Seq<u8>)
    ensures
        month_of_abbreviation(s) matches Some(m) ==> 1 <= m <= 12,
{
}

/// The fields `process_token` may set are in range.
pub open spec fn state_in_range(state: DateState) -> bool {
    (state.month matches Some(m) ==> 1 <= m <= 12) && (state.year matches Some(y) ==> y <= 9999)
}

/// Processing a token keeps the state in range.
pub proof fn lemma_process_token_in_range(state: DateState, token: Seq<u8>)
    requires
        state_in_range(state),
    ensures
        state_in_range(process_token(state, token)),
{
    lemma_match_year_bound(token);
    if token.len() >= 3 {
        lemma_month_range(token.subrange(0, 3));
    }
}

/// Processing tokens keeps the state in range.
pub proof fn lemma_process_tokens_in_range(tokens: Seq<Seq<u8>>, i: nat, state: DateState)
    requires
        state_in_range(state),
    ensures
        state_in_range(process_tokens(tokens, i, state)),
    decreases tokens.len() - i
{
    if i < tokens.len() {
        lemma_process_token_in_range(state, tokens[i as int]);
        lemma_process_tokens_in_range(tokens, i + 1, process_token(state, tokens[i as int]));
    }
}

/// A parsed cookie-date is a date in the range the conversion to seconds
/// accepts: a year from 1601 to 9999, a month, a day within the month, and
/// a time of day.
pub proof fn lemma_parsed_date_in_range(input: Seq<u8>)
    ensures
        parse_a_cookie_date(input) matches Some(d) ==> (super::contract::seconds_since_1601_requires(d)
            && d.day_of_month <= days_in_month(d.year, d.month)),
{
    let state = process_tokens(date_tokens(input), 0, initial_state());
    lemma_process_tokens_in_range(date_tokens(input), 0, initial_state());
    assert(state_in_range(state));
}

// ---------------------------------------------------------------------
// The calendar: consecutive days are 86400 seconds apart.
// ---------------------------------------------------------------------

/// January 1 of the next year is a year's length of days after January 1
/// of the year.
pub proof fn lemma_days_before_year_step(y: nat)
    requires
        y >= 1601,
    ensures
        days_before_year(y as int + 1) == days_before_year(y as int) + (if is_leap_year(y) { 366int } else { 365int }),
{
    let n = y as int;
    // Each count of leap years moves by one exactly at a multiple.
    assert(n / 4 - (n - 1) / 4 == if n % 4 == 0 { 1int } else { 0int }) by (nonlinear_arith)
        requires n >= 1601;
    assert(n / 100 - (n - 1) / 100 == if n % 100 == 0 { 1int } else { 0int }) by (nonlinear_arith)
        requires n >= 1601;
    assert(n / 400 - (n - 1) / 400 == if n % 400 == 0 { 1int } else { 0int }) by (nonlinear_arith)
        requires n >= 1601;
}

/// No date before 1601-01-01 is counted: the days before a year from 1601
/// are non-negative.
pub proof fn lemma_days_before_year_nonnegative(y: nat)
    requires
        y >= 1601,
    ensures
        days_before_year(y as int) >= 0,
    decreases y - 1601
{
    if y > 1601 {
        lemma_days_before_year_nonnegative((y - 1) as nat);
        lemma_days_before_year_step((y - 1) as nat);
    }
}

/// The instant of a date from 1601 is not negative.
pub proof fn lemma_seconds_nonnegative(d: CookieDate)
    requires
        d.year >= 1601,
        1 <= d.month <= 12,
        1 <= d.day_of_month,
    ensures
        seconds_since_1601(d) >= 0,
{
    lemma_days_before_year_nonnegative(d.year);
}

/// The first of a month is the previous month's length after the first of
/// the previous month.
pub proof fn lemma_days_before_month_step(y: nat, m: nat)
    requires
        1 <= m <= 11,
    ensures
        days_before_month(y, m + 1) == days_before_month(y, m) + days_in_month(y, m),
{
}

/// The next calendar day of a date.
pub open spec fn next_day(d: CookieDate) -> CookieDate {
    if d.day_of_month < days_in_month(d.year, d.month) {
        CookieDate { day_of_month: d.day_of_month + 1, ..d }
    } else if d.month < 12 {
        CookieDate { month: d.month + 1, day_of_month: 1, ..d }
    } else {
        CookieDate { year: d.year + 1, month: 1, day_of_month: 1, ..d }
    }
}

/// The conversion to seconds counts days: the next calendar day, at the
/// same time of day, is 86400 seconds later. (With the first date,
/// 1601-01-01T00:00:00Z at 0, this fixes every instant.)
pub proof fn lemma_next_day_adds_86400(d: CookieDate)
    requires
        d.year >= 1601,
        1 <= d.month <= 12,
        1 <= d.day_of_month <= days_in_month(d.year, d.month),
    ensures
        seconds_since_1601(next_day(d)) == seconds_since_1601(d) + 86400,
{
    if d.day_of_month < days_in_month(d.year, d.month) {
    } else if d.month < 12 {
        lemma_days_before_month_step(d.year, d.month);
    } else {
        lemma_days_before_year_step(d.year);
        // December starts 334 days (335 in a leap year) into the year, and
        // has 31 days.
        assert(days_before_month(d.year, 12) + 31 == if is_leap_year(d.year) { 366int } else { 365int });
    }
}

/// 1601-01-01T00:00:00Z is instant 0, the earliest representable.
pub proof fn lemma_epoch_is_zero()
    ensures
        seconds_since_1601(CookieDate { year: 1601, month: 1, day_of_month: 1, hour: 0, minute: 0, second: 0 }) == 0,
{
}

/// The two-digit year pivot of steps 3 and 4: 70 to 99 are 1970 to 1999
/// and 0 to 69 are 2000 to 2069 (RFC 6265bis §5.1.1 notes that other user
/// agents differ).
pub proof fn lemma_two_digit_year_pivot()
    ensures
        two_digit_year_pivot(70) == 1970,
        two_digit_year_pivot(99) == 1999,
        two_digit_year_pivot(0) == 2000,
        two_digit_year_pivot(69) == 2069,
        forall|y: nat| 100 <= y ==> two_digit_year_pivot(y) == y,
{
}

/// "nov" names November.
pub proof fn lemma_november()
    ensures
        month_of_abbreviation(seq![0x4Eu8, 0x6F, 0x76]) == Some(11nat),
{
    assert(crate::ascii::ascii_lowercase(seq![0x4Eu8, 0x6F, 0x76]) =~= seq![0x6Eu8, 0x6F, 0x76]);
}

} // verus!
