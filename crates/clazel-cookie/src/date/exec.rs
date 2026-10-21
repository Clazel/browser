//! The executable cookie-date parser, proven to meet [`super::contract`].
//!
//! The code mirrors the spec: [`date_tokens`] is step 1,
//! [`process_token_exec`] one pass of step 2, and [`parse_a_cookie_date`]
//! steps 3 to 7. Each is proven equal to its spec function, so the step
//! comments live in [`super::spec`].

#[allow(unused_imports)]
use super::spec::*;
use crate::strings::{ascii_lowercase_exec, at, is_digit_exec};
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// A parsed cookie-date, viewed as [`CookieDate`].
pub struct DateRecord {
    /// year-value.
    pub year: u32,
    /// month-value, 1 for January.
    pub month: u32,
    /// day-of-month-value.
    pub day_of_month: u32,
    /// hour-value.
    pub hour: u32,
    /// minute-value.
    pub minute: u32,
    /// second-value.
    pub second: u32,
}

impl View for DateRecord {
    type V = CookieDate;

    open spec fn view(&self) -> CookieDate {
        CookieDate {
            year: self.year as nat,
            month: self.month as nat,
            day_of_month: self.day_of_month as nat,
            hour: self.hour as nat,
            minute: self.minute as nat,
            second: self.second as nat,
        }
    }
}

/// The view of an optional date; `None` is failure.
pub open spec fn option_view(d: Option<DateRecord>) -> Option<CookieDate> {
    match d {
        Some(d) => Some(d@),
        None => None,
    }
}

/// The date-tokens of an exec token list, viewed.
pub open spec fn tokens_view(v: Seq<Vec<u8>>) -> Seq<Seq<u8>> {
    v.map_values(|t: Vec<u8>| t@)
}

/// The found-flags and values of step 2.
pub struct DateStateExec {
    /// found-time, with (hour-value, minute-value, second-value).
    pub time: Option<(u32, u32, u32)>,
    /// found-day-of-month, with day-of-month-value.
    pub day_of_month: Option<u32>,
    /// found-month, with month-value.
    pub month: Option<u32>,
    /// found-year, with year-value.
    pub year: Option<u32>,
}

/// A number option, viewed.
pub open spec fn nat_option(o: Option<u32>) -> Option<nat> {
    match o {
        Some(v) => Some(v as nat),
        None => None,
    }
}

/// A time option, viewed.
pub open spec fn time_option(o: Option<(u32, u32, u32)>) -> Option<(nat, nat, nat)> {
    match o {
        Some((h, m, s)) => Some((h as nat, m as nat, s as nat)),
        None => None,
    }
}

impl View for DateStateExec {
    type V = DateState;

    open spec fn view(&self) -> DateState {
        DateState {
            time: time_option(self.time),
            day_of_month: nat_option(self.day_of_month),
            month: nat_option(self.month),
            year: nat_option(self.year),
        }
    }
}

// ---------------------------------------------------------------------
// Step 1: date-tokens.
// ---------------------------------------------------------------------

/// [`is_non_delimiter`].
fn is_non_delimiter_exec(c: u8) -> (r: bool)
    ensures
        r == is_non_delimiter(c),
{
    c <= 0x08 || (0x0A..=0x1F).contains(&c) || is_digit_exec(c) || c == 0x3A
        || (0x41..=0x5A).contains(&c) || (0x61..=0x7A).contains(&c) || c >= 0x7F
}

/// Step 1: divide the cookie-date into date-tokens.
pub fn date_tokens_exec(input: &[u8]) -> (out: Vec<Vec<u8>>)
    ensures
        tokens_view(out@) == date_tokens(input@),
{
    let mut done: Vec<Vec<u8>> = Vec::new();
    let mut current: Vec<u8> = Vec::new();
    let mut i: usize = 0;
    assert(input@.skip(0) =~= input@);
    assert(tokens_view(done@) =~= Seq::<Seq<u8>>::empty());
    assert(current@ =~= Seq::<u8>::empty());
    while i < input.len()
        invariant
            i <= input.len(),
            tokens_loop(input@.skip(i as int), current@, tokens_view(done@)) == date_tokens(input@),
        decreases input.len() - i,
    {
        let c = match input.get(i) {
            Some(c) => *c,
            None => 0,
        };
        let ghost s = input@.skip(i as int);
        let ghost current_before = current@;
        let ghost done_before = tokens_view(done@);
        assert(s[0] == c);
        assert(s.skip(1) =~= input@.skip(i as int + 1));
        if is_non_delimiter_exec(c) {
            current.push(c);
            assert(current@ == current_before.push(c));
        } else if !current.is_empty() {
            done.push(current);
            assert(tokens_view(done@) =~= done_before.push(current_before));
            current = Vec::new();
            assert(current@ =~= Seq::<u8>::empty());
        } else {
            assert(current_before =~= Seq::<u8>::empty());
            assert(done_before =~= tokens_view(done@));
        }
        reveal_with_fuel(tokens_loop, 2);
        assert(tokens_loop(s, current_before, done_before) == tokens_loop(
            input@.skip(i as int + 1),
            current@,
            tokens_view(done@),
        ));
        // Never saturates: i < input.len().
        i = i.saturating_add(1);
    }
    assert(input@.skip(input.len() as int) =~= Seq::<u8>::empty());
    if !current.is_empty() {
        let ghost done_before = tokens_view(done@);
        let ghost current_before = current@;
        done.push(current);
        assert(tokens_view(done@) =~= done_before.push(current_before));
    }
    done
}

// ---------------------------------------------------------------------
// Numbers in tokens.
// ---------------------------------------------------------------------

/// The number of consecutive DIGITs of `s` from index `start`.
fn digit_run_exec(s: &[u8], start: usize) -> (r: usize)
    ensures
        r == digit_run(s@, start as nat),
{
    if start >= s.len() {
        return 0;
    }
    let mut i = start;
    while i < s.len() && is_digit_exec(match s.get(i) {
        Some(c) => *c,
        None => 0,
    })
        invariant
            start <= i <= s.len(),
            digit_run(s@, start as nat) == (i - start) + digit_run(s@, i as nat),
        decreases s.len() - i,
    {
        // Never saturates: i < s.len().
        i = i.saturating_add(1);
    }
    assert(i >= s.len() || !crate::ascii::is_digit(s@[i as int]));
    // Never saturates: start <= i.
    i.saturating_sub(start)
}

/// The number `s[start..start + n]` denotes, for at most four digits.
fn digits_value_exec(s: &[u8], start: usize, n: usize) -> (r: u32)
    requires
        n <= 4,
        start + n <= s.len(),
        forall|k: int| start <= k < start + n ==> crate::ascii::is_digit(#[trigger] s@[k]),
    ensures
        r as nat == crate::ascii::digits_value(s@.subrange(start as int, (start + n) as int)),
{
    let mut acc: u32 = 0;
    let mut j: usize = 0;
    assert(s@.subrange(start as int, start as int) =~= Seq::<u8>::empty());
    while j < n
        invariant
            j <= n,
            n <= 4,
            start + n <= s.len(),
            forall|k: int| start <= k < start + n ==> crate::ascii::is_digit(#[trigger] s@[k]),
            acc as nat == crate::ascii::digits_value(s@.subrange(start as int, (start + j) as int)),
            j == 0 ==> acc == 0,
            j <= 1 ==> acc < 10,
            j <= 2 ==> acc < 100,
            j <= 3 ==> acc < 1000,
            acc < 10000,
        decreases n - j,
    {
        // Never saturates: start + j < s.len().
        let d = match s.get(start.saturating_add(j)) {
            Some(c) => (*c).saturating_sub(0x30),
            None => 0,
        };
        assert(s@.subrange(start as int, (start + j + 1) as int).drop_last() =~= s@.subrange(start as int, (start + j) as int));
        assert(s@.subrange(start as int, (start + j + 1) as int).last() == s@[(start + j) as int]);
        acc =acc.saturating_mul(10).saturating_add(d as u32);
        // Never saturates: j < n.
        j = j.saturating_add(1);
    }
    acc
}

/// A number and its digit count, viewed.
pub open spec fn field_view(o: Option<(u32, usize)>) -> Option<(nat, nat)> {
    match o {
        Some((v, n)) => Some((v as nat, n as nat)),
        None => None,
    }
}

/// `time-field = 1*2DIGIT` at `start`: its value and length.
fn time_field_exec(s: &[u8], start: usize) -> (r: Option<(u32, usize)>)
    ensures
        field_view(r) == time_field(s@, start as nat),
{
    let n = digit_run_exec(s, start);
    if (1..=2).contains(&n) {
        proof {
            lemma_digit_run_digits(s@, start as nat);
        }
        let v = digits_value_exec(s, start, n);
        Some((v, n))
    } else {
        None
    }
}

/// The octets counted by `digit_run` are digits, and they are in range.
proof fn lemma_digit_run_digits(s: Seq<u8>, start: nat)
    ensures
        start + digit_run(s, start) <= s.len() || digit_run(s, start) == 0,
        forall|k: int| start <= k < start + digit_run(s, start) ==> crate::ascii::is_digit(#[trigger] s[k]),
    decreases s.len() - start
{
    if start < s.len() && crate::ascii::is_digit(s[start as int]) {
        lemma_digit_run_digits(s, start + 1);
    }
}

/// `time = hms-time [ non-digit *OCTET ]`.
fn match_time_exec(token: &[u8]) -> (r: Option<(u32, u32, u32)>)
    ensures
        time_option(r) == match_time(token@),
{
    let (h, n1) = time_field_exec(token, 0)?;
    if at(token, n1) != Some(0x3A) {
        return None;
    }
    // Never saturates: n1 <= 2.
    let (m, n2) = time_field_exec(token, n1.saturating_add(1))?;
    let p = n1.saturating_add(1).saturating_add(n2);
    if at(token, p) != Some(0x3A) {
        return None;
    }
    // Never saturates: p <= 5.
    let (s, _) = time_field_exec(token, p.saturating_add(1))?;
    Some((h, m, s))
}

/// `day-of-month = 1*2DIGIT [ non-digit *OCTET ]`.
fn match_day_of_month_exec(token: &[u8]) -> (r: Option<u32>)
    ensures
        nat_option(r) == match_day_of_month(token@),
{
    let n = digit_run_exec(token, 0);
    if (1..=2).contains(&n) {
        proof {
            lemma_digit_run_digits(token@, 0);
        }
        Some(digits_value_exec(token, 0, n))
    } else {
        None
    }
}

/// `year = 2*4DIGIT [ non-digit *OCTET ]`.
fn match_year_exec(token: &[u8]) -> (r: Option<u32>)
    ensures
        nat_option(r) == match_year(token@),
{
    let n = digit_run_exec(token, 0);
    if (2..=4).contains(&n) {
        proof {
            lemma_digit_run_digits(token@, 0);
        }
        Some(digits_value_exec(token, 0, n))
    } else {
        None
    }
}

/// Is the three-octet string `l` equal to `seq![a, b, c]`?
fn eq3(l: &[u8], a: u8, b: u8, c: u8) -> (r: bool)
    requires
        l@.len() == 3,
    ensures
        r == (l@ == seq![a, b, c]),
{
    let r = at(l, 0) == Some(a) && at(l, 1) == Some(b) && at(l, 2) == Some(c);
    if r {
        assert(l@ =~= seq![a, b, c]);
    }
    r
}

/// The month an abbreviation names.
fn month_of_abbreviation_exec(s: &[u8]) -> (r: Option<u32>)
    requires
        s@.len() == 3,
    ensures
        nat_option(r) == month_of_abbreviation(s@),
{
    let l = ascii_lowercase_exec(s);
    assert(l@.len() == 3) by {
        assert(crate::ascii::ascii_lowercase(s@).len() == s@.len());
    }
    let l = l.as_slice();
    if eq3(l, 0x6A, 0x61, 0x6E) {
        Some(1)
    } else if eq3(l, 0x66, 0x65, 0x62) {
        Some(2)
    } else if eq3(l, 0x6D, 0x61, 0x72) {
        Some(3)
    } else if eq3(l, 0x61, 0x70, 0x72) {
        Some(4)
    } else if eq3(l, 0x6D, 0x61, 0x79) {
        Some(5)
    } else if eq3(l, 0x6A, 0x75, 0x6E) {
        Some(6)
    } else if eq3(l, 0x6A, 0x75, 0x6C) {
        Some(7)
    } else if eq3(l, 0x61, 0x75, 0x67) {
        Some(8)
    } else if eq3(l, 0x73, 0x65, 0x70) {
        Some(9)
    } else if eq3(l, 0x6F, 0x63, 0x74) {
        Some(10)
    } else if eq3(l, 0x6E, 0x6F, 0x76) {
        Some(11)
    } else if eq3(l, 0x64, 0x65, 0x63) {
        Some(12)
    } else {
        None
    }
}

/// `month = ( "jan" / ... / "dec" ) *OCTET`.
fn match_month_exec(token: &[u8]) -> (r: Option<u32>)
    ensures
        nat_option(r) == match_month(token@),
{
    if token.len() >= 3 {
        month_of_abbreviation_exec(vstd::slice::slice_subrange(token, 0, 3))
    } else {
        None
    }
}

// ---------------------------------------------------------------------
// Step 2.
// ---------------------------------------------------------------------

/// Step 2: process one date-token.
pub fn process_token_exec(state: &DateStateExec, token: &[u8]) -> (out: DateStateExec)
    ensures
        out@ == process_token(state@, token@),
{
    if state.time.is_none() {
        let t = match_time_exec(token);
        if t.is_some() {
            return DateStateExec { time: t, day_of_month: state.day_of_month, month: state.month, year: state.year };
        }
    }
    if state.day_of_month.is_none() {
        let d = match_day_of_month_exec(token);
        if d.is_some() {
            return DateStateExec { time: state.time, day_of_month: d, month: state.month, year: state.year };
        }
    }
    if state.month.is_none() {
        let m = match_month_exec(token);
        if m.is_some() {
            return DateStateExec { time: state.time, day_of_month: state.day_of_month, month: m, year: state.year };
        }
    }
    if state.year.is_none() {
        let y = match_year_exec(token);
        if y.is_some() {
            return DateStateExec { time: state.time, day_of_month: state.day_of_month, month: state.month, year: y };
        }
    }
    DateStateExec { time: state.time, day_of_month: state.day_of_month, month: state.month, year: state.year }
}

// ---------------------------------------------------------------------
// Calendar.
// ---------------------------------------------------------------------

/// [`is_leap_year`].
pub fn is_leap_year_exec(y: u32) -> (r: bool)
    ensures
        r == is_leap_year(y as nat),
{
    y.checked_rem(4) == Some(0) && (y.checked_rem(100) != Some(0) || y.checked_rem(400) == Some(0))
}

/// [`days_in_month`].
pub fn days_in_month_exec(y: u32, m: u32) -> (r: u32)
    ensures
        r as nat == days_in_month(y as nat, m as nat),
{
    if m == 2 {
        if is_leap_year_exec(y) { 29 } else { 28 }
    } else if m == 4 || m == 6 || m == 9 || m == 11 {
        30
    } else {
        31
    }
}

// ---------------------------------------------------------------------
// The algorithm.
// ---------------------------------------------------------------------

/// §5.1.1 "parse a cookie-date".
pub fn parse_a_cookie_date(input: &[u8]) -> (output: Option<DateRecord>)
    ensures
        super::contract::parse_a_cookie_date_ensures(input@, option_view(output)),
{
    // 1. Divide into date-tokens.
    let tokens = date_tokens_exec(input);
    // 2. Process each date-token.
    let mut state = DateStateExec { time: None, day_of_month: None, month: None, year: None };
    assert(state@ == initial_state());
    let ghost token_view = tokens_view(tokens@);
    let mut i: usize = 0;
    while i < tokens.len()
        invariant
            i <= tokens.len(),
            token_view == tokens_view(tokens@),
            process_tokens(token_view, 0, initial_state()) == process_tokens(token_view, i as nat, state@),
        decreases tokens.len() - i,
    {
        if let Some(token) = tokens.get(i) {
            state = process_token_exec(&state, token.as_slice());
        }
        // Never saturates: i < tokens.len().
        i = i.saturating_add(1);
    }
    match (state.time, state.day_of_month, state.month, state.year) {
        (Some((hour, minute, second)), Some(day_of_month), Some(month), Some(year_value)) => {
            // 3.
            let year_value = if (70..=99).contains(&year_value) { year_value.saturating_add(1900) } else { year_value };
            // 4.
            let year_value = if year_value <= 69 { year_value.saturating_add(2000) } else { year_value };
            // 5.
            // 6. ("If no such date exists": the same outcome, failure.)
            if !(1..=31).contains(&day_of_month) || year_value < 1601 || hour > 23 || minute > 59 || second > 59
                || day_of_month > days_in_month_exec(year_value, month)
            {
                None
            } else {
                // 7.
                Some(DateRecord { year: year_value, month, day_of_month, hour, minute, second })
            }
        },
        _ => None,
    }
}

// ---------------------------------------------------------------------
// Instants.
// ---------------------------------------------------------------------

impl DateRecord {
    /// Seconds since 1601-01-01T00:00:00Z of this date in UTC.
    pub fn seconds_since_1601(&self) -> (output: u64)
        requires
            super::contract::seconds_since_1601_requires(self@),
        ensures
            super::contract::seconds_since_1601_ensures(self@, output),
    {
        let y = self.year as u64;
        let before = y.saturating_sub(1);
        let leap_days = (before / 4).saturating_sub(before / 100).saturating_add(before / 400);
        // Never saturates: the year is at least 1601, so the leap years
        // before it number at least 388.
        let days_before_year = 365u64.saturating_mul(y.saturating_sub(1601)).saturating_add(leap_days).saturating_sub(388);
        let cumulative: u64 = match self.month {
            1 => 0,
            2 => 31,
            3 => 59,
            4 => 90,
            5 => 120,
            6 => 151,
            7 => 181,
            8 => 212,
            9 => 243,
            10 => 273,
            11 => 304,
            _ => 334,
        };
        let leap_day: u64 = if self.month > 2 && is_leap_year_exec(self.year) { 1 } else { 0 };
        let days = days_before_year
            .saturating_add(cumulative)
            .saturating_add(leap_day)
            .saturating_add(self.day_of_month as u64)
            .saturating_sub(1);
        days.saturating_mul(86400)
            .saturating_add((self.hour as u64).saturating_mul(3600))
            .saturating_add((self.minute as u64).saturating_mul(60))
            .saturating_add(self.second as u64)
    }
}

} // verus!
