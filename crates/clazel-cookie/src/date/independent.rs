//! A second transcription of what a date string means, from RFC 9110
//! §5.6.7 (the HTTP-date grammar), and a proof that [`super::spec`]'s
//! cookie-date parser reads every HTTP-date as RFC 9110 does.
//!
//! RFC 9110 defines three formats (IMF-fixdate, the obsolete RFC 850 and
//! asctime forms) by grammar only; it says what a string denotes, and it
//! was written by a different body, in 2022, for a different protocol
//! field. This file transcribes that grammar as three builders, one per
//! format, from the fields of a date to the string the grammar produces
//! (so "every string in the grammar" is "the builder applied to every
//! value of the fields the grammar allows"), and the calendar those fields
//! denote.
//!
//! What is proven (`lemma_imf_fixdate_agrees`, `lemma_asctime_agrees`,
//! `lemma_rfc850_agrees`): on every string the grammar produces, the
//! cookie-date parser returns the date the fields denote when they denote
//! one a cookie-date can represent, and fails otherwise. The class and its
//! limits:
//! - **Years.** IMF-fixdate and asctime have a four-digit year, and the
//!   statement covers years 100 to 9999. A four-digit year below 100
//!   ("0094") is a two-digit year to the cookie-date algorithm (§5.1.1
//!   steps 3 and 4 add 1900 or 2000), so it is read differently, and years
//!   below 1601 fail in any case.
//! - **Two-digit years (RFC 850).** RFC 9110 reads a two-digit year
//!   relative to the current time ("more than 50 years in the future"), so
//!   no function of the string alone agrees with it. The cookie algorithm
//!   fixes a pivot (70 to 99 are 19xx, 0 to 69 are 20xx), and the lemma
//!   states that: it holds for the pivot, not for RFC 9110's rule.
//! - **Leap seconds.** RFC 9110's `time-of-day` allows second 60; a
//!   cookie-date cannot represent one (§5.1.1 step 5), so the parse
//!   fails. The calendar below denotes no date for second 60.
//! - **Day names.** The grammar fixes a day name but does not tie it to
//!   the date; neither does the cookie algorithm, which ignores it.
//! - HTTP-date is case sensitive; the cookie algorithm is not. The lemma
//!   concerns strings the case-sensitive grammar produces, so this is not
//!   tested here, only that no capitalization of the grammar is rejected.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------
// Tokenization of a string built from tokens and separators.
// ---------------------------------------------------------------------

/// Every octet of `s` is a delimiter (§5.1.1 step 1).
pub open spec fn all_delimiters(s: Seq<u8>) -> bool {
    forall|i: int| 0 <= i < s.len() ==> is_delimiter(#[trigger] s[i])
}

/// Every octet of `s` is a non-delimiter.
pub open spec fn all_non_delimiters(s: Seq<u8>) -> bool {
    forall|i: int| 0 <= i < s.len() ==> is_non_delimiter(#[trigger] s[i])
}

/// What `tokens_loop` does with the run being collected at a delimiter.
pub open spec fn flush(current: Seq<u8>, done: Seq<Seq<u8>>) -> Seq<Seq<u8>> {
    if current.len() > 0 { done.push(current) } else { done }
}

/// A run of delimiters ends the current run and starts none.
proof fn lemma_loop_delimiters(sep: Seq<u8>, rest: Seq<u8>, current: Seq<u8>, done: Seq<Seq<u8>>)
    requires
        sep.len() > 0,
        all_delimiters(sep),
    ensures
        tokens_loop(sep + rest, current, done) == tokens_loop(rest, seq![], flush(current, done)),
    decreases sep.len()
{
    let all = sep + rest;
    assert(all[0] == sep[0]);
    assert(is_delimiter(sep[0]));
    assert(!is_non_delimiter(sep[0]));
    assert(all.skip(1) =~= sep.skip(1) + rest);
    if sep.len() > 1 {
        let s1 = sep.skip(1);
        assert forall|i: int| 0 <= i < s1.len() implies is_delimiter(#[trigger] s1[i]) by {
            assert(s1[i] == sep[i + 1]);
        }
        lemma_loop_delimiters(s1, rest, seq![], flush(current, done));
        assert(flush(seq![], flush(current, done)) == flush(current, done));
    } else {
        assert(sep.skip(1) =~= Seq::<u8>::empty());
        assert(all.skip(1) =~= rest);
    }
}

/// A run of non-delimiters extends the current run.
proof fn lemma_loop_token(t: Seq<u8>, rest: Seq<u8>, current: Seq<u8>, done: Seq<Seq<u8>>)
    requires
        all_non_delimiters(t),
    ensures
        tokens_loop(t + rest, current, done) == tokens_loop(rest, current + t, done),
    decreases t.len()
{
    if t.len() == 0 {
        assert(t + rest =~= rest);
        assert(current + t =~= current);
    } else {
        let all = t + rest;
        assert(all[0] == t[0]);
        assert(all.skip(1) =~= t.skip(1) + rest);
        let t1 = t.skip(1);
        assert forall|i: int| 0 <= i < t1.len() implies is_non_delimiter(#[trigger] t1[i]) by {
            assert(t1[i] == t[i + 1]);
        }
        lemma_loop_token(t1, rest, current.push(t[0]), done);
        assert(current.push(t[0]) + t1 =~= current + t);
    }
}

/// The tokens already collected only come first.
proof fn lemma_loop_done_prefix(s: Seq<u8>, current: Seq<u8>, done: Seq<Seq<u8>>)
    ensures
        tokens_loop(s, current, done) == done + tokens_loop(s, current, seq![]),
    decreases s.len()
{
    if s.len() == 0 {
        assert(done.push(current) =~= done + seq![current]);
        assert(done + seq![] =~= done);
    } else if is_non_delimiter(s[0]) {
        lemma_loop_done_prefix(s.skip(1), current.push(s[0]), done);
    } else if current.len() > 0 {
        lemma_loop_done_prefix(s.skip(1), seq![], done.push(current));
        lemma_loop_done_prefix(s.skip(1), seq![], seq![current]);
        assert(done.push(current) + tokens_loop(s.skip(1), seq![], seq![]) =~= done + (seq![current]
            + tokens_loop(s.skip(1), seq![], seq![])));
    } else {
        lemma_loop_done_prefix(s.skip(1), seq![], done);
    }
}

/// A token, a separator and the rest: the token, then the rest's tokens.
pub proof fn lemma_tokens_cons(t: Seq<u8>, sep: Seq<u8>, rest: Seq<u8>)
    requires
        t.len() > 0,
        all_non_delimiters(t),
        sep.len() > 0,
        all_delimiters(sep),
    ensures
        date_tokens(t + (sep + rest)) == seq![t] + date_tokens(rest),
{
    lemma_loop_token(t, sep + rest, seq![], seq![]);
    assert(seq![] + t =~= t);
    lemma_loop_delimiters(sep, rest, t, seq![]);
    lemma_loop_done_prefix(rest, seq![], seq![t]);
}

/// A token alone is one token.
pub proof fn lemma_tokens_last(t: Seq<u8>)
    requires
        t.len() > 0,
        all_non_delimiters(t),
    ensures
        date_tokens(t) == seq![t],
{
    lemma_loop_token(t, seq![], seq![], seq![]);
    assert(t + seq![] =~= t);
    assert(seq![] + t =~= t);
}

// ---------------------------------------------------------------------
// RFC 9110 §5.6.7: the grammar, as builders.
// ---------------------------------------------------------------------

/// The values the productions of an HTTP-date take.
pub struct HttpDateFields {
    /// Index of `day-name` (or `day-name-l`): 0 is Monday, 6 is Sunday.
    pub day_name: nat,
    /// `day`, `2DIGIT` (or the digit of `date3`'s `SP 1DIGIT`).
    pub day: nat,
    /// Index of `month`: 0 is January.
    pub month: nat,
    /// `year`, `4DIGIT` (`2DIGIT` in `date2`).
    pub year: nat,
    /// `hour`, `2DIGIT`.
    pub hour: nat,
    /// `minute`, `2DIGIT`.
    pub minute: nat,
    /// `second`, `2DIGIT`.
    pub second: nat,
}

/// Values the productions allow: every `DIGIT` is a digit, every name one
/// of the listed.
pub open spec fn fields_allowed(f: HttpDateFields) -> bool {
    f.day_name < 7 && f.day < 100 && f.month < 12 && f.year < 10000 && f.hour < 100 && f.minute < 100 && f.second < 100
}

/// The `DIGIT` of value `n` (for `n < 10`).
pub open spec fn digit(n: nat) -> u8 {
    (0x30 + n) as u8
}

/// `2DIGIT` of the number `n` (for `n < 100`).
pub open spec fn two_digits(n: nat) -> Seq<u8> {
    seq![digit(n / 10), digit(n % 10)]
}

/// `4DIGIT` of the number `n` (for `n < 10000`).
pub open spec fn four_digits(n: nat) -> Seq<u8> {
    seq![digit(n / 1000), digit(n / 100 % 10), digit(n / 10 % 10), digit(n % 10)]
}

/// `day-name = %s"Mon" / %s"Tue" / %s"Wed" / %s"Thu" / %s"Fri" / %s"Sat" /
/// %s"Sun"`, by index.
pub open spec fn day_name(i: nat) -> Seq<u8> {
    if i == 0 { seq![0x4Du8, 0x6F, 0x6E] }
    else if i == 1 { seq![0x54u8, 0x75, 0x65] }
    else if i == 2 { seq![0x57u8, 0x65, 0x64] }
    else if i == 3 { seq![0x54u8, 0x68, 0x75] }
    else if i == 4 { seq![0x46u8, 0x72, 0x69] }
    else if i == 5 { seq![0x53u8, 0x61, 0x74] }
    else { seq![0x53u8, 0x75, 0x6E] }
}

/// `day-name-l = %s"Monday" / ... / %s"Sunday"`, by index.
pub open spec fn day_name_long(i: nat) -> Seq<u8> {
    if i == 0 { seq![0x4Du8, 0x6F, 0x6E, 0x64, 0x61, 0x79] }
    else if i == 1 { seq![0x54u8, 0x75, 0x65, 0x73, 0x64, 0x61, 0x79] }
    else if i == 2 { seq![0x57u8, 0x65, 0x64, 0x6E, 0x65, 0x73, 0x64, 0x61, 0x79] }
    else if i == 3 { seq![0x54u8, 0x68, 0x75, 0x72, 0x73, 0x64, 0x61, 0x79] }
    else if i == 4 { seq![0x46u8, 0x72, 0x69, 0x64, 0x61, 0x79] }
    else if i == 5 { seq![0x53u8, 0x61, 0x74, 0x75, 0x72, 0x64, 0x61, 0x79] }
    else { seq![0x53u8, 0x75, 0x6E, 0x64, 0x61, 0x79] }
}

/// `month = %s"Jan" / ... / %s"Dec"`, by index.
pub open spec fn month_name(i: nat) -> Seq<u8> {
    if i == 0 { seq![0x4Au8, 0x61, 0x6E] }
    else if i == 1 { seq![0x46u8, 0x65, 0x62] }
    else if i == 2 { seq![0x4Du8, 0x61, 0x72] }
    else if i == 3 { seq![0x41u8, 0x70, 0x72] }
    else if i == 4 { seq![0x4Du8, 0x61, 0x79] }
    else if i == 5 { seq![0x4Au8, 0x75, 0x6E] }
    else if i == 6 { seq![0x4Au8, 0x75, 0x6C] }
    else if i == 7 { seq![0x41u8, 0x75, 0x67] }
    else if i == 8 { seq![0x53u8, 0x65, 0x70] }
    else if i == 9 { seq![0x4Fu8, 0x63, 0x74] }
    else if i == 10 { seq![0x4Eu8, 0x6F, 0x76] }
    else { seq![0x44u8, 0x65, 0x63] }
}

/// `GMT = %s"GMT"`
pub open spec fn gmt() -> Seq<u8> {
    seq![0x47u8, 0x4D, 0x54]
}

/// `time-of-day = hour ":" minute ":" second`
pub open spec fn time_of_day(f: HttpDateFields) -> Seq<u8> {
    two_digits(f.hour) + (seq![0x3Au8] + (two_digits(f.minute) + (seq![0x3Au8] + two_digits(f.second))))
}

/// `IMF-fixdate = day-name "," SP date1 SP time-of-day SP GMT`, with
/// `date1 = day SP month SP year`.
pub open spec fn imf_fixdate(f: HttpDateFields) -> Seq<u8> {
    day_name(f.day_name) + (seq![0x2Cu8, 0x20] + (two_digits(f.day) + (seq![0x20u8] + (month_name(f.month)
        + (seq![0x20u8] + (four_digits(f.year) + (seq![0x20u8] + (time_of_day(f) + (seq![0x20u8] + gmt())))))))))
}

/// `asctime-date = day-name SP date3 SP time-of-day SP year`, with
/// `date3 = month SP ( 2DIGIT / ( SP 1DIGIT ))`: `padded` chooses
/// `SP 1DIGIT` (for a day below 10).
pub open spec fn asctime_date(f: HttpDateFields, padded: bool) -> Seq<u8> {
    day_name(f.day_name) + (seq![0x20u8] + (month_name(f.month) + (seq![0x20u8] + ((if padded {
        seq![0x20u8] + seq![digit(f.day)]
    } else {
        two_digits(f.day)
    }) + (seq![0x20u8] + (time_of_day(f) + (seq![0x20u8] + four_digits(f.year))))))))
}

/// `rfc850-date = day-name-l "," SP date2 SP time-of-day SP GMT`, with
/// `date2 = day "-" month "-" 2DIGIT` (the 2DIGIT is `f.year`, below 100).
pub open spec fn rfc850_date(f: HttpDateFields) -> Seq<u8> {
    day_name_long(f.day_name) + (seq![0x2Cu8, 0x20] + (two_digits(f.day) + (seq![0x2Du8] + (month_name(f.month)
        + (seq![0x2Du8] + (two_digits(f.year) + (seq![0x20u8] + (time_of_day(f) + (seq![0x20u8] + gmt())))))))))
}

// ---------------------------------------------------------------------
// The calendar the fields denote.
// ---------------------------------------------------------------------

/// A leap year of the Gregorian calendar.
pub open spec fn gregorian_leap(y: nat) -> bool {
    y % 400 == 0 || (y % 4 == 0 && y % 100 != 0)
}

/// The days in month `m` (0 is January) of year `y`.
pub open spec fn month_length(y: nat, m: nat) -> nat {
    if m == 1 {
        if gregorian_leap(y) { 29 } else { 28 }
    } else if m == 3 || m == 5 || m == 8 || m == 10 {
        30
    } else {
        31
    }
}

/// The fields denote an instant a cookie-date can represent: from year
/// 1601, a day of the month, a time of day with no leap second.
pub open spec fn denotes_cookie_date(year: nat, month: nat, day: nat, hour: nat, minute: nat, second: nat) -> bool {
    year >= 1601 && 1 <= day <= month_length(year, month) && hour <= 23 && minute <= 59 && second <= 59
}

/// The cookie-date record for fields.
pub open spec fn date_of(year: nat, f: HttpDateFields) -> CookieDate {
    CookieDate { year, month: f.month + 1, day_of_month: f.day, hour: f.hour, minute: f.minute, second: f.second }
}

// ---------------------------------------------------------------------
// The statements (lemma statements first, proofs in the next commit).
// ---------------------------------------------------------------------

/// What the cookie-date parser makes of the string of fields `f` in
/// `format`: the date the fields denote when they denote one a cookie-date
/// can represent, and failure otherwise. `year` is the year the fields
/// denote (the four digits, or the pivoted two).
pub open spec fn reads_as_denoted(input: Seq<u8>, year: nat, f: HttpDateFields) -> bool {
    parse_a_cookie_date(input) == if denotes_cookie_date(year, f.month, f.day, f.hour, f.minute, f.second) {
        Some(date_of(year, f))
    } else {
        None
    }
}

/// The year RFC 850's two digits stand for under §5.1.1 steps 3 and 4.
pub open spec fn pivoted_year(two_digit: nat) -> nat {
    if two_digit >= 70 { 1900 + two_digit } else { 2000 + two_digit }
}

/// Statement of `lemma_imf_fixdate_agrees`: every IMF-fixdate the grammar
/// produces, with a year from 100, is read as the date its fields denote.
pub open spec fn imf_fixdate_agrees(f: HttpDateFields) -> bool {
    (fields_allowed(f) && f.year >= 100) ==> reads_as_denoted(imf_fixdate(f), f.year, f)
}

/// Statement of `lemma_asctime_agrees`: likewise for asctime-date, in
/// both forms of `date3` (`padded` only for a day below 10).
pub open spec fn asctime_agrees(f: HttpDateFields, padded: bool) -> bool {
    (fields_allowed(f) && f.year >= 100 && (padded ==> f.day < 10)) ==> reads_as_denoted(
        asctime_date(f, padded),
        f.year,
        f,
    )
}

/// Statement of `lemma_rfc850_agrees`: likewise for rfc850-date, where the
/// year is two digits and the cookie-date parser's pivot reads it.
pub open spec fn rfc850_agrees(f: HttpDateFields) -> bool {
    (fields_allowed(f) && f.year < 100) ==> reads_as_denoted(rfc850_date(f), pivoted_year(f.year), f)
}

} // verus!
