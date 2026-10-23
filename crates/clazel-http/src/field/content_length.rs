//! Executable `Content-Length` (§8.6): the digits, the repeated-value list
//! case, and the `u64` limit. Each public function is proven to meet
//! [`super::contract`].

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

use super::contract::ContentLengthError;
use super::list::split_values;
use super::section::combine;
use super::string::{all_in_exec, at, slice_eq};

verus! {

/// The value of the decimal digits `s`, if it fits in a `u64`.
fn decimal_to_u64(s: &[u8]) -> (r: Option<u64>)
    requires
        all_in(s@, Class::Digit),
    ensures
        match r {
            Some(n) => n as nat == decimal_value(s@),
            None => decimal_value(s@) > u64::MAX,
        },
{
    proof {
        super::lemmas::lemma_all_in_index(s@, Class::Digit);
    }
    assert(s@.take(0) =~= Seq::<u8>::empty());
    let mut acc: u64 = 0;
    let mut overflow = false;
    let mut i: usize = 0;
    while i < s.len()
        invariant
            i <= s.len(),
            forall|j: int| 0 <= j < s.len() ==> is_digit(#[trigger] s@[j]),
            !overflow ==> acc as nat == decimal_value(s@.take(i as int)),
            overflow ==> decimal_value(s@.take(i as int)) > u64::MAX,
        decreases s.len() - i,
    {
        let c = match at(s, i) {
            Some(c) => c,
            None => {
                // Unreachable: i < s.len().
                assert(false);
                0
            },
        };
        assert(s@.take(i as int + 1) =~= s@.take(i as int).push(c));
        proof {
            super::lemmas::lemma_decimal_value_push(s@.take(i as int), c);
        }
        // c is a digit, so this does not wrap.
        let d = c.wrapping_sub(0x30) as u64;
        if !overflow {
            if acc > u64::MAX.saturating_sub(d) / 10 {
                overflow = true;
            } else {
                acc = acc.saturating_mul(10).saturating_add(d);
            }
        }
        // Never saturates: i < s.len().
        i = i.saturating_add(1);
    }
    assert(s@.take(s.len() as int) =~= s@);
    if overflow {
        None
    } else {
        Some(acc)
    }
}

/// `parse_content_length` (§8.6) of the combined field value `value`.
pub fn parse_content_length(value: &[u8]) -> (out: Result<u64, ContentLengthError>)
    ensures
        super::contract::parse_content_length_ensures(value@, out),
{
    let members = split_values(value);
    let ghost view = super::types::strings_view(members@);
    let first = match members.first() {
        Some(f) => f,
        None => return Err(ContentLengthError::Invalid),
    };
    assert(view[0] == first@);
    let digits = !first.is_empty() && all_in_exec(first.as_slice(), &Class::Digit);
    if !digits {
        return Err(ContentLengthError::Invalid);
    }
    proof {
        super::lemmas::lemma_all_equal_index(view, first@);
    }
    let mut i: usize = 0;
    while i < members.len()
        invariant
            i <= members.len(),
            view == super::types::strings_view(members@),
            view[0] == first@,
            view == super::spec::split_values(value@),
            forall|j: int| 0 <= j < i ==> (#[trigger] view[j]) == first@,
        decreases members.len() - i,
    {
        let member = match members.get(i) {
            Some(member) => member,
            None => {
                // Unreachable: i < members.len().
                assert(false);
                return Err(ContentLengthError::Invalid);
            },
        };
        if !slice_eq(member.as_slice(), first.as_slice()) {
            assert(view[i as int] == member@);
            proof {
                super::lemmas::lemma_all_equal_index(view, first@);
            }
            assert(!all_equal(view, first@));
            return Err(ContentLengthError::Invalid);
        }
        // Never saturates: i < members.len().
        i = i.saturating_add(1);
    }
    match decimal_to_u64(first.as_slice()) {
        Some(n) => Ok(n),
        None => Err(ContentLengthError::TooLarge),
    }
}

/// `parse_content_length_lines` (§8.6): the field line values of every
/// `Content-Length` line, combined (§5.3) and read.
pub fn parse_content_length_lines(lines: &[Vec<u8>]) -> (out: Result<u64, ContentLengthError>)
    ensures
        super::contract::parse_content_length_lines_ensures(super::types::strings_view(lines@), out),
{
    if lines.is_empty() {
        return Err(ContentLengthError::Invalid);
    }
    let combined = combine(lines);
    parse_content_length(combined.as_slice())
}

} // verus!
