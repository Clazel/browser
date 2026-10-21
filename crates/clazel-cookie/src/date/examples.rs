//! Examples evaluated on the spec: Verus computes the spec on concrete
//! inputs, so a transcription error shows up here as a failed proof.
//! The inputs are the rows of `http-state`'s `dates/examples.json` (see
//! `tests/data/http-state-dates/SOURCE.md`) and RFC 9110 §5.6.7's own
//! example date; `tests/conformance_dates.rs` runs all the suite's rows
//! through the executable parser.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// RFC 9110 §5.6.7's example: "Sun, 06 Nov 1994 08:49:37 GMT".
pub proof fn example_imf_fixdate()
    ensures
        parse_a_cookie_date(
            seq![0x53u8, 0x75u8, 0x6Eu8, 0x2Cu8, 0x20u8, 0x30u8, 0x36u8, 0x20u8, 0x4Eu8, 0x6Fu8, 0x76u8, 0x20u8, 0x31u8, 0x39u8, 0x39u8, 0x34u8, 0x20u8, 0x30u8, 0x38u8, 0x3Au8, 0x34u8, 0x39u8, 0x3Au8, 0x33u8, 0x37u8, 0x20u8, 0x47u8, 0x4Du8, 0x54u8],
        ) == Some(CookieDate { year: 1994, month: 11, day_of_month: 6, hour: 8, minute: 49, second: 37 }),
{
    assert(parse_a_cookie_date(
        seq![0x53u8, 0x75u8, 0x6Eu8, 0x2Cu8, 0x20u8, 0x30u8, 0x36u8, 0x20u8, 0x4Eu8, 0x6Fu8, 0x76u8, 0x20u8, 0x31u8, 0x39u8, 0x39u8, 0x34u8, 0x20u8, 0x30u8, 0x38u8, 0x3Au8, 0x34u8, 0x39u8, 0x3Au8, 0x33u8, 0x37u8, 0x20u8, 0x47u8, 0x4Du8, 0x54u8],
    ) == Some(CookieDate { year: 1994, month: 11, day_of_month: 6, hour: 8, minute: 49, second: 37 })) by (compute_only);
}

} // verus!
