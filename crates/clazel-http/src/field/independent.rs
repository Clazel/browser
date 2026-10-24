//! An independent transcription of HTTP header names, header values and
//! list splitting, from a different standard than [`super::spec`]: the
//! WHATWG Fetch Standard (docs/VERIFICATION.md, "Trust without reviewers",
//! item 2). The transcription section below uses nothing from `spec.rs`;
//! only the proof section after it does. It was written from the Fetch
//! text before `spec.rs` was read again.
//!
//! Sources (each pinned):
//! - Fetch Standard, Living Standard, last updated 19 October 2026, commit
//!   `59afe349913d56898c947576216f1c2579308be7`,
//!   <https://fetch.spec.whatwg.org/#http-whitespace>, §2.2 "HTTP": "HTTP
//!   tab or space", "HTTP whitespace", "HTTP newline byte", "HTTP tab or
//!   space byte", "HTTP whitespace byte", "collect an HTTP quoted string",
//!   "get, decode, and split" (for a header value), "header name", "header
//!   value" and "normalize".
//! - MIME Sniffing Standard, Living Standard, last updated 19 October 2026,
//!   commit `ba4b3c385b9765ddfe4a994e2bb89e0ab96068e2`,
//!   <https://mimesniff.spec.whatwg.org/#http-token-code-point>, §3: "HTTP
//!   token code point". Fetch defines a header name as a byte sequence that
//!   "matches the field-name token production" of the HTTP RFC, which would
//!   be RFC 9110 itself; the MIME Sniffing Standard states the same
//!   production as a list of code points ("This matches the value space of
//!   the token token production"), and that list is what is transcribed.
//! - Infra Standard, Living Standard, commit
//!   `459b7829230ad256a690dabd315db974469af8e7`: "collecting a sequence of
//!   code points", "ASCII alphanumeric".
//!
//! What the two parsers agree on, and where they differ (every difference
//! is by design of one of the two standards, and proven or exhibited in the
//! lemmas below):
//! - [`lemma_header_name_equals_field_name`]: a header name is exactly a
//!   `field-name` (a `token`), for every byte sequence.
//! - [`lemma_trim_equals_strip_ows`]: Fetch's "HTTP tab or space" is RFC
//!   9110's `SP / HTAB`, so removing it from the ends of a string is
//!   removing OWS, for every byte sequence. (Fetch's *normalize* removes
//!   "HTTP whitespace bytes", which also include CR and LF; it differs from
//!   `strip_ows` on exactly the strings whose ends, after the SP and HTAB
//!   are gone, are a CR or LF: see [`lemma_normalize_equals_strip_ows`],
//!   which proves them equal when there is no CR or LF at all, and
//!   `examples` of the difference in its doc comment.)
//! - [`lemma_header_value_equals_field_value`]: a RFC 9110 `field-value` is
//!   a Fetch header value; the two agree on every byte sequence made only
//!   of SP, HTAB, VCHAR and obs-text. Fetch also accepts any other byte
//!   except NUL, CR and LF (the other controls, and DEL), because
//!   `field-value` "is not compatible with deployed content" (Fetch's own
//!   note).
//! - [`lemma_quoted_string_agrees`]: Fetch's "collect an HTTP quoted
//!   string" reads every RFC 9110 `quoted-string` to the same value and
//!   the same end. It accepts more: an unterminated string, any byte in the
//!   body, any byte after a backslash.
//! - [`lemma_get_decode_split_equals_split_values`]: Fetch's "get, decode,
//!   and split" gives the same pieces as `split_values` on **every** byte
//!   sequence, including the empty pieces; and
//!   [`lemma_get_decode_split_drop_empty`]: dropping the empty ones is
//!   exactly RFC 9110's `list_elements`. The one difference of substance is
//!   that Fetch keeps the empty elements where §5.6.1.2 says a recipient
//!   ignores them; `split_values` is the shared function, `list_elements`
//!   the RFC's.
//!
//! Modelling choices:
//! - Fetch's strings are isomorphic-decoded byte sequences ("Let input be
//!   the result of isomorphic decoding value"); isomorphic decoding keeps
//!   each byte's value, so a `Seq<u8>` is the same string and the position
//!   variable indexes bytes. "Collecting a sequence of code points" takes
//!   its condition as an [`Until`], one variant per condition used.
//! - Iteration ("while true") is a recursive function carrying the loop's
//!   variables; "continue" is a recursive call, "break" returns.
//! - Fetch's "collect an HTTP quoted string" step 7 reads "from
//!   positionStart to position, inclusive", which takes one code point past
//!   the closing quote and contradicts the standard's own examples; we
//!   take the evident intent (exclusive), as `clazel-mime` does (see
//!   `docs/ERRATA.md`).
//! - "Assert: the code point at position within input is U+002C (,)"
//!   (get, decode, and split, step 7) and the other assertions hold
//!   because of the steps before them; they are not transcribed.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ===========================================================================
// Transcription: Fetch §2.2 and MIME Sniffing §3 (uses nothing from spec.rs).
// ===========================================================================

/// An HTTP tab or space byte: "0x09 (HT) or 0x20 (SP)".
pub open spec fn f_is_http_tab_or_space(b: u8) -> bool {
    b == 0x09 || b == 0x20
}

/// An HTTP newline byte: "0x0A (LF) or 0x0D (CR)".
pub open spec fn f_is_http_newline(b: u8) -> bool {
    b == 0x0A || b == 0x0D
}

/// An HTTP whitespace byte: "an HTTP newline byte or HTTP tab or space byte".
pub open spec fn f_is_http_whitespace(b: u8) -> bool {
    f_is_http_newline(b) || f_is_http_tab_or_space(b)
}

/// ASCII alphanumeric (Infra): an ASCII digit, upper alpha or lower alpha.
pub open spec fn f_is_ascii_alphanumeric(b: u8) -> bool {
    (0x30 <= b <= 0x39) || (0x41 <= b <= 0x5A) || (0x61 <= b <= 0x7A)
}

/// HTTP token code point (MIME Sniffing §3): "U+0021 (!), U+0023 (#),
/// U+0024 ($), U+0025 (%), U+0026 (&), U+0027 ('), U+002A (*), U+002B (+),
/// U+002D (-), U+002E (.), U+005E (^), U+005F (_), U+0060 (`), U+007C (|),
/// U+007E (~), or an ASCII alphanumeric."
pub open spec fn f_is_http_token_code_point(b: u8) -> bool {
    b == 0x21 || b == 0x23 || b == 0x24 || b == 0x25 || b == 0x26 || b == 0x27
        || b == 0x2A || b == 0x2B || b == 0x2D || b == 0x2E || b == 0x5E || b == 0x5F
        || b == 0x60 || b == 0x7C || b == 0x7E || f_is_ascii_alphanumeric(b)
}

/// Every byte of `s` is an HTTP token code point.
pub open spec fn f_all_token_code_points(s: Seq<u8>) -> bool
    decreases s.len()
{
    s.len() == 0 || (f_is_http_token_code_point(s[0]) && f_all_token_code_points(s.drop_first()))
}

/// Fetch: "A header name is a byte sequence that matches the field-name
/// token production" (a token is one or more token code points).
pub open spec fn f_is_header_name(s: Seq<u8>) -> bool {
    s.len() > 0 && f_all_token_code_points(s)
}

/// `s` contains no 0x00 (NUL) or HTTP newline byte.
pub open spec fn f_no_nul_or_newline(s: Seq<u8>) -> bool
    decreases s.len()
{
    s.len() == 0 || (s[0] != 0x00 && !f_is_http_newline(s[0]) && f_no_nul_or_newline(s.drop_first()))
}

/// Fetch: "A header value is a byte sequence that matches the following
/// conditions: Has no leading or trailing HTTP tab or space bytes.
/// Contains no 0x00 (NUL) or HTTP newline bytes."
pub open spec fn f_is_header_value(s: Seq<u8>) -> bool {
    (s.len() == 0 || (!f_is_http_tab_or_space(s[0]) && !f_is_http_tab_or_space(s.last())))
        && f_no_nul_or_newline(s)
}

/// Which bytes are removed from the ends of a string.
pub enum Strip {
    /// "HTTP tab or space"
    TabOrSpace,
    /// "HTTP whitespace bytes"
    Whitespace,
}

/// Is `b` one of the bytes `strip` removes?
pub open spec fn f_stripped(strip: Strip, b: u8) -> bool {
    match strip {
        Strip::TabOrSpace => f_is_http_tab_or_space(b),
        Strip::Whitespace => f_is_http_whitespace(b),
    }
}

/// `s` without its leading bytes that `strip` removes.
pub open spec fn f_remove_leading(strip: Strip, s: Seq<u8>) -> Seq<u8>
    decreases s.len()
{
    if s.len() > 0 && f_stripped(strip, s[0]) {
        f_remove_leading(strip, s.drop_first())
    } else {
        s
    }
}

/// `s` without its trailing bytes that `strip` removes.
pub open spec fn f_remove_trailing(strip: Strip, s: Seq<u8>) -> Seq<u8>
    decreases s.len()
{
    if s.len() > 0 && f_stripped(strip, s.last()) {
        f_remove_trailing(strip, s.drop_last())
    } else {
        s
    }
}

/// "Remove all HTTP tab or space from the start and end of" `s`.
pub open spec fn f_trim(s: Seq<u8>) -> Seq<u8> {
    f_remove_trailing(Strip::TabOrSpace, f_remove_leading(Strip::TabOrSpace, s))
}

/// Fetch, header value "normalize": "remove any leading and trailing HTTP
/// whitespace bytes from potentialValue".
pub open spec fn f_normalize(s: Seq<u8>) -> Seq<u8> {
    f_remove_trailing(Strip::Whitespace, f_remove_leading(Strip::Whitespace, s))
}

/// The conditions "collecting a sequence of code points" is given below.
pub enum Until {
    /// "not U+0022 (") or U+002C (,)" (get, decode, and split)
    QuoteOrComma,
    /// "not U+0022 (") or U+005C (\)" (collect an HTTP quoted string)
    QuoteOrBackslash,
}

/// Does `b` meet the condition?
pub open spec fn f_meets(cond: Until, b: u8) -> bool {
    match cond {
        Until::QuoteOrComma => b != 0x22 && b != 0x2C,
        Until::QuoteOrBackslash => b != 0x22 && b != 0x5C,
    }
}

/// Collect a sequence of code points (Infra), step 2's loop, with `result`
/// as built so far. Returns (result, position).
pub open spec fn f_collect_loop(cond: Until, input: Seq<u8>, position: nat, result: Seq<u8>) -> (Seq<u8>, nat)
    decreases input.len() - position
{
    // 2. "While position doesn't point past the end of input and the code
    //    point at position within input meets the condition:"
    if position < input.len() && f_meets(cond, input[position as int]) {
        // 2.1 append it to result. 2.2 advance position by 1.
        f_collect_loop(cond, input, position + 1, result.push(input[position as int]))
    } else {
        // 3. "Return result."
        (result, position)
    }
}

/// Collect a sequence of code points meeting `cond` from `input`, given
/// `position`. Returns (result, position).
pub open spec fn f_collect(cond: Until, input: Seq<u8>, position: nat) -> (Seq<u8>, nat) {
    f_collect_loop(cond, input, position, seq![])
}

/// Collect an HTTP quoted string (Fetch §2.2), step 5's "While true" loop,
/// with `value` as built so far. Returns (value, position).
pub open spec fn f_quoted_loop(input: Seq<u8>, position: nat, value: Seq<u8>) -> (Seq<u8>, nat)
    decreases input.len() - position via f_quoted_loop_decreases
{
    // 5.1 "Append the result of collecting a sequence of code points that
    //      are not U+0022 (") or U+005C (\) from input, given position, to
    //      value."
    let (collected, position) = f_collect(Until::QuoteOrBackslash, input, position);
    let value = value + collected;
    if position >= input.len() {
        // 5.2 "If position is past the end of input, then break."
        (value, position)
    } else {
        // 5.3 "Let quoteOrBackslash be the code point at position within input."
        let quote_or_backslash = input[position as int];
        // 5.4 "Advance position by 1."
        let position = position + 1;
        if quote_or_backslash == 0x5C {
            // 5.5 "If quoteOrBackslash is U+005C (\), then:"
            if position >= input.len() {
                // 5.5.1 "If position is past the end of input, then append
                //       U+005C (\) to value and break."
                (value.push(0x5C), position)
            } else {
                // 5.5.2 "Append the code point at position within input to value."
                // 5.5.3 "Advance position by 1."
                f_quoted_loop(input, position + 1, value.push(input[position as int]))
            }
        } else {
            // 5.6 "Otherwise:" 5.6.1 asserts quoteOrBackslash is U+0022 ("),
            // which holds because step 5.1 stopped at it. 5.6.2 "Break."
            (value, position)
        }
    }
}

/// Termination of [`f_quoted_loop`].
#[via_fn]
pub proof fn f_quoted_loop_decreases(input: Seq<u8>, position: nat, value: Seq<u8>) {
    super::termination::lemma_f_collect_loop_position(Until::QuoteOrBackslash, input, position, seq![]);
}

/// Collect an HTTP quoted string (Fetch §2.2) from `input`, given
/// `position` and `extract_value`. Returns (the string, position).
pub open spec fn f_collect_quoted(input: Seq<u8>, position: nat, extract_value: bool) -> (Seq<u8>, nat) {
    // 1. "Let positionStart be position."
    let position_start = position;
    // 2. "Let value be the empty string."
    // 3. "Assert: the code point at position within input is U+0022 (")."
    // 4. "Advance position by 1."
    // 5. the loop.
    let (value, position) = f_quoted_loop(input, position + 1, seq![]);
    if extract_value {
        // 6. "If extract-value is true, then return value."
        (value, position)
    } else {
        // 7. "Return the code points from positionStart to position,
        //    inclusive, within input." Exclusive: see the modelling choices.
        (input.subrange(position_start as int, position as int), position)
    }
}

/// Get, decode, and split a header value (Fetch §2.2), step 5's "While
/// true" loop from `position`, with `temp_value` and `values` as built so
/// far. Returns `values`.
pub open spec fn f_get_decode_split_loop(
    input: Seq<u8>,
    position: nat,
    temp_value: Seq<u8>,
    values: Seq<Seq<u8>>,
) -> Seq<Seq<u8>>
    decreases input.len() - position via f_get_decode_split_loop_decreases
{
    // 5.1 "Append the result of collecting a sequence of code points that
    //      are not U+0022 (") or U+002C (,) from input, given position, to
    //      temporaryValue."
    let (collected, position) = f_collect(Until::QuoteOrComma, input, position);
    let temp_value = temp_value + collected;
    // 5.2 "If position is not past the end of input and the code point at
    //      position within input is U+0022 ("), then:"
    let (temp_value, position, continues) = if position < input.len() && input[position as int] == 0x22 {
        // 5.2.1 "Append the result of collecting an HTTP quoted string from
        //       input, given position, to temporaryValue."
        let (quoted, after) = f_collect_quoted(input, position, false);
        // 5.2.2 "If position is not past the end of input, then continue."
        (temp_value + quoted, after, after < input.len())
    } else {
        (temp_value, position, false)
    };
    if continues {
        f_get_decode_split_loop(input, position, temp_value, values)
    } else {
        // 5.3 "Remove all HTTP tab or space from the start and end of
        //      temporaryValue."
        // 5.4 "Append temporaryValue to values."
        let values = values.push(f_trim(temp_value));
        // 5.5 "Set temporaryValue to the empty string."
        if position >= input.len() {
            // 5.6 "If position is past the end of input, then return values."
            values
        } else {
            // 5.7 "Assert: the code point at position within input is
            //      U+002C (,)." 5.8 "Advance position by 1."
            f_get_decode_split_loop(input, position + 1, seq![], values)
        }
    }
}

/// Termination of [`f_get_decode_split_loop`]: each round passes a quoted
/// string or a comma.
#[via_fn]
pub proof fn f_get_decode_split_loop_decreases(input: Seq<u8>, position: nat, temp_value: Seq<u8>, values: Seq<Seq<u8>>) {
    super::termination::lemma_f_collect_loop_position(Until::QuoteOrComma, input, position, seq![]);
    let p = f_collect(Until::QuoteOrComma, input, position).1;
    if p < input.len() && input[p as int] == 0x22 {
        super::termination::lemma_f_quoted_loop_position(input, p + 1, seq![]);
    }
}

/// Get, decode, and split a header value (Fetch §2.2, #concept-header-value-get-decode-split).
pub open spec fn f_get_decode_split(value: Seq<u8>) -> Seq<Seq<u8>> {
    // 1. "Let input be the result of isomorphic decoding value": the same bytes.
    // 2. position at the start. 3. "Let values be a list of strings, initially « »."
    // 4. "Let temporaryValue be the empty string." 5. the loop.
    f_get_decode_split_loop(value, 0, seq![], seq![])
}

// ===========================================================================
// Proofs: what the two transcriptions agree on (this section uses spec.rs).
// ===========================================================================

/// The token code points of MIME Sniffing and RFC 9110's `tchar`s are the
/// same octets.
pub proof fn lemma_f_all_token(s: Seq<u8>)
    ensures
        f_all_token_code_points(s) <==> all_in(s, Class::Tchar),
    decreases s.len()
{
    if s.len() > 0 {
        lemma_f_all_token(s.drop_first());
        assert(f_is_http_token_code_point(s[0]) <==> is_tchar(s[0]));
    }
}

/// A Fetch header name is exactly an RFC 9110 `field-name`, for every byte
/// sequence.
pub proof fn lemma_header_name_equals_field_name(s: Seq<u8>)
    ensures
        f_is_header_name(s) <==> is_field_name(s),
{
    lemma_f_all_token(s);
}

/// Removing the leading HTTP tab or space is removing the leading OWS.
pub proof fn lemma_remove_leading_tab_or_space(s: Seq<u8>)
    ensures
        f_remove_leading(Strip::TabOrSpace, s) == strip_leading_ows(s),
    decreases s.len()
{
    if s.len() > 0 && f_is_http_tab_or_space(s[0]) {
        lemma_remove_leading_tab_or_space(s.drop_first());
        let n = run_len(Class::Ows, s.drop_first());
        super::termination::lemma_run_len_le(Class::Ows, s.drop_first());
        assert(run_len(Class::Ows, s) == 1 + n);
        assert forall|k: int| 0 <= k < s.drop_first().skip(n as int).len() implies s.skip((1 + n) as int)[k]
            == (#[trigger] s.drop_first().skip(n as int))[k] by {
            assert(s.drop_first()[n + k] == s[1 + n + k]);
        }
        assert(s.skip((1 + n) as int) =~= s.drop_first().skip(n as int));
    } else {
        assert(run_len(Class::Ows, s) == 0);
        assert(s.skip(0) =~= s);
    }
}

/// Removing the trailing HTTP tab or space is removing the trailing OWS.
pub proof fn lemma_remove_trailing_tab_or_space(s: Seq<u8>)
    ensures
        f_remove_trailing(Strip::TabOrSpace, s) == strip_trailing_ows(s),
    decreases s.len()
{
    if s.len() > 0 && f_is_http_tab_or_space(s.last()) {
        lemma_remove_trailing_tab_or_space(s.drop_last());
    }
}

/// Fetch's "remove all HTTP tab or space from the start and end" is RFC
/// 9110's removal of OWS, for every byte sequence.
pub proof fn lemma_trim_equals_strip_ows(s: Seq<u8>)
    ensures
        f_trim(s) == strip_ows(s),
{
    lemma_remove_leading_tab_or_space(s);
    lemma_remove_trailing_tab_or_space(strip_leading_ows(s));
}

/// No octet of `s` is CR or LF.
pub open spec fn no_cr_or_lf(s: Seq<u8>) -> bool {
    forall|i: int| 0 <= i < s.len() ==> !f_is_http_newline(#[trigger] s[i])
}

/// Without CR and LF, HTTP whitespace is HTTP tab or space, at the start.
pub proof fn lemma_remove_leading_whitespace(s: Seq<u8>)
    requires
        no_cr_or_lf(s),
    ensures
        f_remove_leading(Strip::Whitespace, s) == f_remove_leading(Strip::TabOrSpace, s),
    decreases s.len()
{
    if s.len() > 0 && f_stripped(Strip::TabOrSpace, s[0]) {
        assert(no_cr_or_lf(s.drop_first())) by {
            assert forall|i: int| 0 <= i < s.drop_first().len() implies !f_is_http_newline(#[trigger] s.drop_first()[i]) by {
                assert(s.drop_first()[i] == s[i + 1]);
            }
        }
        lemma_remove_leading_whitespace(s.drop_first());
    }
}

/// Without CR and LF, HTTP whitespace is HTTP tab or space, at the end.
pub proof fn lemma_remove_trailing_whitespace(s: Seq<u8>)
    requires
        no_cr_or_lf(s),
    ensures
        f_remove_trailing(Strip::Whitespace, s) == f_remove_trailing(Strip::TabOrSpace, s),
    decreases s.len()
{
    if s.len() > 0 && f_stripped(Strip::TabOrSpace, s.last()) {
        assert(no_cr_or_lf(s.drop_last())) by {
            assert forall|i: int| 0 <= i < s.drop_last().len() implies !f_is_http_newline(#[trigger] s.drop_last()[i]) by {
                assert(s.drop_last()[i] == s[i]);
            }
        }
        lemma_remove_trailing_whitespace(s.drop_last());
    }
}

/// Fetch's *normalize* removes HTTP whitespace bytes, which include CR and
/// LF, so it removes more than OWS in general; on a string with no CR and
/// no LF it removes exactly OWS. (The strings where it removes more are
/// the ones with a CR or LF at an end once SP and HTAB are gone: normalize
/// takes `LF a` to `a`, where `strip_ows` keeps the LF; see
/// [`lemma_normalize_differs`].)
pub proof fn lemma_normalize_equals_strip_ows(s: Seq<u8>)
    requires
        no_cr_or_lf(s),
    ensures
        f_normalize(s) == strip_ows(s),
{
    lemma_remove_leading_whitespace(s);
    lemma_remove_leading_tab_or_space(s);
    let t = f_remove_leading(Strip::TabOrSpace, s);
    let n = run_len(Class::Ows, s);
    super::termination::lemma_run_len_le(Class::Ows, s);
    assert(t == s.skip(n as int));
    assert(no_cr_or_lf(t)) by {
        assert forall|i: int| 0 <= i < t.len() implies !f_is_http_newline(#[trigger] t[i]) by {
            assert(t[i] == s[i + n]);
        }
    }
    lemma_remove_trailing_whitespace(t);
    lemma_remove_trailing_tab_or_space(t);
}

/// Where normalize and `strip_ows` differ: a leading LF.
pub proof fn lemma_normalize_differs()
    ensures
        f_normalize(seq![0x0Au8, 0x61u8]) =~= seq![0x61u8],
        strip_ows(seq![0x0Au8, 0x61u8]) =~= seq![0x0Au8, 0x61u8],
{
    assert(f_normalize(seq![0x0Au8, 0x61u8]) =~= seq![0x61u8]) by (compute_only);
    assert(strip_ows(seq![0x0Au8, 0x61u8]) =~= seq![0x0Au8, 0x61u8]) by (compute_only);
}

/// Every octet of a string that is SP, HTAB, VCHAR or obs-text is neither
/// NUL, CR nor LF.
pub proof fn lemma_field_content_no_nul_or_newline(s: Seq<u8>)
    requires
        all_in(s, Class::FieldContent),
    ensures
        f_no_nul_or_newline(s),
    decreases s.len()
{
    if s.len() > 0 {
        lemma_field_content_no_nul_or_newline(s.drop_first());
    }
}

/// An RFC 9110 `field-value` is a Fetch header value, and the two agree on
/// every byte sequence made only of SP, HTAB, VCHAR and obs-text. Fetch
/// also accepts the other controls and DEL (see the file header).
pub proof fn lemma_header_value_equals_field_value(s: Seq<u8>)
    ensures
        is_field_value(s) ==> f_is_header_value(s),
        all_in(s, Class::FieldContent) ==> (f_is_header_value(s) <==> is_field_value(s)),
{
    if all_in(s, Class::FieldContent) {
        lemma_field_content_no_nul_or_newline(s);
        lemma_all_in_index_for_header(s);
        if s.len() > 0 {
            assert(in_class(Class::FieldContent, s[0]));
            assert(in_class(Class::FieldContent, s[s.len() - 1]));
            assert(s.last() == s[s.len() - 1]);
        }
    }
}

/// `all_in` for the field-content class, by index.
proof fn lemma_all_in_index_for_header(s: Seq<u8>)
    ensures
        all_in(s, Class::FieldContent) ==> (forall|i: int| 0 <= i < s.len() ==> in_class(Class::FieldContent, #[trigger] s[i])),
{
    super::lemmas::lemma_all_in_index(s, Class::FieldContent);
}

/// Where a header value is not a `field-value`: a byte string with a
/// control byte other than NUL, CR, LF.
pub proof fn lemma_header_value_differs()
    ensures
        f_is_header_value(seq![0x61u8, 0x01u8, 0x62u8]),
        !is_field_value(seq![0x61u8, 0x01u8, 0x62u8]),
{
    assert(f_is_header_value(seq![0x61u8, 0x01u8, 0x62u8])) by (compute_only);
    assert(!is_field_value(seq![0x61u8, 0x01u8, 0x62u8])) by (compute_only);
}

/// The facts about Fetch's collecting that the proofs below use: it takes
/// the longest run of bytes meeting the condition.
pub proof fn lemma_f_collect_loop(cond: Until, input: Seq<u8>, position: nat, result: Seq<u8>)
    requires
        position <= input.len(),
    ensures
        ({
            let (r, p) = f_collect_loop(cond, input, position, result);
            &&& position <= p <= input.len()
            &&& r == result + input.subrange(position as int, p as int)
            &&& forall|i: int| position <= i < p ==> f_meets(cond, #[trigger] input[i])
            &&& p < input.len() ==> !f_meets(cond, input[p as int])
        }),
    decreases input.len() - position
{
    if position < input.len() && f_meets(cond, input[position as int]) {
        lemma_f_collect_loop(cond, input, position + 1, result.push(input[position as int]));
        let (r, p) = f_collect_loop(cond, input, position + 1, result.push(input[position as int]));
        assert(r =~= result + input.subrange(position as int, p as int)) by {
            assert(input.subrange(position as int, p as int) =~= seq![input[position as int]]
                + input.subrange(position as int + 1, p as int));
        }
    } else {
        assert(input.subrange(position as int, position as int) =~= Seq::<u8>::empty());
    }
}

/// The scan of an empty input is the same in every state.
pub proof fn lemma_scan_empty(input: Seq<u8>, state: QState, cur: Seq<u8>, acc: Seq<Seq<u8>>)
    requires
        input.len() == 0,
    ensures
        split_scan(input, state, cur, acc) == acc.push(strip_ows(cur)),
{
}

/// The splitter passes over octets that are neither DQUOTE nor backslash,
/// inside a quoted string, by adding them to the current piece.
pub proof fn lemma_scan_quoted_run(seg: Seq<u8>, rest: Seq<u8>, cur: Seq<u8>, acc: Seq<Seq<u8>>)
    requires
        forall|i: int| 0 <= i < seg.len() ==> (#[trigger] seg[i]) != 0x22 && seg[i] != 0x5C,
    ensures
        split_scan(seg + rest, QState::Quoted, cur, acc) == split_scan(rest, QState::Quoted, cur + seg, acc),
    decreases seg.len()
{
    if seg.len() > 0 {
        let c = seg[0];
        assert((seg + rest)[0] == c);
        assert((seg + rest).drop_first() =~= seg.drop_first() + rest);
        assert(forall|i: int| 0 <= i < seg.drop_first().len() ==> (#[trigger] seg.drop_first()[i]) != 0x22
            && seg.drop_first()[i] != 0x5C) by {
            assert forall|i: int| 0 <= i < seg.drop_first().len() implies (#[trigger] seg.drop_first()[i]) != 0x22
                && seg.drop_first()[i] != 0x5C by {
                assert(seg.drop_first()[i] == seg[i + 1]);
            }
        }
        lemma_scan_quoted_run(seg.drop_first(), rest, cur.push(c), acc);
        assert(cur.push(c) + seg.drop_first() =~= cur + seg);
    } else {
        assert(seg + rest =~= rest);
        assert(cur + seg =~= cur);
    }
}

/// The splitter, inside a quoted string at a DQUOTE: the string ends.
pub proof fn lemma_quoted_step_quote(input: Seq<u8>, p: nat, cur: Seq<u8>, acc: Seq<Seq<u8>>)
    requires
        p < input.len(),
        input[p as int] == 0x22,
    ensures
        split_scan(input.skip(p as int), QState::Quoted, cur, acc)
            == split_scan(input.skip(p as int + 1), QState::Plain, cur.push(0x22), acc),
{
    assert(input.skip(p as int)[0] == 0x22u8);
    assert(input.skip(p as int).drop_first() =~= input.skip(p as int + 1));
}

/// The splitter, inside a quoted string at a backslash with a byte after
/// it: both bytes go into the piece, and the string goes on.
pub proof fn lemma_quoted_step_escape(input: Seq<u8>, p: nat, cur: Seq<u8>, acc: Seq<Seq<u8>>)
    requires
        p + 1 < input.len(),
        input[p as int] == 0x5C,
    ensures
        split_scan(input.skip(p as int), QState::Quoted, cur, acc)
            == split_scan(input.skip(p as int + 2), QState::Quoted, cur.push(0x5C).push(input[p as int + 1]), acc),
{
    reveal_with_fuel(split_scan, 3);
    assert(input.skip(p as int)[0] == 0x5Cu8);
    assert(input.skip(p as int).drop_first() =~= input.skip(p as int + 1));
    assert(input.skip(p as int + 1)[0] == input[p as int + 1]);
    assert(input.skip(p as int + 1).drop_first() =~= input.skip(p as int + 2));
}

/// The splitter, inside a quoted string at a backslash that ends the
/// input: the backslash goes into the last piece.
pub proof fn lemma_quoted_step_escape_end(input: Seq<u8>, p: nat, cur: Seq<u8>, acc: Seq<Seq<u8>>)
    requires
        p + 1 == input.len(),
        input[p as int] == 0x5C,
    ensures
        split_scan(input.skip(p as int), QState::Quoted, cur, acc) == acc.push(strip_ows(cur.push(0x5C))),
{
    reveal_with_fuel(split_scan, 3);
    assert(input.skip(p as int)[0] == 0x5Cu8);
    assert(input.skip(p as int).drop_first() =~= Seq::<u8>::empty());
}

/// Fetch's quoted-string loop and the splitter's state `Quoted` read the
/// same bytes: from `position`, the loop stops where the string ends, and
/// the splitter, which has taken the same bytes into its current piece, is
/// back outside a quoted string (or at the end of the input, where its
/// state does not matter).
pub proof fn lemma_quoted_loop_scan(input: Seq<u8>, position: nat, value: Seq<u8>, cur: Seq<u8>, acc: Seq<Seq<u8>>)
    requires
        position <= input.len(),
    ensures
        position <= f_quoted_loop(input, position, value).1 <= input.len(),
        split_scan(input.skip(position as int), QState::Quoted, cur, acc) == split_scan(
            input.skip(f_quoted_loop(input, position, value).1 as int),
            QState::Plain,
            cur + input.subrange(position as int, f_quoted_loop(input, position, value).1 as int),
            acc,
        ),
    decreases input.len() - position
{
    lemma_f_collect_loop(Until::QuoteOrBackslash, input, position, seq![]);
    let (run, p) = f_collect(Until::QuoteOrBackslash, input, position);
    assert(run =~= input.subrange(position as int, p as int));
    assert(input.skip(position as int) =~= run + input.skip(p as int));
    assert(forall|i: int| 0 <= i < run.len() ==> (#[trigger] run[i]) != 0x22 && run[i] != 0x5C) by {
        assert forall|i: int| 0 <= i < run.len() implies (#[trigger] run[i]) != 0x22 && run[i] != 0x5C by {
            assert(run[i] == input[position + i]);
            assert(f_meets(Until::QuoteOrBackslash, input[position + i]));
        }
    }
    // The run is passed over inside the string.
    lemma_scan_quoted_run(run, input.skip(p as int), cur, acc);
    if p >= input.len() {
        assert(input.skip(p as int).len() == 0);
        lemma_scan_empty(input.skip(p as int), QState::Quoted, cur + run, acc);
        lemma_scan_empty(input.skip(p as int), QState::Plain, cur + run, acc);
    } else if input[p as int] == 0x5C {
        if p + 1 >= input.len() {
            lemma_quoted_step_escape_end(input, p, cur + run, acc);
            assert(input.skip(p as int + 1).len() == 0);
            lemma_scan_empty(input.skip(p as int + 1), QState::Plain, (cur + run).push(0x5C), acc);
            assert(input.subrange(position as int, p as int + 1) =~= run.push(0x5C));
            assert((cur + run).push(0x5C) =~= cur + run.push(0x5C));
        } else {
            lemma_quoted_step_escape(input, p, cur + run, acc);
            let d = input[p as int + 1];
            lemma_quoted_loop_scan(input, p + 2, (value + run).push(d), (cur + run).push(0x5C).push(d), acc);
            let p3 = f_quoted_loop(input, p + 2, (value + run).push(d)).1;
            assert(input.subrange(position as int, p3 as int)
                =~= run + seq![0x5Cu8, d] + input.subrange(p as int + 2, p3 as int));
            assert(cur + input.subrange(position as int, p3 as int)
                =~= (cur + run).push(0x5C).push(d) + input.subrange(p as int + 2, p3 as int));
        }
    } else {
        lemma_quoted_step_quote(input, p, cur + run, acc);
        assert(input.subrange(position as int, p as int + 1) =~= run.push(0x22));
        assert((cur + run).push(0x22) =~= cur + run.push(0x22));
    }
}

/// Fetch's "get, decode, and split" and the RFC's splitter read the same
/// bytes: from `position`, with the same piece so far and the same finished
/// pieces, they finish with the same list.
pub proof fn lemma_get_decode_split_loop_scan(input: Seq<u8>, position: nat, temp_value: Seq<u8>, values: Seq<Seq<u8>>)
    requires
        position <= input.len(),
    ensures
        f_get_decode_split_loop(input, position, temp_value, values)
            == split_scan(input.skip(position as int), QState::Plain, temp_value, values),
    decreases input.len() - position
{
    lemma_f_collect_loop(Until::QuoteOrComma, input, position, seq![]);
    let (run, p) = f_collect(Until::QuoteOrComma, input, position);
    assert(run =~= input.subrange(position as int, p as int));
    assert(input.skip(position as int) =~= run + input.skip(p as int));
    assert(super::lemmas::no_comma_or_quote(run)) by {
        assert forall|i: int| 0 <= i < run.len() implies (#[trigger] run[i]) != 0x2C && run[i] != 0x22 by {
            assert(run[i] == input[position + i]);
            assert(f_meets(Until::QuoteOrComma, input[position + i]));
        }
    }
    super::lemmas::lemma_scan_plain_run(run, input.skip(p as int), temp_value, values);
    let t = temp_value + run;
    if p < input.len() && input[p as int] == 0x22 {
        let (quoted, after) = f_collect_quoted(input, p, false);
        let (_, p2) = f_quoted_loop(input, p + 1, seq![]);
        super::termination::lemma_f_quoted_loop_position(input, p + 1, seq![]);
        assert(after == p2);
        assert(quoted =~= input.subrange(p as int, p2 as int));
        assert(input.skip(p as int)[0] == 0x22u8);
        assert(input.skip(p as int).drop_first() =~= input.skip(p as int + 1));
        lemma_quoted_loop_scan(input, p + 1, seq![], t.push(0x22), values);
        assert(t.push(0x22) + input.subrange(p as int + 1, p2 as int) =~= t + quoted) by {
            assert(quoted =~= seq![0x22u8] + input.subrange(p as int + 1, p2 as int));
        }
        if after < input.len() {
            lemma_get_decode_split_loop_scan(input, after, t + quoted, values);
        } else {
            assert(input.skip(after as int).len() == 0);
            lemma_scan_empty(input.skip(after as int), QState::Plain, t + quoted, values);
            lemma_trim_equals_strip_ows(t + quoted);
        }
    } else {
        lemma_trim_equals_strip_ows(t);
        if p >= input.len() {
            assert(input.skip(p as int).len() == 0);
            lemma_scan_empty(input.skip(p as int), QState::Plain, t, values);
        } else {
            assert(input[p as int] == 0x2C);
            assert(input.skip(p as int)[0] == 0x2Cu8);
            assert(input.skip(p as int).drop_first() =~= input.skip(p as int + 1));
            lemma_get_decode_split_loop_scan(input, p + 1, seq![], values.push(f_trim(t)));
        }
    }
}

/// Fetch's "get, decode, and split" gives the same pieces as `split_values`
/// on every byte sequence, the empty pieces included.
pub proof fn lemma_get_decode_split_equals_split_values(value: Seq<u8>)
    ensures
        f_get_decode_split(value) == split_values(value),
{
    lemma_get_decode_split_loop_scan(value, 0, seq![], seq![]);
    assert(value.skip(0) =~= value);
}

/// Dropping the empty pieces of Fetch's "get, decode, and split" is exactly
/// RFC 9110's list elements (§5.6.1.2): the one way the two differ.
pub proof fn lemma_get_decode_split_drop_empty(value: Seq<u8>)
    ensures
        drop_empty(f_get_decode_split(value)) == list_elements(value),
{
    lemma_get_decode_split_equals_split_values(value);
}

/// Fetch's "collect an HTTP quoted string" reads every RFC 9110
/// `quoted-string` to the same value and the same end: the loop, from a
/// position whose suffix the RFC parser reads as `(v, rest)`, gives
/// `(v, input.len() - rest.len())`.
pub proof fn lemma_quoted_loop_agrees(input: Seq<u8>, position: nat, value: Seq<u8>, v: Seq<u8>, rest: Seq<u8>)
    requires
        position <= input.len(),
        quoted_body(input.skip(position as int), value) == Some((v, rest)),
    ensures
        f_quoted_loop(input, position, value) == (v, (input.len() - rest.len()) as nat),
    decreases input.len() - position
{
    lemma_f_collect_loop(Until::QuoteOrBackslash, input, position, seq![]);
    let (run, p) = f_collect(Until::QuoteOrBackslash, input, position);
    assert(run =~= input.subrange(position as int, p as int));
    // Every byte of the run is `qdtext` (the RFC read it), so the RFC reader
    // passes over the run too.
    lemma_quoted_body_run(input, position, p, value);
    assert(quoted_body(input.skip(p as int), value + run) == Some((v, rest)));
    if p >= input.len() {
        assert(input.skip(p as int).len() == 0);
        assert(false);
    } else {
        let c = input[p as int];
        assert(input.skip(p as int)[0] == c);
        assert(input.skip(p as int).drop_first() =~= input.skip(p as int + 1));
        if c == 0x5C {
            assert(input.skip(p as int).len() >= 2);
            assert(input.skip(p as int)[1] == input[p as int + 1]);
            assert(input.skip(p as int).drop_first().drop_first() =~= input.skip(p as int + 2));
            lemma_quoted_loop_agrees(input, p + 2, (value + run).push(input[p as int + 1]), v, rest);
        } else {
            assert(c == 0x22);
            assert(rest =~= input.skip(p as int + 1));
            assert(v == value + run);
        }
    }
}

/// The RFC reader passes over a run of bytes none of which is DQUOTE or
/// backslash, once it has read the string they belong to: the run's bytes
/// are all `qdtext`.
pub proof fn lemma_quoted_body_run(input: Seq<u8>, position: nat, p: nat, value: Seq<u8>)
    requires
        position <= p <= input.len(),
        forall|i: int| position <= i < p ==> (#[trigger] input[i]) != 0x22 && input[i] != 0x5C,
        quoted_body(input.skip(position as int), value) is Some,
    ensures
        quoted_body(input.skip(position as int), value)
            == quoted_body(input.skip(p as int), value + input.subrange(position as int, p as int)),
    decreases p - position
{
    if position < p {
        let c = input[position as int];
        assert(input.skip(position as int)[0] == c);
        assert(input.skip(position as int).drop_first() =~= input.skip(position as int + 1));
        assert(is_qdtext(c));
        lemma_quoted_body_run(input, position + 1, p, value.push(c));
        assert(value.push(c) + input.subrange(position as int + 1, p as int)
            =~= value + input.subrange(position as int, p as int));
    } else {
        assert(input.subrange(position as int, position as int) =~= Seq::<u8>::empty());
        assert(value + Seq::<u8>::empty() =~= value);
    }
}

/// On every RFC 9110 `quoted-string` at the start of `input`, Fetch's
/// "collect an HTTP quoted string" (extract-value true) gives the same
/// value, and stops at the same place.
pub proof fn lemma_quoted_string_agrees(input: Seq<u8>, v: Seq<u8>, rest: Seq<u8>)
    requires
        parse_quoted_string(input) == Some((v, rest)),
    ensures
        f_collect_quoted(input, 0, true) == (v, (input.len() - rest.len()) as nat),
{
    assert(input.skip(1) =~= input.drop_first());
    lemma_quoted_loop_agrees(input, 1, seq![], v, rest);
}

} // verus!
