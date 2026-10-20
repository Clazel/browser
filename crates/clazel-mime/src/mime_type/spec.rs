//! Executable-style specification of MIME types, transcribed from the
//! WHATWG MIME Sniffing Standard §4, with the definitions it uses from
//! Fetch and Infra. Nothing here runs; it defines what "correct" means.
//! Every definition cites its standard, and each `// N.` comment is the
//! step number in the cited algorithm.
//!
//! Sources (each pinned; a review is against exactly this text):
//! - MIME Sniffing Standard, Living Standard, last updated 19 October 2026,
//!   commit `ba4b3c385b9765ddfe4a994e2bb89e0ab96068e2`,
//!   <https://mimesniff.spec.whatwg.org/>: §3 terminology (HTTP token code
//!   point, HTTP quoted-string token code point), §4.1 MIME type
//!   representation, §4.2 essence, §4.4 parse a MIME type (and from bytes),
//!   §4.5 serialize a MIME type (and to bytes), §4.6 MIME type groups.
//! - Fetch Standard, Living Standard, last updated 19 October 2026, commit
//!   `59afe349913d56898c947576216f1c2579308be7`,
//!   <https://fetch.spec.whatwg.org/>: §2.2 HTTP tab or space, HTTP
//!   whitespace, collect an HTTP quoted string.
//! - Infra Standard, Living Standard, last updated 19 October 2026, commit
//!   `459b7829230ad256a690dabd315db974469af8e7`,
//!   <https://infra.spec.whatwg.org/>: §4.5 isomorphic decode, §4.6 ASCII
//!   code point classes, §4.7 ASCII lowercase, ends with, isomorphic
//!   encode, collect a sequence of code points, §5.2 ordered maps.
//!
//! Not transcribed: §4.2 "supported by the user agent" and "minimize a
//! supported MIME type" (they depend on what a user agent supports, which
//! is not defined here), and §4.3 "valid MIME type string", which is RFC
//! 9110's `media-type` production; that production is transcribed, from
//! RFC 9110 itself, in [`super::independent`].
//!
//! Modelling choices (each one is a deliberate, reviewable deviation in form,
//! never in meaning):
//! - A string is a `Seq<u32>` of scalar values (as in `clazel-encoding`).
//!   Infra strings are sequences of 16-bit code units, interpreted as code
//!   points; every algorithm here reads strings by code point, so a
//!   sequence of code points is the same string. Lone surrogates cannot be
//!   represented; no algorithm here treats them specially, so nothing
//!   depends on them.
//! - A position variable is a `nat` index into the string; "past the end"
//!   is `position >= input.len()`. An algorithm that advances a position
//!   variable returns the new position alongside its result.
//! - Iteration ("while", "for each") is a recursive function carrying the
//!   loop's variables; "continue" is a recursive call, "break" returns.
//! - "Collect a sequence of code points" takes its condition as a
//!   [`Condition`], one variant per condition the algorithms here use.
//! - "Solely contains" a class of code points is a recursive check over the
//!   string (so that Verus can evaluate it on concrete inputs).
//! - An ordered map (Infra §5.2) is a `Seq` of (key, value) entries, in
//!   order. "Exists" and "set" are transcribed from Infra over that list.
//! - A MIME type record is the struct [`MimeTypeRecord`].
//! - "ends with" (Infra §4.7) is defined on code units; every suffix used
//!   here is ASCII, and an ASCII code unit only ever encodes the same ASCII
//!   code point, so the suffix test on code points is the same test.
//! - Two loops need a termination argument Verus cannot find alone. Their
//!   `#[via_fn]` proofs must sit in this module, so they are here, but each
//!   only calls lemmas in `termination.rs`; they add nothing to the meaning.
//! - String literals are `Seq<u32>` of their code points, written in hex
//!   with the text in the doc comment (`lit_*` at the end of this file).
//!   The unit tests in `groups.rs` check each against a Rust string
//!   literal, through the implementation that is proven to use it.
//! - Fetch "collect an HTTP quoted string" step 7 says "from positionStart
//!   to position, inclusive". Read literally that includes the code point
//!   after the closing quote, which contradicts the standard's own examples
//!   (`"Hello" World` gives `"Hello"`). We specify the evident intent
//!   (exclusive); see `docs/ERRATA.md`. MIME parsing calls it only with
//!   extract-value true, so this step is never used here.

#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ===========================================================================
// Infra §4.6 code points, and the MIME Sniffing §3 / Fetch §2.2 classes.
// ===========================================================================

/// ASCII upper alpha (Infra §4.6): "a code point in the range U+0041 (A) to
/// U+005A (Z), inclusive."
pub open spec fn is_ascii_upper_alpha(c: u32) -> bool {
    0x41 <= c <= 0x5A
}

/// ASCII lower alpha (Infra §4.6): "a code point in the range U+0061 (a) to
/// U+007A (z), inclusive."
pub open spec fn is_ascii_lower_alpha(c: u32) -> bool {
    0x61 <= c <= 0x7A
}

/// ASCII alpha (Infra §4.6): "an ASCII upper alpha or ASCII lower alpha."
pub open spec fn is_ascii_alpha(c: u32) -> bool {
    is_ascii_upper_alpha(c) || is_ascii_lower_alpha(c)
}

/// ASCII digit (Infra §4.6): "a code point in the range U+0030 (0) to
/// U+0039 (9), inclusive."
pub open spec fn is_ascii_digit(c: u32) -> bool {
    0x30 <= c <= 0x39
}

/// ASCII alphanumeric (Infra §4.6): "an ASCII digit or ASCII alpha."
pub open spec fn is_ascii_alphanumeric(c: u32) -> bool {
    is_ascii_digit(c) || is_ascii_alpha(c)
}

/// HTTP tab or space (Fetch §2.2): "U+0009 TAB or U+0020 SPACE."
pub open spec fn is_http_tab_or_space(c: u32) -> bool {
    c == 0x09 || c == 0x20
}

/// HTTP whitespace (Fetch §2.2): "U+000A LF, U+000D CR, or an HTTP tab or
/// space."
pub open spec fn is_http_whitespace(c: u32) -> bool {
    c == 0x0A || c == 0x0D || is_http_tab_or_space(c)
}

/// HTTP token code point (MIME Sniffing §3): "U+0021 (!), U+0023 (#),
/// U+0024 ($), U+0025 (%), U+0026 (&), U+0027 ('), U+002A (*), U+002B (+),
/// U+002D (-), U+002E (.), U+005E (^), U+005F (_), U+0060 (`), U+007C (|),
/// U+007E (~), or an ASCII alphanumeric."
pub open spec fn is_http_token_code_point(c: u32) -> bool {
    c == 0x21 || c == 0x23 || c == 0x24 || c == 0x25 || c == 0x26 || c == 0x27
        || c == 0x2A || c == 0x2B || c == 0x2D || c == 0x2E || c == 0x5E || c == 0x5F
        || c == 0x60 || c == 0x7C || c == 0x7E || is_ascii_alphanumeric(c)
}

/// HTTP quoted-string token code point (MIME Sniffing §3): "U+0009 TAB, a
/// code point in the range U+0020 SPACE to U+007E (~), inclusive, or a code
/// point in the range U+0080 through U+00FF (ÿ), inclusive."
pub open spec fn is_http_quoted_string_token_code_point(c: u32) -> bool {
    c == 0x09 || (0x20 <= c <= 0x7E) || (0x80 <= c <= 0xFF)
}

/// `s` solely contains HTTP token code points.
pub open spec fn solely_http_token_code_points(s: Seq<u32>) -> bool
    decreases s.len()
{
    s.len() == 0 || (is_http_token_code_point(s[0]) && solely_http_token_code_points(s.drop_first()))
}

/// `s` solely contains HTTP quoted-string token code points.
pub open spec fn solely_http_quoted_string_token_code_points(s: Seq<u32>) -> bool
    decreases s.len()
{
    s.len() == 0 || (is_http_quoted_string_token_code_point(s[0])
        && solely_http_quoted_string_token_code_points(s.drop_first()))
}

// ===========================================================================
// Infra §4.7 strings, and §4.5 / §4.7 isomorphic decode and encode.
// ===========================================================================

/// ASCII lowercase (Infra §4.7): "replace all ASCII upper alphas in the
/// string with their corresponding code point in ASCII lower alpha."
pub open spec fn ascii_lowercase(s: Seq<u32>) -> Seq<u32> {
    s.map_values(|c: u32| if is_ascii_upper_alpha(c) { (c + 0x20) as u32 } else { c })
}

/// "`input` ends with `suffix`" (Infra §4.7): `suffix` is a suffix of
/// `input` (see the modelling choices on code units).
pub open spec fn ends_with(input: Seq<u32>, suffix: Seq<u32>) -> bool {
    suffix.len() <= input.len() && input.subrange(input.len() - suffix.len(), input.len() as int) == suffix
}

/// Isomorphic decode (Infra §4.5): "return a string whose code point length
/// is equal to input's length and whose code points have the same values
/// as the values of input's bytes, in the same order."
pub open spec fn isomorphic_decode(input: Seq<u8>) -> Seq<u32> {
    input.map_values(|b: u8| b as u32)
}

/// Isomorphic encode (Infra §4.7): "1. Assert: input contains no code
/// points greater than U+00FF. 2. Return a byte sequence whose length is
/// equal to input's code point length and whose bytes have the same values
/// as the values of input's code points, in the same order." Callers meet
/// the assertion (`contract::serialize_to_bytes_requires`).
pub open spec fn isomorphic_encode(input: Seq<u32>) -> Seq<u8> {
    input.map_values(|c: u32| c as u8)
}

/// The conditions that "collect a sequence of code points" is given in the
/// algorithms below.
pub enum Condition {
    /// "not U+002F (/)" (parse a MIME type, step 3)
    NotSolidus,
    /// "not U+003B (;)" (parse a MIME type, steps 7, 11.8.2 and 11.9.1)
    NotSemicolon,
    /// "not U+003B (;) or U+003D (=)" (parse a MIME type, step 11.3)
    NotSemicolonOrEqualsSign,
    /// "HTTP whitespace" (parse a MIME type, step 11.2)
    HttpWhitespace,
    /// "not U+0022 (") or U+005C (\)" (collect an HTTP quoted string, step 5.1)
    NotQuotationMarkOrReverseSolidus,
}

/// Whether code point `c` meets `condition`.
pub open spec fn meets(condition: Condition, c: u32) -> bool {
    match condition {
        Condition::NotSolidus => c != 0x2F,
        Condition::NotSemicolon => c != 0x3B,
        Condition::NotSemicolonOrEqualsSign => c != 0x3B && c != 0x3D,
        Condition::HttpWhitespace => is_http_whitespace(c),
        Condition::NotQuotationMarkOrReverseSolidus => c != 0x22 && c != 0x5C,
    }
}

/// Collect a sequence of code points (Infra §4.7, #collect-a-sequence-of-code-points),
/// step 2's loop, with `result` as built so far. Returns (result, position).
pub open spec fn collect_loop(condition: Condition, input: Seq<u32>, position: nat, result: Seq<u32>) -> (Seq<u32>, nat)
    decreases input.len() - position
{
    // 2. "While position doesn't point past the end of input and the code
    //    point at position within input meets the condition condition:"
    if position < input.len() && meets(condition, input[position as int]) {
        // 2.1 "Append that code point to the end of result."
        // 2.2 "Advance position by 1."
        collect_loop(condition, input, position + 1, result.push(input[position as int]))
    } else {
        // 3. "Return result."
        (result, position)
    }
}

/// Collect a sequence of code points meeting `condition` from `input`,
/// given `position`. Returns (result, position).
pub open spec fn collect(condition: Condition, input: Seq<u32>, position: nat) -> (Seq<u32>, nat) {
    // 1. "Let result be the empty string." 2-3: the loop.
    collect_loop(condition, input, position, seq![])
}

/// Remove any leading HTTP whitespace from `s`.
pub open spec fn remove_leading_http_whitespace(s: Seq<u32>) -> Seq<u32>
    decreases s.len()
{
    if s.len() > 0 && is_http_whitespace(s[0]) {
        remove_leading_http_whitespace(s.drop_first())
    } else {
        s
    }
}

/// Remove any trailing HTTP whitespace from `s`.
pub open spec fn remove_trailing_http_whitespace(s: Seq<u32>) -> Seq<u32>
    decreases s.len()
{
    if s.len() > 0 && is_http_whitespace(s.last()) {
        remove_trailing_http_whitespace(s.drop_last())
    } else {
        s
    }
}

// ===========================================================================
// Infra §5.2 ordered maps, as a list of entries.
// ===========================================================================

/// An ordered map from strings to strings: its entries, in order.
pub type OrderedMap = Seq<(Seq<u32>, Seq<u32>)>;

/// "map[key] exists" (Infra §5.2): "if the map contains an entry with the
/// given key".
pub open spec fn map_exists(map: OrderedMap, key: Seq<u32>) -> bool
    decreases map.len()
{
    map.len() > 0 && (map[0].0 == key || map_exists(map.drop_first(), key))
}

/// "Set the value of an entry in an ordered map to a given value" (Infra
/// §5.2): "If the map contains an entry with the given key, then set the
/// value of that entry to the given value. Otherwise, add a new entry ...
/// to the end of the map." (A map has at most one entry per key, so the
/// first match is the entry.)
pub open spec fn map_set(map: OrderedMap, key: Seq<u32>, value: Seq<u32>) -> OrderedMap
    decreases map.len()
{
    if map.len() == 0 {
        seq![(key, value)]
    } else if map[0].0 == key {
        map.update(0, (key, value))
    } else {
        seq![map[0]] + map_set(map.drop_first(), key, value)
    }
}

// ===========================================================================
// MIME Sniffing §4.1 and §4.2.
// ===========================================================================

/// A MIME type record (§4.1, <https://mimesniff.spec.whatwg.org/#mime-type>).
pub struct MimeTypeRecord {
    /// type: "a non-empty ASCII string"
    pub type_: Seq<u32>,
    /// subtype: "a non-empty ASCII string"
    pub subtype: Seq<u32>,
    /// parameters: "an ordered map whose keys are ASCII strings and values
    /// are strings limited to HTTP quoted-string token code points. It is
    /// initially empty."
    pub parameters: OrderedMap,
}

/// The essence of a MIME type (§4.2, #mime-type-essence): "mimeType's type,
/// followed by U+002F (/), followed by mimeType's subtype."
pub open spec fn essence(mime_type: MimeTypeRecord) -> Seq<u32> {
    mime_type.type_ + seq![0x2Fu32] + mime_type.subtype
}

// ===========================================================================
// Fetch §2.2 collect an HTTP quoted string.
// ===========================================================================

/// Collect an HTTP quoted string (Fetch §2.2), step 5's "While true" loop,
/// with `value` as built so far. Returns (value, position).
pub open spec fn quoted_string_loop(input: Seq<u32>, position: nat, value: Seq<u32>) -> (Seq<u32>, nat)
    decreases input.len() - position via quoted_string_loop_decreases
{
    // 5.1 "Append the result of collecting a sequence of code points that
    //      are not U+0022 (") or U+005C (\) from input, given position, to
    //      value."
    let (collected, position) = collect(Condition::NotQuotationMarkOrReverseSolidus, input, position);
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
                quoted_string_loop(input, position + 1, value.push(input[position as int]))
            }
        } else {
            // 5.6 "Otherwise:" 5.6.1 asserts quoteOrBackslash is U+0022 ("),
            // which holds because step 5.1 stopped at it. 5.6.2 "Break."
            (value, position)
        }
    }
}

/// Termination of [`quoted_string_loop`]: collecting never moves backwards.
#[via_fn]
pub proof fn quoted_string_loop_decreases(input: Seq<u32>, position: nat, value: Seq<u32>) {
    super::termination::lemma_collect_loop_position(Condition::NotQuotationMarkOrReverseSolidus, input, position, seq![]);
}

/// Collect an HTTP quoted string (Fetch §2.2, #collect-an-http-quoted-string)
/// from `input`, given `position` and `extract_value`. Returns (the
/// string, position).
pub open spec fn collect_an_http_quoted_string(input: Seq<u32>, position: nat, extract_value: bool) -> (Seq<u32>, nat) {
    // 1. "Let positionStart be position."
    let position_start = position;
    // 2. "Let value be the empty string."
    // 3. "Assert: the code point at position within input is U+0022 (")."
    //    The one caller checks this first (parse a MIME type, step 11.8).
    // 4. "Advance position by 1."
    // 5. the loop.
    let (value, position) = quoted_string_loop(input, position + 1, seq![]);
    if extract_value {
        // 6. "If extract-value is true, then return value."
        (value, position)
    } else {
        // 7. "Return the code points from positionStart to position,
        //    inclusive, within input." Erratum: read literally, "inclusive"
        //    takes one code point past the closing quote, which contradicts
        //    the standard's examples; we take positionStart up to, not
        //    including, position (see docs/ERRATA.md).
        (input.subrange(position_start as int, position as int), position)
    }
}

// ===========================================================================
// MIME Sniffing §4.4 parse a MIME type.
// ===========================================================================

/// Remove any leading and trailing HTTP whitespace from `s`.
pub open spec fn remove_leading_and_trailing_http_whitespace(s: Seq<u32>) -> Seq<u32> {
    remove_trailing_http_whitespace(remove_leading_http_whitespace(s))
}

/// Parse a MIME type, step 11.10: set the parameter if every condition
/// holds; otherwise leave `mime_type` as it is.
pub open spec fn set_parameter_if_valid(mime_type: MimeTypeRecord, parameter_name: Seq<u32>, parameter_value: Seq<u32>) -> MimeTypeRecord {
    // 11.10 "If all of the following are true"
    if parameter_name.len() != 0
        // "parameterName solely contains HTTP token code points"
        && solely_http_token_code_points(parameter_name)
        // "parameterValue solely contains HTTP quoted-string token code points"
        && solely_http_quoted_string_token_code_points(parameter_value)
        // "mimeType's parameters[parameterName] does not exist"
        && !map_exists(mime_type.parameters, parameter_name)
    {
        // "then set mimeType's parameters[parameterName] to parameterValue."
        MimeTypeRecord { parameters: map_set(mime_type.parameters, parameter_name, parameter_value), ..mime_type }
    } else {
        mime_type
    }
}

/// Parse a MIME type (§4.4), step 11's loop: "While position is not past
/// the end of input:".
pub open spec fn parse_parameters(input: Seq<u32>, position: nat, mime_type: MimeTypeRecord) -> MimeTypeRecord
    decreases input.len() - position via parse_parameters_decreases
{
    if position >= input.len() {
        // Past the end: the loop ends; step 12 returns mimeType.
        mime_type
    } else {
        // 11.1 "Advance position by 1. (This skips past U+003B (;).)"
        let position = position + 1;
        // 11.2 "Collect a sequence of code points that are HTTP whitespace
        //      from input given position."
        let (_, position) = collect(Condition::HttpWhitespace, input, position);
        // 11.3 "Let parameterName be the result of collecting a sequence of
        //      code points that are not U+003B (;) or U+003D (=) from input,
        //      given position."
        let (parameter_name, position) = collect(Condition::NotSemicolonOrEqualsSign, input, position);
        // 11.4 "Set parameterName to parameterName, in ASCII lowercase."
        let parameter_name = ascii_lowercase(parameter_name);
        // 11.5 "If position is not past the end of input, then:"
        if position < input.len() && input[position as int] == 0x3B {
            // 11.5.1 "If the code point at position within input is U+003B
            //        (;), then continue."
            parse_parameters(input, position, mime_type)
        } else {
            // 11.5.2 "Advance position by 1. (This skips past U+003D (=).)"
            let position = if position < input.len() { position + 1 } else { position };
            if position >= input.len() {
                // 11.6 "If position is past the end of input, then break."
                mime_type
            } else {
                // 11.7 "Let parameterValue be null." (Each branch below sets
                //      it or continues, so null is never read.)
                if input[position as int] == 0x22 {
                    // 11.8 "If the code point at position within input is
                    //      U+0022 ("), then:"
                    // 11.8.1 "Set parameterValue to the result of collecting
                    //        an HTTP quoted string from input, given position
                    //        and true."
                    let (parameter_value, position) = collect_an_http_quoted_string(input, position, true);
                    // 11.8.2 "Collect a sequence of code points that are not
                    //        U+003B (;) from input, given position."
                    let (_, position) = collect(Condition::NotSemicolon, input, position);
                    // 11.10, then the next iteration.
                    parse_parameters(input, position, set_parameter_if_valid(mime_type, parameter_name, parameter_value))
                } else {
                    // 11.9 "Otherwise:"
                    // 11.9.1 "Set parameterValue to the result of collecting a
                    //        sequence of code points that are not U+003B (;)
                    //        from input, given position."
                    let (parameter_value, position) = collect(Condition::NotSemicolon, input, position);
                    // 11.9.2 "Remove any trailing HTTP whitespace from parameterValue."
                    let parameter_value = remove_trailing_http_whitespace(parameter_value);
                    if parameter_value.len() == 0 {
                        // 11.9.3 "If parameterValue is the empty string, then continue."
                        parse_parameters(input, position, mime_type)
                    } else {
                        // 11.10, then the next iteration.
                        parse_parameters(input, position, set_parameter_if_valid(mime_type, parameter_name, parameter_value))
                    }
                }
            }
        }
    }
}

/// Termination of [`parse_parameters`]: each iteration advances past at
/// least the U+003B (;) of step 11.1, and collecting never moves backwards.
#[via_fn]
pub proof fn parse_parameters_decreases(input: Seq<u32>, position: nat, mime_type: MimeTypeRecord) {
    if position < input.len() {
        let p1 = position + 1;
        super::termination::lemma_collect_loop_position(Condition::HttpWhitespace, input, p1, seq![]);
        let p2 = collect(Condition::HttpWhitespace, input, p1).1;
        super::termination::lemma_collect_loop_position(Condition::NotSemicolonOrEqualsSign, input, p2, seq![]);
        let p3 = collect(Condition::NotSemicolonOrEqualsSign, input, p2).1;
        if !(p3 < input.len() && input[p3 as int] == 0x3B) {
            let p4 = if p3 < input.len() { p3 + 1 } else { p3 };
            if p4 < input.len() {
                super::termination::lemma_quoted_string_loop_position(input, p4 + 1, seq![]);
                let p5 = collect_an_http_quoted_string(input, p4, true).1;
                assert(p5 == quoted_string_loop(input, p4 + 1, seq![]).1);
                super::termination::lemma_collect_loop_position(Condition::NotSemicolon, input, p5, seq![]);
                super::termination::lemma_collect_loop_position(Condition::NotSemicolon, input, p4, seq![]);
            }
        }
    }
}

/// Parse a MIME type (§4.4, <https://mimesniff.spec.whatwg.org/#parse-a-mime-type>).
/// `None` is failure.
pub open spec fn parse_a_mime_type(input: Seq<u32>) -> Option<MimeTypeRecord> {
    // 1. "Remove any leading and trailing HTTP whitespace from input."
    let input = remove_leading_and_trailing_http_whitespace(input);
    // 2. "Let position be a position variable for input, initially pointing
    //    at the start of input."
    let position = 0nat;
    // 3. "Let type be the result of collecting a sequence of code points
    //    that are not U+002F (/) from input, given position."
    let (type_, position) = collect(Condition::NotSolidus, input, position);
    if type_.len() == 0 || !solely_http_token_code_points(type_) {
        // 4. "If type is the empty string or does not solely contain HTTP
        //    token code points, then return failure."
        None
    } else if position >= input.len() {
        // 5. "If position is past the end of input, then return failure."
        None
    } else {
        // 6. "Advance position by 1. (This skips past U+002F (/).)"
        let position = position + 1;
        // 7. "Let subtype be the result of collecting a sequence of code
        //    points that are not U+003B (;) from input, given position."
        let (subtype, position) = collect(Condition::NotSemicolon, input, position);
        // 8. "Remove any trailing HTTP whitespace from subtype."
        let subtype = remove_trailing_http_whitespace(subtype);
        if subtype.len() == 0 || !solely_http_token_code_points(subtype) {
            // 9. "If subtype is the empty string or does not solely contain
            //    HTTP token code points, then return failure."
            None
        } else {
            // 10. "Let mimeType be a new MIME type record whose type is type,
            //     in ASCII lowercase, and subtype is subtype, in ASCII
            //     lowercase."
            let mime_type = MimeTypeRecord {
                type_: ascii_lowercase(type_),
                subtype: ascii_lowercase(subtype),
                parameters: seq![],
            };
            // 11. the loop; 12. "Return mimeType."
            Some(parse_parameters(input, position, mime_type))
        }
    }
}

/// Parse a MIME type from bytes (§4.4, #parse-a-mime-type-from-bytes).
pub open spec fn parse_a_mime_type_from_bytes(input: Seq<u8>) -> Option<MimeTypeRecord> {
    // 1. "Let string be input, isomorphic decoded."
    let string = isomorphic_decode(input);
    // 2. "Return the result of parse a MIME type with string."
    parse_a_mime_type(string)
}

// ===========================================================================
// MIME Sniffing §4.5 serialize a MIME type.
// ===========================================================================

/// Serialize a MIME type, step 2.4.1: "Precede each occurrence of U+0022
/// (") or U+005C (\) in value with U+005C (\)."
pub open spec fn precede_quotes_and_backslashes(value: Seq<u32>) -> Seq<u32>
    decreases value.len()
{
    if value.len() == 0 {
        seq![]
    } else if value[0] == 0x22 || value[0] == 0x5C {
        seq![0x5Cu32, value[0]] + precede_quotes_and_backslashes(value.drop_first())
    } else {
        seq![value[0]] + precede_quotes_and_backslashes(value.drop_first())
    }
}

/// Serialize a MIME type, step 2.4: the value as it is appended.
pub open spec fn serialize_value(value: Seq<u32>) -> Seq<u32> {
    if !solely_http_token_code_points(value) || value.len() == 0 {
        // 2.4 "If value does not solely contain HTTP token code points or
        //     value is the empty string, then:"
        // 2.4.1 (above), 2.4.2 "Prepend U+0022 (") to value.",
        // 2.4.3 "Append U+0022 (") to value."
        seq![0x22u32] + precede_quotes_and_backslashes(value) + seq![0x22u32]
    } else {
        value
    }
}

/// Serialize a MIME type, step 2: "For each name → value of mimeType's
/// parameters:", from entry `i`, with `serialization` as built so far.
pub open spec fn serialize_parameters(parameters: OrderedMap, i: nat, serialization: Seq<u32>) -> Seq<u32>
    decreases parameters.len() - i
{
    if i < parameters.len() {
        let (name, value) = parameters[i as int];
        // 2.1 "Append U+003B (;) to serialization."
        // 2.2 "Append name to serialization."
        // 2.3 "Append U+003D (=) to serialization."
        // 2.4 (in serialize_value) and 2.5 "Append value to serialization."
        let serialization = serialization + seq![0x3Bu32] + name + seq![0x3Du32] + serialize_value(value);
        serialize_parameters(parameters, i + 1, serialization)
    } else {
        serialization
    }
}

/// Serialize a MIME type (§4.5, <https://mimesniff.spec.whatwg.org/#serialize-a-mime-type>).
pub open spec fn serialize_a_mime_type(mime_type: MimeTypeRecord) -> Seq<u32> {
    // 1. "Let serialization be the concatenation of mimeType's type, U+002F
    //    (/), and mimeType's subtype."
    let serialization = mime_type.type_ + seq![0x2Fu32] + mime_type.subtype;
    // 2. the loop; 3. "Return serialization."
    serialize_parameters(mime_type.parameters, 0, serialization)
}

/// Serialize a MIME type to bytes (§4.5, #serialize-a-mime-type-to-bytes).
pub open spec fn serialize_a_mime_type_to_bytes(mime_type: MimeTypeRecord) -> Seq<u8> {
    // 1. "Let stringSerialization be the result of serialize a MIME type
    //    with mimeType."
    let string_serialization = serialize_a_mime_type(mime_type);
    // 2. "Return stringSerialization, isomorphic encoded."
    isomorphic_encode(string_serialization)
}

// ===========================================================================
// MIME Sniffing §4.6 MIME type groups.
// ===========================================================================

/// `s` is one of `list`.
pub open spec fn is_one_of(s: Seq<u32>, list: Seq<Seq<u32>>) -> bool
    decreases list.len()
{
    list.len() > 0 && (s == list[0] || is_one_of(s, list.drop_first()))
}

/// An image MIME type (§4.6): "a MIME type whose type is "image"."
pub open spec fn is_image_mime_type(mime_type: MimeTypeRecord) -> bool {
    mime_type.type_ == lit_image()
}

/// An audio or video MIME type (§4.6): "any MIME type whose type is "audio"
/// or "video", or whose essence is "application/ogg"."
pub open spec fn is_audio_or_video_mime_type(mime_type: MimeTypeRecord) -> bool {
    mime_type.type_ == lit_audio() || mime_type.type_ == lit_video() || essence(mime_type) == lit_application_ogg()
}

/// A font MIME type (§4.6): "any MIME type whose type is "font", or whose
/// essence is one of the following:"
pub open spec fn is_font_mime_type(mime_type: MimeTypeRecord) -> bool {
    mime_type.type_ == lit_font() || is_one_of(essence(mime_type), seq![
        lit_application_font_cff(),
        lit_application_font_otf(),
        lit_application_font_sfnt(),
        lit_application_font_ttf(),
        lit_application_font_woff(),
        lit_application_vnd_ms_fontobject(),
        lit_application_vnd_ms_opentype(),
    ])
}

/// A ZIP-based MIME type (§4.6): "any MIME type whose subtype ends in
/// "+zip" or whose essence is one of the following: application/zip".
pub open spec fn is_zip_based_mime_type(mime_type: MimeTypeRecord) -> bool {
    ends_with(mime_type.subtype, lit_plus_zip()) || is_one_of(essence(mime_type), seq![lit_application_zip()])
}

/// An archive MIME type (§4.6): "any MIME type whose essence is one of the
/// following:"
pub open spec fn is_archive_mime_type(mime_type: MimeTypeRecord) -> bool {
    is_one_of(essence(mime_type), seq![
        lit_application_x_rar_compressed(),
        lit_application_zip(),
        lit_application_x_gzip(),
    ])
}

/// An XML MIME type (§4.6): "any MIME type whose subtype ends in "+xml" or
/// whose essence is "text/xml" or "application/xml"."
pub open spec fn is_xml_mime_type(mime_type: MimeTypeRecord) -> bool {
    ends_with(mime_type.subtype, lit_plus_xml()) || essence(mime_type) == lit_text_xml()
        || essence(mime_type) == lit_application_xml()
}

/// An HTML MIME type (§4.6): "any MIME type whose essence is "text/html"."
pub open spec fn is_html_mime_type(mime_type: MimeTypeRecord) -> bool {
    essence(mime_type) == lit_text_html()
}

/// A scriptable MIME type (§4.6): "an XML MIME type, HTML MIME type, or any
/// MIME type whose essence is "application/pdf"."
pub open spec fn is_scriptable_mime_type(mime_type: MimeTypeRecord) -> bool {
    is_xml_mime_type(mime_type) || is_html_mime_type(mime_type) || essence(mime_type) == lit_application_pdf()
}

/// The JavaScript MIME type essence strings (§4.6, JavaScript MIME type), in
/// the standard's order.
pub open spec fn javascript_mime_type_essences() -> Seq<Seq<u32>> {
    seq![
        lit_application_ecmascript(),
        lit_application_javascript(),
        lit_application_x_ecmascript(),
        lit_application_x_javascript(),
        lit_text_ecmascript(),
        lit_text_javascript(),
        lit_text_javascript1_0(),
        lit_text_javascript1_1(),
        lit_text_javascript1_2(),
        lit_text_javascript1_3(),
        lit_text_javascript1_4(),
        lit_text_javascript1_5(),
        lit_text_jscript(),
        lit_text_livescript(),
        lit_text_x_ecmascript(),
        lit_text_x_javascript(),
    ]
}

/// A JavaScript MIME type (§4.6): "any MIME type whose essence is one of
/// the following:"
pub open spec fn is_javascript_mime_type(mime_type: MimeTypeRecord) -> bool {
    is_one_of(essence(mime_type), javascript_mime_type_essences())
}

/// "A string is a JavaScript MIME type essence match if it is an ASCII
/// case-insensitive match for one of the JavaScript MIME type essence
/// strings" (§4.6), from entry `i` of the list on.
pub open spec fn javascript_essence_match_from(s: Seq<u32>, i: nat) -> bool
    decreases javascript_mime_type_essences().len() - i
{
    i < javascript_mime_type_essences().len() && (
        // ASCII case-insensitive (Infra §4.7): "the ASCII lowercase of A is
        // the ASCII lowercase of B".
        ascii_lowercase(s) == ascii_lowercase(javascript_mime_type_essences()[i as int])
        || javascript_essence_match_from(s, i + 1))
}

/// A JavaScript MIME type essence match (§4.6).
pub open spec fn is_javascript_mime_type_essence_match(s: Seq<u32>) -> bool {
    javascript_essence_match_from(s, 0)
}

/// A JSON MIME type (§4.6): "any MIME type whose subtype ends in "+json" or
/// whose essence is "application/json" or "text/json"."
pub open spec fn is_json_mime_type(mime_type: MimeTypeRecord) -> bool {
    ends_with(mime_type.subtype, lit_plus_json()) || essence(mime_type) == lit_application_json()
        || essence(mime_type) == lit_text_json()
}

// ===========================================================================
// String literals (see the modelling choices). Each is the text in its doc
// comment, as code points.
// ===========================================================================

/// "`image`"
pub open spec fn lit_image() -> Seq<u32> {
    seq![0x69u32, 0x6D, 0x61, 0x67, 0x65]
}

/// "`audio`"
pub open spec fn lit_audio() -> Seq<u32> {
    seq![0x61u32, 0x75, 0x64, 0x69, 0x6F]
}

/// "`video`"
pub open spec fn lit_video() -> Seq<u32> {
    seq![0x76u32, 0x69, 0x64, 0x65, 0x6F]
}

/// "`font`"
pub open spec fn lit_font() -> Seq<u32> {
    seq![0x66u32, 0x6F, 0x6E, 0x74]
}

/// "`application/ogg`"
pub open spec fn lit_application_ogg() -> Seq<u32> {
    seq![0x61u32, 0x70, 0x70, 0x6C, 0x69, 0x63, 0x61, 0x74, 0x69, 0x6F, 0x6E, 0x2F, 0x6F, 0x67, 0x67]
}

/// "`application/font-cff`"
pub open spec fn lit_application_font_cff() -> Seq<u32> {
    seq![0x61u32, 0x70, 0x70, 0x6C, 0x69, 0x63, 0x61, 0x74, 0x69, 0x6F, 0x6E, 0x2F, 0x66, 0x6F, 0x6E, 0x74, 0x2D, 0x63, 0x66, 0x66]
}

/// "`application/font-otf`"
pub open spec fn lit_application_font_otf() -> Seq<u32> {
    seq![0x61u32, 0x70, 0x70, 0x6C, 0x69, 0x63, 0x61, 0x74, 0x69, 0x6F, 0x6E, 0x2F, 0x66, 0x6F, 0x6E, 0x74, 0x2D, 0x6F, 0x74, 0x66]
}

/// "`application/font-sfnt`"
pub open spec fn lit_application_font_sfnt() -> Seq<u32> {
    seq![0x61u32, 0x70, 0x70, 0x6C, 0x69, 0x63, 0x61, 0x74, 0x69, 0x6F, 0x6E, 0x2F, 0x66, 0x6F, 0x6E, 0x74, 0x2D, 0x73, 0x66, 0x6E, 0x74]
}

/// "`application/font-ttf`"
pub open spec fn lit_application_font_ttf() -> Seq<u32> {
    seq![0x61u32, 0x70, 0x70, 0x6C, 0x69, 0x63, 0x61, 0x74, 0x69, 0x6F, 0x6E, 0x2F, 0x66, 0x6F, 0x6E, 0x74, 0x2D, 0x74, 0x74, 0x66]
}

/// "`application/font-woff`"
pub open spec fn lit_application_font_woff() -> Seq<u32> {
    seq![0x61u32, 0x70, 0x70, 0x6C, 0x69, 0x63, 0x61, 0x74, 0x69, 0x6F, 0x6E, 0x2F, 0x66, 0x6F, 0x6E, 0x74, 0x2D, 0x77, 0x6F, 0x66, 0x66]
}

/// "`application/vnd.ms-fontobject`"
pub open spec fn lit_application_vnd_ms_fontobject() -> Seq<u32> {
    seq![0x61u32, 0x70, 0x70, 0x6C, 0x69, 0x63, 0x61, 0x74, 0x69, 0x6F, 0x6E, 0x2F, 0x76, 0x6E, 0x64, 0x2E, 0x6D, 0x73, 0x2D, 0x66, 0x6F, 0x6E, 0x74, 0x6F, 0x62, 0x6A, 0x65, 0x63, 0x74]
}

/// "`application/vnd.ms-opentype`"
pub open spec fn lit_application_vnd_ms_opentype() -> Seq<u32> {
    seq![0x61u32, 0x70, 0x70, 0x6C, 0x69, 0x63, 0x61, 0x74, 0x69, 0x6F, 0x6E, 0x2F, 0x76, 0x6E, 0x64, 0x2E, 0x6D, 0x73, 0x2D, 0x6F, 0x70, 0x65, 0x6E, 0x74, 0x79, 0x70, 0x65]
}

/// "`+zip`"
pub open spec fn lit_plus_zip() -> Seq<u32> {
    seq![0x2Bu32, 0x7A, 0x69, 0x70]
}

/// "`application/zip`"
pub open spec fn lit_application_zip() -> Seq<u32> {
    seq![0x61u32, 0x70, 0x70, 0x6C, 0x69, 0x63, 0x61, 0x74, 0x69, 0x6F, 0x6E, 0x2F, 0x7A, 0x69, 0x70]
}

/// "`application/x-rar-compressed`"
pub open spec fn lit_application_x_rar_compressed() -> Seq<u32> {
    seq![0x61u32, 0x70, 0x70, 0x6C, 0x69, 0x63, 0x61, 0x74, 0x69, 0x6F, 0x6E, 0x2F, 0x78, 0x2D, 0x72, 0x61, 0x72, 0x2D, 0x63, 0x6F, 0x6D, 0x70, 0x72, 0x65, 0x73, 0x73, 0x65, 0x64]
}

/// "`application/x-gzip`"
pub open spec fn lit_application_x_gzip() -> Seq<u32> {
    seq![0x61u32, 0x70, 0x70, 0x6C, 0x69, 0x63, 0x61, 0x74, 0x69, 0x6F, 0x6E, 0x2F, 0x78, 0x2D, 0x67, 0x7A, 0x69, 0x70]
}

/// "`+xml`"
pub open spec fn lit_plus_xml() -> Seq<u32> {
    seq![0x2Bu32, 0x78, 0x6D, 0x6C]
}

/// "`text/xml`"
pub open spec fn lit_text_xml() -> Seq<u32> {
    seq![0x74u32, 0x65, 0x78, 0x74, 0x2F, 0x78, 0x6D, 0x6C]
}

/// "`application/xml`"
pub open spec fn lit_application_xml() -> Seq<u32> {
    seq![0x61u32, 0x70, 0x70, 0x6C, 0x69, 0x63, 0x61, 0x74, 0x69, 0x6F, 0x6E, 0x2F, 0x78, 0x6D, 0x6C]
}

/// "`text/html`"
pub open spec fn lit_text_html() -> Seq<u32> {
    seq![0x74u32, 0x65, 0x78, 0x74, 0x2F, 0x68, 0x74, 0x6D, 0x6C]
}

/// "`application/pdf`"
pub open spec fn lit_application_pdf() -> Seq<u32> {
    seq![0x61u32, 0x70, 0x70, 0x6C, 0x69, 0x63, 0x61, 0x74, 0x69, 0x6F, 0x6E, 0x2F, 0x70, 0x64, 0x66]
}

/// "`application/ecmascript`"
pub open spec fn lit_application_ecmascript() -> Seq<u32> {
    seq![0x61u32, 0x70, 0x70, 0x6C, 0x69, 0x63, 0x61, 0x74, 0x69, 0x6F, 0x6E, 0x2F, 0x65, 0x63, 0x6D, 0x61, 0x73, 0x63, 0x72, 0x69, 0x70, 0x74]
}

/// "`application/javascript`"
pub open spec fn lit_application_javascript() -> Seq<u32> {
    seq![0x61u32, 0x70, 0x70, 0x6C, 0x69, 0x63, 0x61, 0x74, 0x69, 0x6F, 0x6E, 0x2F, 0x6A, 0x61, 0x76, 0x61, 0x73, 0x63, 0x72, 0x69, 0x70, 0x74]
}

/// "`application/x-ecmascript`"
pub open spec fn lit_application_x_ecmascript() -> Seq<u32> {
    seq![0x61u32, 0x70, 0x70, 0x6C, 0x69, 0x63, 0x61, 0x74, 0x69, 0x6F, 0x6E, 0x2F, 0x78, 0x2D, 0x65, 0x63, 0x6D, 0x61, 0x73, 0x63, 0x72, 0x69, 0x70, 0x74]
}

/// "`application/x-javascript`"
pub open spec fn lit_application_x_javascript() -> Seq<u32> {
    seq![0x61u32, 0x70, 0x70, 0x6C, 0x69, 0x63, 0x61, 0x74, 0x69, 0x6F, 0x6E, 0x2F, 0x78, 0x2D, 0x6A, 0x61, 0x76, 0x61, 0x73, 0x63, 0x72, 0x69, 0x70, 0x74]
}

/// "`text/ecmascript`"
pub open spec fn lit_text_ecmascript() -> Seq<u32> {
    seq![0x74u32, 0x65, 0x78, 0x74, 0x2F, 0x65, 0x63, 0x6D, 0x61, 0x73, 0x63, 0x72, 0x69, 0x70, 0x74]
}

/// "`text/javascript`"
pub open spec fn lit_text_javascript() -> Seq<u32> {
    seq![0x74u32, 0x65, 0x78, 0x74, 0x2F, 0x6A, 0x61, 0x76, 0x61, 0x73, 0x63, 0x72, 0x69, 0x70, 0x74]
}

/// "`text/javascript1.0`"
pub open spec fn lit_text_javascript1_0() -> Seq<u32> {
    seq![0x74u32, 0x65, 0x78, 0x74, 0x2F, 0x6A, 0x61, 0x76, 0x61, 0x73, 0x63, 0x72, 0x69, 0x70, 0x74, 0x31, 0x2E, 0x30]
}

/// "`text/javascript1.1`"
pub open spec fn lit_text_javascript1_1() -> Seq<u32> {
    seq![0x74u32, 0x65, 0x78, 0x74, 0x2F, 0x6A, 0x61, 0x76, 0x61, 0x73, 0x63, 0x72, 0x69, 0x70, 0x74, 0x31, 0x2E, 0x31]
}

/// "`text/javascript1.2`"
pub open spec fn lit_text_javascript1_2() -> Seq<u32> {
    seq![0x74u32, 0x65, 0x78, 0x74, 0x2F, 0x6A, 0x61, 0x76, 0x61, 0x73, 0x63, 0x72, 0x69, 0x70, 0x74, 0x31, 0x2E, 0x32]
}

/// "`text/javascript1.3`"
pub open spec fn lit_text_javascript1_3() -> Seq<u32> {
    seq![0x74u32, 0x65, 0x78, 0x74, 0x2F, 0x6A, 0x61, 0x76, 0x61, 0x73, 0x63, 0x72, 0x69, 0x70, 0x74, 0x31, 0x2E, 0x33]
}

/// "`text/javascript1.4`"
pub open spec fn lit_text_javascript1_4() -> Seq<u32> {
    seq![0x74u32, 0x65, 0x78, 0x74, 0x2F, 0x6A, 0x61, 0x76, 0x61, 0x73, 0x63, 0x72, 0x69, 0x70, 0x74, 0x31, 0x2E, 0x34]
}

/// "`text/javascript1.5`"
pub open spec fn lit_text_javascript1_5() -> Seq<u32> {
    seq![0x74u32, 0x65, 0x78, 0x74, 0x2F, 0x6A, 0x61, 0x76, 0x61, 0x73, 0x63, 0x72, 0x69, 0x70, 0x74, 0x31, 0x2E, 0x35]
}

/// "`text/jscript`"
pub open spec fn lit_text_jscript() -> Seq<u32> {
    seq![0x74u32, 0x65, 0x78, 0x74, 0x2F, 0x6A, 0x73, 0x63, 0x72, 0x69, 0x70, 0x74]
}

/// "`text/livescript`"
pub open spec fn lit_text_livescript() -> Seq<u32> {
    seq![0x74u32, 0x65, 0x78, 0x74, 0x2F, 0x6C, 0x69, 0x76, 0x65, 0x73, 0x63, 0x72, 0x69, 0x70, 0x74]
}

/// "`text/x-ecmascript`"
pub open spec fn lit_text_x_ecmascript() -> Seq<u32> {
    seq![0x74u32, 0x65, 0x78, 0x74, 0x2F, 0x78, 0x2D, 0x65, 0x63, 0x6D, 0x61, 0x73, 0x63, 0x72, 0x69, 0x70, 0x74]
}

/// "`text/x-javascript`"
pub open spec fn lit_text_x_javascript() -> Seq<u32> {
    seq![0x74u32, 0x65, 0x78, 0x74, 0x2F, 0x78, 0x2D, 0x6A, 0x61, 0x76, 0x61, 0x73, 0x63, 0x72, 0x69, 0x70, 0x74]
}

/// "`+json`"
pub open spec fn lit_plus_json() -> Seq<u32> {
    seq![0x2Bu32, 0x6A, 0x73, 0x6F, 0x6E]
}

/// "`application/json`"
pub open spec fn lit_application_json() -> Seq<u32> {
    seq![0x61u32, 0x70, 0x70, 0x6C, 0x69, 0x63, 0x61, 0x74, 0x69, 0x6F, 0x6E, 0x2F, 0x6A, 0x73, 0x6F, 0x6E]
}

/// "`text/json`"
pub open spec fn lit_text_json() -> Seq<u32> {
    seq![0x74u32, 0x65, 0x78, 0x74, 0x2F, 0x6A, 0x73, 0x6F, 0x6E]
}

} // verus!
