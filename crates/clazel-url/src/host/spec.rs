//! Executable-style specification of hosts, transcribed from the WHATWG
//! URL Standard §3 "Hosts (domains and IP addresses)": §3.1 host
//! representation, §3.2 forbidden host code points, §3.5 host parsing and
//! §3.6 host serializing, with the definitions they use from URL §1 and
//! Infra. Nothing here runs; it defines what "correct" means. Every
//! definition cites the standard, and each `// N.` comment is the step
//! number in the cited algorithm.
//!
//! Sources (each pinned; a review is against exactly this text):
//! - URL Standard, Living Standard, `url.bs` at commit
//!   `845bafca22fb0c5a42c4bf384a9bdea525a2f10d` (19 October 2026),
//!   <https://url.spec.whatwg.org/>: §1 "serialize an integer", §1.1
//!   validation errors, §1.2 parsers (pointer, c, remaining, EOF code
//!   point), §3.1, §3.2, §3.5, §3.6.
//! - Infra Standard, Living Standard, commit
//!   `459b7829230ad256a690dabd315db974469af8e7` (19 October 2026),
//!   <https://infra.spec.whatwg.org/>: §4.6 ASCII digit and hex digit,
//!   §4.7 collect a sequence of code points, strictly split.
//! - Percent-decoding and "UTF-8 percent-encode" (URL §1.3) come from
//!   `clazel-percent`'s spec, and "UTF-8 decode without BOM" (Encoding §6)
//!   from `clazel-encoding`'s.
//!
//! **The domain parser is `clazel-idna`'s (item 1.8):** host parser step 6
//! runs the "domain parser" (URL §3.3), which runs UTS #46 "Unicode
//! ToASCII". That algorithm is not transcribed here. [`host_parser`] takes
//! it as a parameter, `domain_parser`, and every theorem and contract about
//! the host parser holds *for every* `domain_parser` (it is universally
//! quantified, never assumed to behave in any way). The real one is
//! `clazel_idna::uts46::spec::domain_parser`, which
//! `contract::url_domain_parser` instantiates; the exec `host_parser_full`
//! is proven to compute `host_parser` with it. Not transcribed here: §3.3, §3.4
//! (valid host strings, which are defined through the domain parser), and
//! §3.2's public suffix and registrable domain (the Public Suffix List).
//!
//! Modelling choices (each one is a deliberate, reviewable deviation in form,
//! never in meaning):
//! - A string is a `Seq<u32>` of code points (as in `clazel-encoding`).
//!   Every algorithm here reads strings by code point.
//! - Validation errors (URL §1.1) are not modelled: they never change what
//!   an algorithm returns ("A validation error does not mean that the
//!   parser terminates"). Each step that only reports one is a comment
//!   saying so; a step that reports one *and* returns failure returns
//!   `None`.
//! - Failure is `None`; a result is `Some`.
//! - A host (§3.1) is the enum [`Host`]. An IPv4 address is a `nat` and an
//!   IPv6 address is a `Seq<nat>` of its pieces, so the algorithms' integer
//!   arithmetic is exact; `lemmas.rs` proves that the parsers only return
//!   values that fit (below 2^32; eight pieces below 2^16). A domain, an
//!   opaque host and the empty host are all strings in the standard; the
//!   enum records which one a result is. The opaque-host parser returns a
//!   string, and host parser step 2 returns it as an opaque host, or as
//!   the empty host if it is the empty string (an opaque host is non-empty,
//!   §3.1, and the empty host "is the empty string"; the URL parser's host
//!   state relies on this for `test://?`).
//! - A pointer (§1.2) is an `int`. [`c_at`] is "c": `None` is the EOF code
//!   point. "remaining starts with X" is "the code point after c is X".
//! - Iteration ("while", "for each") is a recursive function carrying the
//!   loop's variables; "continue" is a recursive call, "break" and
//!   "return" return. Where a loop's condition is false right after its
//!   body, the exit is folded into that branch, with a comment.
//! - IPv6 parser step 6.4 increases pointer and length together, so the
//!   pointer after it is the pointer before it plus length: the loop
//!   [`ipv6_hex_digits`] returns (value, length), and the caller adds
//!   length to the pointer. Step 6.5.2 "Decrease pointer by length" then
//!   gives back the pointer from before step 6.4.
//! - IPv4-in-IPv6 step 6.5.5.4 always runs at least once (step 6.5.5.3
//!   returned failure otherwise), so ipv4Piece is non-null after it; the
//!   loop [`ipv4_piece_digits`] is entered with the first digit's value.
//! - "Collect a sequence of code points" returns the collected string;
//!   position advances by its length.
//! - Infra "strictly split" asserts that each token after the first is
//!   preceded by the delimiter; that holds by construction here (a token
//!   ends at the delimiter or at the end).
//! - "Radix-R digit" (IPv4 number parser step 7) is not defined by the
//!   standard (its source says so). It is read as an ASCII hex digit whose
//!   value (step 8's "using ASCII hex digits for digits with values 0
//!   through 15") is less than R: for R = 10 the ASCII digits, for R = 8
//!   U+0030 (0) to U+0037 (7), for R = 16 the ASCII hex digits.
//! - One loop needs a termination argument Verus cannot find alone. Its
//!   `#[via_fn]` proof must sit in this module, so it is here, but it only
//!   calls a lemma in `termination.rs`; it adds nothing to the meaning.
//! - Assertions ("Assert: input is not the empty string") are `recommends`
//!   clauses; the contracts require them of callers.

#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------
// Infra §4.6 code points.
// ---------------------------------------------------------------------

/// Infra §4.6: "An ASCII digit is a code point in the range U+0030 (0) to
/// U+0039 (9), inclusive."
pub open spec fn is_ascii_digit(c: u32) -> bool {
    0x30 <= c <= 0x39
}

/// Infra §4.6: "An ASCII upper hex digit is an ASCII digit or a code point
/// in the range U+0041 (A) to U+0046 (F), inclusive." "An ASCII lower hex
/// digit is an ASCII digit or a code point in the range U+0061 (a) to
/// U+0066 (f), inclusive." "An ASCII hex digit is an ASCII upper hex digit
/// or ASCII lower hex digit."
pub open spec fn is_ascii_hex_digit(c: u32) -> bool {
    is_ascii_digit(c) || (0x41 <= c <= 0x46) || (0x61 <= c <= 0x66)
}

/// The value of an ASCII hex digit, "interpreted as a hexadecimal number":
/// 0 to 9, then A to F (and a to f) are 10 to 15.
pub open spec fn hex_digit_value(c: u32) -> nat {
    if is_ascii_digit(c) {
        (c - 0x30) as nat
    } else if 0x41 <= c <= 0x46 {
        (c - 0x37) as nat
    } else {
        (c - 0x57) as nat
    }
}

// ---------------------------------------------------------------------
// Infra §4.7 strings.
// ---------------------------------------------------------------------

/// Infra §4.7 "collect a sequence of code points" that are not equal to
/// `delimiter`, from `input`, given a position variable at `position`:
/// the collected string (see the modelling choices).
pub open spec fn collect_not_equal(input: Seq<u32>, delimiter: u32, position: nat) -> Seq<u32>
    decreases input.len() - position
{
    if position < input.len() && input[position as int] != delimiter {
        seq![input[position as int]] + collect_not_equal(input, delimiter, position + 1)
    } else {
        seq![]
    }
}

/// "Strictly split" step 5, the loop, from `position` with the tokens so
/// far.
pub open spec fn strictly_split_loop(input: Seq<u32>, delimiter: u32, position: nat, tokens: Seq<Seq<u32>>) -> Seq<Seq<u32>>
    decreases input.len() - position via strictly_split_loop_decreases
{
    // 5. "While position is not past the end of input:"
    if position >= input.len() {
        // 6. "Return tokens."
        tokens
    } else {
        // 5.1 "Assert: the code point at position within input is
        //     delimiter." (see the modelling choices)
        // 5.2 "Advance position by 1."
        // 5.3 "Let token be the result of collecting a sequence of code
        //     points that are not equal to delimiter from input, given
        //     position."
        let token = collect_not_equal(input, delimiter, position + 1);
        // 5.4 "Append token to tokens."
        strictly_split_loop(input, delimiter, position + 1 + token.len(), tokens.push(token))
    }
}

/// Termination of [`strictly_split_loop`]: a collected token never runs
/// past the end of the input.
#[via_fn]
pub proof fn strictly_split_loop_decreases(input: Seq<u32>, delimiter: u32, position: nat, tokens: Seq<Seq<u32>>) {
    if position < input.len() {
        super::termination::lemma_collect_not_equal_len(input, delimiter, position + 1);
    }
}

/// Infra §4.7: "To strictly split a string input on a particular delimiter
/// code point delimiter".
pub open spec fn strictly_split(input: Seq<u32>, delimiter: u32) -> Seq<Seq<u32>> {
    // 1. "Let position be a position variable for input, initially
    //    pointing at the start of input."
    // 2. "Let tokens be a list of strings, initially empty."
    // 3. "Let token be the result of collecting a sequence of code points
    //    that are not equal to delimiter from input, given position."
    let token = collect_not_equal(input, delimiter, 0);
    // 4. "Append token to tokens."
    strictly_split_loop(input, delimiter, token.len(), seq![token])
}

/// The string contains only ASCII digits (and may be empty).
pub open spec fn contains_only_ascii_digits(s: Seq<u32>) -> bool
    decreases s.len()
{
    s.len() == 0 || (is_ascii_digit(s.last()) && contains_only_ascii_digits(s.drop_last()))
}

// ---------------------------------------------------------------------
// URL §1: integers.
// ---------------------------------------------------------------------

/// URL §1: "To serialize an integer, represent it as the shortest possible
/// decimal number."
pub open spec fn serialize_integer(n: nat) -> Seq<u32>
    decreases n
{
    if n < 10 {
        seq![(0x30 + n) as u32]
    } else {
        serialize_integer(n / 10) + seq![(0x30 + n % 10) as u32]
    }
}

/// The lowercase hexadecimal digit for `n` < 16.
pub open spec fn lowercase_hex_digit(n: nat) -> u32 {
    if n < 10 {
        (0x30 + n) as u32
    } else {
        (0x57 + n) as u32
    }
}

/// `n` "represented as the shortest possible lowercase hexadecimal number"
/// (IPv6 serializer step 4.4).
pub open spec fn shortest_lowercase_hex(n: nat) -> Seq<u32>
    decreases n
{
    if n < 16 {
        seq![lowercase_hex_digit(n)]
    } else {
        shortest_lowercase_hex(n / 16) + seq![lowercase_hex_digit(n % 16)]
    }
}

/// `256` to the power `e`.
pub open spec fn pow256(e: nat) -> nat
    decreases e
{
    if e == 0 {
        1
    } else {
        256 * pow256((e - 1) as nat)
    }
}

// ---------------------------------------------------------------------
// URL §1.2 parsers: pointer and c.
// ---------------------------------------------------------------------

/// "c", the code point a pointer for `input` points to; `None` is the EOF
/// code point ("If it is greater than or equal to input's code point
/// length, it points to the EOF code point").
pub open spec fn c_at(input: Seq<u32>, pointer: int) -> Option<u32> {
    if 0 <= pointer < input.len() {
        Some(input[pointer])
    } else {
        None
    }
}

// ---------------------------------------------------------------------
// §3.1 Host representation, §3.2 Host miscellaneous.
// ---------------------------------------------------------------------

/// §3.1: "A host is a domain, an IP address, an opaque host, or an empty
/// host."
pub enum Host {
    /// "A domain is a non-empty ASCII string that identifies a realm within
    /// a network."
    Domain(Seq<u32>),
    /// "An IPv4 address is a 32-bit unsigned integer that identifies a
    /// network address."
    Ipv4(nat),
    /// "An IPv6 address is a 128-bit unsigned integer [...] composed of a
    /// list of 8 16-bit unsigned integers, also known as an IPv6 address's
    /// pieces."
    Ipv6(Seq<nat>),
    /// "An opaque host is a non-empty ASCII string that can be used for
    /// further processing."
    Opaque(Seq<u32>),
    /// "An empty host is the empty string."
    Empty,
}

/// §3.2: "A forbidden host code point is U+0000 NULL, U+0009 TAB, U+000A
/// LF, U+000D CR, U+0020 SPACE, U+0023 (#), U+002F (/), U+003A (:), U+003C
/// (<), U+003E (>), U+003F (?), U+0040 (@), U+005B ([), U+005C (\), U+005D
/// (]), U+005E (^), or U+007C (|)."
pub open spec fn is_forbidden_host_code_point(c: u32) -> bool {
    c == 0x00 || c == 0x09 || c == 0x0A || c == 0x0D || c == 0x20 || c == 0x23 || c == 0x2F
        || c == 0x3A || c == 0x3C || c == 0x3E || c == 0x3F || c == 0x40 || c == 0x5B
        || c == 0x5C || c == 0x5D || c == 0x5E || c == 0x7C
}

/// `s` contains a forbidden host code point at index `i` or later.
pub open spec fn contains_forbidden_host_code_point_from(s: Seq<u32>, i: nat) -> bool
    decreases s.len() - i
{
    i < s.len() && (is_forbidden_host_code_point(s[i as int]) || contains_forbidden_host_code_point_from(s, i + 1))
}

/// The domain parser (§3.3), which `clazel-idna` (item 1.8) provides: given a scalar value
/// string and beStrict, failure (`None`) or a domain. See the header.
pub type DomainParser = spec_fn(Seq<u32>, bool) -> Option<Seq<u32>>;

// ---------------------------------------------------------------------
// §3.5 Host parsing: the host parser.
// ---------------------------------------------------------------------

/// "The host parser takes a scalar value string input with an optional
/// boolean isOpaque (default false), and then runs these steps. They return
/// failure or a host." (<https://url.spec.whatwg.org/#concept-host-parser>)
/// Step 6's domain parser is the parameter `domain_parser` (see the
/// header).
pub open spec fn host_parser(input: Seq<u32>, is_opaque: bool, domain_parser: DomainParser) -> Option<Host>
    recommends
        is_opaque || input.len() > 0,
{
    // 1. "If input starts with U+005B ([), then:"
    if input.len() > 0 && input[0] == 0x5B {
        if input.last() != 0x5D {
            // 1.1 "If input does not end with U+005D (]), IPv6-unclosed
            //     validation error, return failure."
            None
        } else {
            // 1.2 "Return the result of IPv6 parsing input with its leading
            //     U+005B ([) and trailing U+005D (]) removed."
            match ipv6_parser(input.subrange(1, input.len() - 1)) {
                Some(address) => Some(Host::Ipv6(address)),
                None => None,
            }
        }
    } else if is_opaque {
        // 2. "If isOpaque is true, then return the result of opaque-host
        //    parsing input." (An empty result is the empty host; see the
        //    modelling choices.)
        match opaque_host_parser(input) {
            Some(s) => if s.len() == 0 {
                Some(Host::Empty)
            } else {
                Some(Host::Opaque(s))
            },
            None => None,
        }
    } else {
        // 3. "Assert: input is not the empty string." (recommends)
        // 4. "If input contains a percent-encoded byte, domain-percent-encoded
        //    validation error." (validation error only)
        // 5. "Let domain be the result of running UTF-8 decode without BOM
        //    on the percent-decoding of input."
        let domain = clazel_encoding::utf8::spec::utf8_decode_without_bom(
            clazel_percent::spec::percent_decode_string(input),
        );
        // 6. "Let asciiDomain be the result of running domain parser with
        //    domain and false."
        let ascii_domain = domain_parser(domain, false);
        match ascii_domain {
            // 7. "If asciiDomain is failure, then return failure."
            None => None,
            Some(ascii_domain) => if ends_in_a_number(ascii_domain) {
                // 8. "If asciiDomain ends in a number:"
                // 8.1 "If domain is not an ASCII string,
                //     IPv4-non-ASCII-input validation error." (validation
                //     error only)
                // 8.2 "Return the result of IPv4 parsing asciiDomain."
                match ipv4_parser(ascii_domain) {
                    Some(address) => Some(Host::Ipv4(address)),
                    None => None,
                }
            } else {
                // 9. "Return asciiDomain."
                Some(Host::Domain(ascii_domain))
            },
        }
    }
}

// ---------------------------------------------------------------------
// §3.5: the ends in a number checker, the IPv4 parser and the IPv4
// number parser.
// ---------------------------------------------------------------------

/// "The ends in a number checker takes an ASCII string input and then runs
/// these steps. They return a boolean."
pub open spec fn ends_in_a_number(input: Seq<u32>) -> bool
    recommends
        input.len() > 0,
{
    // 1. "Assert: input is not the empty string." (recommends)
    // 2. "Let parts be the result of strictly splitting input on U+002E
    //    (.)."
    let parts = strictly_split(input, 0x2E);
    // 3. "If the last item in parts is the empty string, then remove the
    //    last item from parts."
    let parts = if parts.last().len() == 0 {
        parts.drop_last()
    } else {
        parts
    };
    // 4. "Let last be the last item in parts."
    let last = parts.last();
    if last.len() > 0 && contains_only_ascii_digits(last) {
        // 5. "If last is not the empty string and contains only ASCII
        //    digits, then return true."
        true
    } else if ipv4_number_parser(last) is Some {
        // 6. "If parsing last as an IPv4 number does not return failure,
        //    then return true."
        true
    } else {
        // 7. "Return false."
        false
    }
}

/// An ASCII hex digit whose value is less than `r` (IPv4 number parser
/// step 7's "radix-R digit"; see the modelling choices).
pub open spec fn is_radix_digit(c: u32, r: nat) -> bool {
    is_ascii_hex_digit(c) && hex_digit_value(c) < r
}

/// Every code point of `s` is a radix-`r` digit.
pub open spec fn all_radix_digits(s: Seq<u32>, r: nat) -> bool
    decreases s.len()
{
    s.len() == 0 || (is_radix_digit(s.last(), r) && all_radix_digits(s.drop_last(), r))
}

/// "The mathematical integer value that is represented by input in
/// radix-R notation, using ASCII hex digits for digits with values 0
/// through 15" (IPv4 number parser step 8), most significant digit first.
pub open spec fn radix_value(s: Seq<u32>, r: nat) -> nat
    decreases s.len()
{
    if s.len() == 0 {
        0
    } else {
        radix_value(s.drop_last(), r) * r + hex_digit_value(s.last())
    }
}

/// "The IPv4 number parser takes an ASCII string input and then runs these
/// steps. They return failure or a tuple of a number and a boolean."
pub open spec fn ipv4_number_parser(input: Seq<u32>) -> Option<(nat, bool)> {
    if input.len() == 0 {
        // 1. "If input is the empty string, then return failure."
        None
    } else {
        // 2. "Let validationError be false."
        // 3. "Let R be 10."
        let (validation_error, input, r) = if input.len() >= 2 && input[0] == 0x30 && (input[1] == 0x58
            || input[1] == 0x78) {
            // 4. "If input contains at least two code points and the first
            //    two code points are either "0X" or "0x", then:"
            // 4.1 "Set validationError to true."
            // 4.2 "Remove the first two code points from input."
            // 4.3 "Set R to 16."
            (true, input.subrange(2, input.len() as int), 16nat)
        } else if input.len() >= 2 && input[0] == 0x30 {
            // 5. "Otherwise, if input contains at least two code points and
            //    the first code point is U+0030 (0), then:"
            // 5.1 "Set validationError to true."
            // 5.2 "Remove the first code point from input."
            // 5.3 "Set R to 8."
            (true, input.subrange(1, input.len() as int), 8nat)
        } else {
            (false, input, 10nat)
        };
        if input.len() == 0 {
            // 6. "If input is the empty string, then return (0, true)."
            Some((0nat, true))
        } else if !all_radix_digits(input, r) {
            // 7. "If input contains a code point that is not a radix-R
            //    digit, then return failure."
            None
        } else {
            // 8. "Let output be the mathematical integer value that is
            //    represented by input in radix-R notation, using ASCII hex
            //    digits for digits with values 0 through 15."
            let output = radix_value(input, r);
            // 9. "Return (output, validationError)."
            Some((output, validation_error))
        }
    }
}

/// IPv4 parser step 6, "For each part of parts", from index `i`, with the
/// numbers appended so far.
pub open spec fn ipv4_parse_parts(parts: Seq<Seq<u32>>, i: nat, numbers: Seq<nat>) -> Option<Seq<nat>>
    decreases parts.len() - i
{
    if i >= parts.len() {
        Some(numbers)
    } else {
        // 6.1 "Let result be the result of parsing part."
        match ipv4_number_parser(parts[i as int]) {
            // 6.2 "If result is failure, IPv4-non-numeric-part validation
            //     error, return failure."
            None => None,
            // 6.3 "If result[1] is true, IPv4-non-decimal-part validation
            //     error." (validation error only)
            // 6.4 "Append result[0] to numbers."
            Some(result) => ipv4_parse_parts(parts, i + 1, numbers.push(result.0)),
        }
    }
}

/// Some item of `numbers` from index `i` up to `end` (exclusive) is
/// greater than 255.
pub open spec fn any_greater_than_255(numbers: Seq<nat>, i: nat, end: nat) -> bool
    decreases end - i
{
    i < end && (numbers[i as int] > 255 || any_greater_than_255(numbers, i + 1, end))
}

/// IPv4 parser step 13, "For each n of numbers", from index `counter`
/// (counter is n's index), with ipv4 so far.
pub open spec fn ipv4_sum(numbers: Seq<nat>, counter: nat, ipv4: nat) -> nat
    decreases numbers.len() - counter
{
    if counter >= numbers.len() {
        ipv4
    } else {
        // 13.1 "Increment ipv4 by n × 256^(3 − counter)."
        // 13.2 "Increment counter by 1."
        ipv4_sum(numbers, counter + 1, ipv4 + numbers[counter as int] * pow256((3 - counter) as nat))
    }
}

/// "The IPv4 parser takes an ASCII string input and then runs these steps.
/// They return failure or an IPv4 address."
/// (<https://url.spec.whatwg.org/#concept-ipv4-parser>)
pub open spec fn ipv4_parser(input: Seq<u32>) -> Option<nat> {
    // 1. "Let parts be the result of strictly splitting input on U+002E (.)."
    let parts = strictly_split(input, 0x2E);
    // 2. "If the last item in parts is the empty string, then:"
    // 2.1 "IPv4-empty-part validation error." (validation error only)
    // 2.2 "If parts's size is greater than 1, then remove the last item
    //     from parts."
    let parts = if parts.last().len() == 0 && parts.len() > 1 {
        parts.drop_last()
    } else {
        parts
    };
    // 3. "If parts's size is less than 4, IPv4-too-few-parts validation
    //    error." (validation error only)
    if parts.len() > 4 {
        // 4. "If parts's size is greater than 4, IPv4-too-many-parts
        //    validation error, return failure."
        None
    } else {
        // 5. "Let numbers be an empty list."
        // 6. "For each part of parts:"
        match ipv4_parse_parts(parts, 0, seq![]) {
            None => None,
            Some(numbers) => {
                // 7. "If any item in numbers is greater than 255,
                //    IPv4-out-of-range-part validation error." (validation
                //    error only)
                if any_greater_than_255(numbers, 0, (numbers.len() - 1) as nat) {
                    // 8. "If any but the last item in numbers is greater
                    //    than 255, then return failure."
                    None
                } else if numbers.last() >= pow256((5 - numbers.len()) as nat) {
                    // 9. "If the last item in numbers is greater than or
                    //    equal to 256^(5 − numbers's size), then return
                    //    failure."
                    None
                } else {
                    // 10. "Let ipv4 be the last item in numbers."
                    let ipv4 = numbers.last();
                    // 11. "Remove the last item from numbers."
                    let numbers = numbers.drop_last();
                    // 12. "Let counter be 0."
                    // 13. "For each n of numbers:"
                    // 14. "Return ipv4."
                    Some(ipv4_sum(numbers, 0, ipv4))
                }
            },
        }
    }
}

// ---------------------------------------------------------------------
// §3.5: the IPv6 parser.
// ---------------------------------------------------------------------

/// IPv6 parser step 6.4: "While length is less than 4 and c is an ASCII
/// hex digit, set value to value × 0x10 + c interpreted as a hexadecimal
/// number, and increase pointer and length by 1." The pointer is
/// `start + length` (see the modelling choices). Returns (value, length).
pub open spec fn ipv6_hex_digits(input: Seq<u32>, start: int, value: nat, length: nat) -> (nat, nat)
    decreases 4 - length
{
    if length >= 4 {
        (value, length)
    } else {
        match c_at(input, start + length) {
            Some(c) if is_ascii_hex_digit(c) => ipv6_hex_digits(
                input,
                start,
                value * 0x10 + hex_digit_value(c),
                length + 1,
            ),
            _ => (value, length),
        }
    }
}

/// IPv4-in-IPv6 step 6.5.5.4, "While c is an ASCII digit", with ipv4Piece
/// so far (non-null; see the modelling choices) and the pointer. Returns
/// failure or (ipv4Piece, pointer).
pub open spec fn ipv4_piece_digits(input: Seq<u32>, pointer: int, ipv4_piece: nat) -> Option<(nat, int)>
    decreases input.len() - pointer
{
    match c_at(input, pointer) {
        Some(c) if is_ascii_digit(c) => {
        // 6.5.5.4.1 "Let number be c interpreted as decimal number."
        let number = (c - 0x30) as nat;
        // 6.5.5.4.2 "If ipv4Piece is null, then set ipv4Piece to number."
        //     (Not taken here: ipv4Piece is non-null.)
        if ipv4_piece == 0 {
            // 6.5.5.4.3 "Otherwise, if ipv4Piece is 0,
            //     IPv4-in-IPv6-invalid-code-point validation error, return
            //     failure."
            None
        } else {
            // 6.5.5.4.4 "Otherwise, set ipv4Piece to ipv4Piece × 10 +
            //     number."
            let ipv4_piece = ipv4_piece * 10 + number;
            if ipv4_piece > 255 {
                // 6.5.5.4.5 "If ipv4Piece is greater than 255,
                //     IPv4-in-IPv6-out-of-range-part validation error,
                //     return failure."
                None
            } else {
                // 6.5.5.4.6 "Increase pointer by 1."
                ipv4_piece_digits(input, pointer + 1, ipv4_piece)
            }
        }
        },
        _ => Some((ipv4_piece, pointer)),
    }
}

/// IPv6 parser step 6.5.5, "While c is not the EOF code point", with
/// address, pieceIndex, numbersSeen and pointer. Returns failure or
/// (address, pieceIndex, numbersSeen) when c is the EOF code point.
pub open spec fn ipv4_in_ipv6(input: Seq<u32>, address: Seq<nat>, piece_index: int, numbers_seen: nat, pointer: int) -> Option<(Seq<nat>, int, nat)>
    decreases 4 - numbers_seen
{
    match c_at(input, pointer) {
        None => Some((address, piece_index, numbers_seen)),
        Some(c) => {
            // 6.5.5.1 "Let ipv4Piece be null."
            // 6.5.5.2 "If numbersSeen is greater than 0, then:"
            if numbers_seen > 0 && !(c == 0x2E && numbers_seen < 4) {
                // 6.5.5.2.2 "Otherwise, IPv4-in-IPv6-invalid-code-point
                //     validation error, return failure."
                None
            } else {
                // 6.5.5.2.1 "If c is a U+002E (.) and numbersSeen is less
                //     than 4, then increase pointer by 1."
                let pointer = if numbers_seen > 0 {
                    pointer + 1
                } else {
                    pointer
                };
                match c_at(input, pointer) {
                    Some(c) if is_ascii_digit(c) => {
                        // 6.5.5.4 "While c is an ASCII digit:", first time
                        //     round: 6.5.5.4.1 number; 6.5.5.4.2 "If
                        //     ipv4Piece is null, then set ipv4Piece to
                        //     number."; 6.5.5.4.5 (a single digit is at
                        //     most 9); 6.5.5.4.6 "Increase pointer by 1."
                        match ipv4_piece_digits(input, pointer + 1, (c - 0x30) as nat) {
                            None => None,
                            Some((ipv4_piece, pointer)) => {
                                // 6.5.5.5 "Set address[pieceIndex] to
                                //     address[pieceIndex] × 0x100 +
                                //     ipv4Piece."
                                let address = address.update(piece_index, address[piece_index] * 0x100 + ipv4_piece);
                                // 6.5.5.6 "Increase numbersSeen by 1."
                                let numbers_seen = numbers_seen + 1;
                                // 6.5.5.7 "If numbersSeen is 2 or 4, then
                                //     increase pieceIndex by 1."
                                let piece_index = if numbers_seen == 2 || numbers_seen == 4 {
                                    piece_index + 1
                                } else {
                                    piece_index
                                };
                                ipv4_in_ipv6(input, address, piece_index, numbers_seen, pointer)
                            },
                        }
                    },
                    // 6.5.5.3 "If c is not an ASCII digit,
                    //     IPv4-in-IPv6-invalid-code-point validation error,
                    //     return failure."
                    _ => None,
                }
            }
        },
    }
}

/// IPv6 parser step 6, "While c is not the EOF code point", with address,
/// pieceIndex, compress and pointer. Returns failure or (address,
/// pieceIndex, compress) when the loop ends.
pub open spec fn ipv6_main_loop(input: Seq<u32>, address: Seq<nat>, piece_index: int, compress: Option<int>, pointer: int) -> Option<(Seq<nat>, int, Option<int>)>
    decreases input.len() - pointer
{
    match c_at(input, pointer) {
        None => Some((address, piece_index, compress)),
        Some(c) => if piece_index == 8 {
            // 6.1 "If pieceIndex is 8, IPv6-too-many-pieces validation
            //     error, return failure."
            None
        } else if c == 0x3A {
            // 6.2 "If c is U+003A (:), then:"
            if compress is Some {
                // 6.2.1 "If compress is non-null, IPv6-multiple-compression
                //     validation error, return failure."
                None
            } else {
                // 6.2.2 "Increase pointer and pieceIndex by 1, set compress
                //     to pieceIndex, and then continue."
                ipv6_main_loop(input, address, piece_index + 1, Some(piece_index + 1), pointer + 1)
            }
        } else {
            // 6.3 "Let value and length be 0."
            // 6.4 "While length is less than 4 and c is an ASCII hex digit,
            //     [...]"
            let (value, length) = ipv6_hex_digits(input, pointer, 0, 0);
            let after = pointer + length;
            match c_at(input, after) {
                Some(c) if c == 0x2E => {
                    // 6.5 "If c is U+002E (.), then:"
                    if length == 0 {
                        // 6.5.1 "If length is 0, IPv4-in-IPv6-invalid-code-point
                        //     validation error, return failure."
                        None
                    } else if piece_index > 6 {
                        // 6.5.2 "Decrease pointer by length." (back to
                        //     `pointer`)
                        // 6.5.3 "If pieceIndex is greater than 6,
                        //     IPv4-in-IPv6-too-many-pieces validation
                        //     error, return failure."
                        None
                    } else {
                        // 6.5.4 "Let numbersSeen be 0."
                        // 6.5.5 "While c is not the EOF code point:"
                        match ipv4_in_ipv6(input, address, piece_index, 0, pointer) {
                            None => None,
                            Some((address, piece_index, numbers_seen)) => if numbers_seen != 4 {
                                // 6.5.6 "If numbersSeen is not 4,
                                //     IPv4-in-IPv6-too-few-parts validation
                                //     error, return failure."
                                None
                            } else {
                                // 6.5.7 "Break."
                                Some((address, piece_index, compress))
                            },
                        }
                    }
                },
                Some(c) if c == 0x3A => {
                    // 6.6 "Otherwise, if c is U+003A (:):"
                    // 6.6.1 "Increase pointer by 1."
                    if c_at(input, after + 1) is None {
                        // 6.6.2 "If c is the EOF code point,
                        //     IPv6-invalid-code-point validation error,
                        //     return failure."
                        None
                    } else {
                        // 6.8 "If length is greater than 1 and value is less
                        //     than 0x10^(length − 1), IPv6-piece-leading-zero
                        //     validation error." (validation error only)
                        // 6.9 "Set address[pieceIndex] to value."
                        // 6.10 "Increase pieceIndex by 1."
                        ipv6_main_loop(input, address.update(piece_index, value), piece_index + 1, compress, after + 1)
                    }
                },
                // 6.7 "Otherwise, if c is not the EOF code point,
                //     IPv6-invalid-code-point validation error, return
                //     failure."
                Some(_) => None,
                None => {
                    // c is the EOF code point. 6.8 (validation error
                    // only); 6.9 "Set address[pieceIndex] to value."; 6.10
                    // "Increase pieceIndex by 1."; and then the loop ends,
                    // because c is the EOF code point.
                    Some((address.update(piece_index, value), piece_index + 1, compress))
                },
            }
        },
    }
}

/// IPv6 parser step 7.3: "While pieceIndex is not 0 and swaps is greater
/// than 0, swap address[pieceIndex] with address[compress + swaps − 1], and
/// then decrease both pieceIndex and swaps by 1."
pub open spec fn ipv6_swaps(address: Seq<nat>, piece_index: int, compress: int, swaps: int) -> Seq<nat>
    decreases swaps
{
    if piece_index != 0 && swaps > 0 {
        let other = compress + swaps - 1;
        let swapped = address.update(piece_index, address[other]).update(other, address[piece_index]);
        ipv6_swaps(swapped, piece_index - 1, compress, swaps - 1)
    } else {
        address
    }
}

/// "The IPv6 parser takes a scalar value string input and then runs these
/// steps. They return failure or an IPv6 address."
/// (<https://url.spec.whatwg.org/#concept-ipv6-parser>)
pub open spec fn ipv6_parser(input: Seq<u32>) -> Option<Seq<nat>> {
    // 1. "Let address be a new IPv6 address whose pieces are all 0."
    let address = seq![0nat, 0, 0, 0, 0, 0, 0, 0];
    // 2. "Let pieceIndex be 0."
    // 3. "Let compress be null."
    // 4. "Let pointer be a pointer for input."
    let looped = if c_at(input, 0) == Some(0x3Au32) {
        // 5. "If c is U+003A (:), then:"
        if c_at(input, 1) != Some(0x3Au32) {
            // 5.1 "If remaining does not start with U+003A (:),
            //     IPv6-invalid-compression validation error, return
            //     failure."
            None
        } else {
            // 5.2 "Increase pointer by 2."
            // 5.3 "Increase pieceIndex by 1 and then set compress to
            //     pieceIndex."
            // 6. "While c is not the EOF code point:"
            ipv6_main_loop(input, address, 1, Some(1), 2)
        }
    } else {
        // 6. "While c is not the EOF code point:"
        ipv6_main_loop(input, address, 0, None, 0)
    };
    match looped {
        None => None,
        Some((address, piece_index, compress)) => match compress {
            Some(compress) => {
                // 7. "If compress is non-null, then:"
                // 7.1 "Let swaps be pieceIndex − compress."
                let swaps = piece_index - compress;
                // 7.2 "Set pieceIndex to 7."
                // 7.3 "While pieceIndex is not 0 and swaps is greater than
                //     0, [...]"
                // 9. "Return address."
                Some(ipv6_swaps(address, 7, compress, swaps))
            },
            None => if piece_index != 8 {
                // 8. "Otherwise, if compress is null and pieceIndex is not
                //    8, IPv6-too-few-pieces validation error, return
                //    failure."
                None
            } else {
                // 9. "Return address."
                Some(address)
            },
        },
    }
}

// ---------------------------------------------------------------------
// §3.5: the opaque-host parser.
// ---------------------------------------------------------------------

/// "The opaque-host parser takes a scalar value string input, and then
/// runs these steps. They return failure or an opaque host."
/// (<https://url.spec.whatwg.org/#concept-opaque-host-parser>)
pub open spec fn opaque_host_parser(input: Seq<u32>) -> Option<Seq<u32>> {
    if contains_forbidden_host_code_point_from(input, 0) {
        // 1. "If input contains a forbidden host code point,
        //    host-invalid-code-point validation error, return failure."
        None
    } else {
        // 2. "If input contains a code point that is not a URL code point
        //    and not U+0025 (%), invalid-URL-unit validation error."
        //    (validation error only)
        // 3. "If input contains a U+0025 (%) and the two code points
        //    following it are not ASCII hex digits, invalid-URL-unit
        //    validation error." (validation error only)
        // 4. "Return the result of running UTF-8 percent-encode on input
        //    using the C0 control percent-encode set."
        Some(clazel_percent::spec::utf8_percent_encode(input, clazel_percent::spec::PercentEncodeSet::C0Control))
    }
}

// ---------------------------------------------------------------------
// §3.6 Host serializing.
// ---------------------------------------------------------------------

/// "The host serializer takes a host host and then runs these steps. They
/// return an ASCII string."
/// (<https://url.spec.whatwg.org/#concept-host-serializer>)
pub open spec fn host_serializer(host: Host) -> Seq<u32> {
    match host {
        // 1. "If host is an IPv4 address, return the result of running the
        //    IPv4 serializer on host."
        Host::Ipv4(address) => ipv4_serializer(address),
        // 2. "Otherwise, if host is an IPv6 address, return U+005B ([),
        //    followed by the result of running the IPv6 serializer on host,
        //    followed by U+005D (])."
        Host::Ipv6(address) => seq![0x5Bu32] + ipv6_serializer(address) + seq![0x5Du32],
        // 3. "Otherwise, host is a domain, opaque host, or empty host,
        //    return host."
        Host::Domain(s) => s,
        Host::Opaque(s) => s,
        Host::Empty => seq![],
    }
}

/// IPv4 serializer step 3, "For each i in the range 1 to 4, inclusive",
/// from `i`, with output and n so far.
pub open spec fn ipv4_serializer_loop(output: Seq<u32>, n: nat, i: nat) -> Seq<u32>
    decreases 5 - i
{
    if i > 4 {
        output
    } else {
        // 3.1 "Prepend n % 256, serialized, to output."
        let output = serialize_integer(n % 256) + output;
        // 3.2 "If i is not 4, then prepend U+002E (.) to output."
        let output = if i != 4 {
            seq![0x2Eu32] + output
        } else {
            output
        };
        // 3.3 "Set n to floor(n / 256)."
        ipv4_serializer_loop(output, n / 256, i + 1)
    }
}

/// "The IPv4 serializer takes an IPv4 address address and then runs these
/// steps. They return an ASCII string."
/// (<https://url.spec.whatwg.org/#concept-ipv4-serializer>)
pub open spec fn ipv4_serializer(address: nat) -> Seq<u32> {
    // 1. "Let output be the empty string."
    // 2. "Let n be the value of address."
    // 3. "For each i in the range 1 to 4, inclusive:"
    // 4. "Return output."
    ipv4_serializer_loop(seq![], address, 1)
}

/// IPv6 serializer step 4, "For each pieceIndex of address's pieces's
/// indices", from `piece_index`, with ignore0 and output so far.
pub open spec fn ipv6_serializer_loop(address: Seq<nat>, compress: Option<int>, ignore0: bool, piece_index: nat, output: Seq<u32>) -> Seq<u32>
    decreases address.len() - piece_index
{
    if piece_index >= address.len() {
        output
    } else if ignore0 && address[piece_index as int] == 0 {
        // 4.1 "If ignore0 is true and address[pieceIndex] is 0, then
        //     continue."
        ipv6_serializer_loop(address, compress, ignore0, piece_index + 1, output)
    } else {
        // 4.2 "Otherwise, if ignore0 is true, set ignore0 to false."
        if compress == Some(piece_index as int) {
            // 4.3 "If compress is pieceIndex, then:"
            // 4.3.1 "Let separator be "::" if pieceIndex is 0; otherwise
            //     U+003A (:)."
            let separator = if piece_index == 0 {
                seq![0x3Au32, 0x3A]
            } else {
                seq![0x3Au32]
            };
            // 4.3.2 "Append separator to output."
            // 4.3.3 "Set ignore0 to true and continue."
            ipv6_serializer_loop(address, compress, true, piece_index + 1, output + separator)
        } else {
            // 4.4 "Append address[pieceIndex], represented as the shortest
            //     possible lowercase hexadecimal number, to output."
            let output = output + shortest_lowercase_hex(address[piece_index as int]);
            // 4.5 "If pieceIndex is not 7, then append U+003A (:) to
            //     output."
            let output = if piece_index != 7 {
                output + seq![0x3Au32]
            } else {
                output
            };
            ipv6_serializer_loop(address, compress, false, piece_index + 1, output)
        }
    }
}

/// "The IPv6 serializer takes an IPv6 address address and then runs these
/// steps. They return an ASCII string."
/// (<https://url.spec.whatwg.org/#concept-ipv6-serializer>)
pub open spec fn ipv6_serializer(address: Seq<nat>) -> Seq<u32> {
    // 1. "Let output be the empty string."
    // 2. "Let compress be the result of finding the IPv6 address compressed
    //    piece index given address."
    let compress = find_ipv6_compressed_piece_index(address);
    // 3. "Let ignore0 be false."
    // 4. "For each pieceIndex of address's pieces's indices:"
    // 5. "Return output."
    ipv6_serializer_loop(address, compress, false, 0, seq![])
}

/// "Find the IPv6 address compressed piece index" step 5, "For each
/// pieceIndex of address's pieces's indices", from `piece_index`, with
/// longestIndex, longestSize, foundIndex and foundSize; then steps 6 and 7.
pub open spec fn find_compressed_loop(address: Seq<nat>, piece_index: nat, longest_index: Option<int>, longest_size: nat, found_index: Option<int>, found_size: nat) -> Option<int>
    decreases address.len() - piece_index
{
    if piece_index >= address.len() {
        if found_size > longest_size {
            // 6. "If foundSize is greater than longestSize, then return
            //    foundIndex."
            found_index
        } else {
            // 7. "Return longestIndex."
            longest_index
        }
    } else if address[piece_index as int] != 0 {
        // 5.1 "If address's pieces[pieceIndex] is not 0:"
        // 5.1.1 "If foundSize is greater than longestSize, then set
        //     longestIndex to foundIndex and longestSize to foundSize."
        let (longest_index, longest_size) = if found_size > longest_size {
            (found_index, found_size)
        } else {
            (longest_index, longest_size)
        };
        // 5.1.2 "Set foundIndex to null."
        // 5.1.3 "Set foundSize to 0."
        find_compressed_loop(address, piece_index + 1, longest_index, longest_size, None, 0)
    } else {
        // 5.2 "Otherwise:"
        // 5.2.1 "If foundIndex is null, then set foundIndex to pieceIndex."
        let found_index = if found_index is None {
            Some(piece_index as int)
        } else {
            found_index
        };
        // 5.2.2 "Increment foundSize by 1."
        find_compressed_loop(address, piece_index + 1, longest_index, longest_size, found_index, found_size + 1)
    }
}

/// "To find the IPv6 address compressed piece index given an IPv6 address
/// address" (<https://url.spec.whatwg.org/#find-the-ipv6-address-compressed-piece-index>)
pub open spec fn find_ipv6_compressed_piece_index(address: Seq<nat>) -> Option<int> {
    // 1. "Let longestIndex be null."
    // 2. "Let longestSize be 1."
    // 3. "Let foundIndex be null."
    // 4. "Let foundSize be 0."
    // 5. "For each pieceIndex of address's pieces's indices:"
    find_compressed_loop(address, 0, None, 1, None, 0)
}

} // verus!
