//! Contracts the executable field functions must be proven to meet. Each
//! exec function's `ensures` clause is exactly one of these predicates
//! (applied to the views of its arguments and result), and its `requires`
//! clause is the matching `*_requires` predicate where there is one, so
//! reviewing these and [`super::spec`] is enough to know what the
//! implementation guarantees.
//!
//! Strings are `&[u8]` and `Vec<u8>`, viewed as `Seq<u8>`. Positions are
//! `usize`, viewed as `nat`; `None` is failure.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Why `Content-Length` was not accepted.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ContentLengthError {
    /// The value does not match §8.6 (and is not a repeat of one value).
    Invalid,
    /// The value matches §8.6 but is greater than `u64::MAX`.
    TooLarge,
}

/// Contract for `is_token(&[u8]) -> bool` (§5.6.2).
pub open spec fn is_token_ensures(s: Seq<u8>, output: bool) -> bool {
    output == is_token(s)
}

/// Contract for `is_field_name(&[u8]) -> bool` (§5.1).
pub open spec fn is_field_name_ensures(s: Seq<u8>, output: bool) -> bool {
    output == is_field_name(s)
}

/// Contract for `field_name_eq(&[u8], &[u8]) -> bool` (§5.1).
pub open spec fn field_name_eq_ensures(a: Seq<u8>, b: Seq<u8>, output: bool) -> bool {
    output == field_name_eq(a, b)
}

/// Contract for `strip_ows(&[u8]) -> Vec<u8>` (§5.5, §5.6.3).
pub open spec fn strip_ows_ensures(s: Seq<u8>, output: Seq<u8>) -> bool {
    output == strip_ows(s)
}

/// Contract for `is_field_value(&[u8]) -> bool` (§5.5).
pub open spec fn is_field_value_ensures(s: Seq<u8>, output: bool) -> bool {
    output == is_field_value(s)
}

/// Contract for `is_ows(&[u8]) -> bool` (§5.6.3).
pub open spec fn is_ows_ensures(s: Seq<u8>, output: bool) -> bool {
    output == is_ows(s)
}

/// Contract for `is_rws(&[u8]) -> bool` (§5.6.3).
pub open spec fn is_rws_ensures(s: Seq<u8>, output: bool) -> bool {
    output == is_rws(s)
}

/// Contract for `is_bws(&[u8]) -> bool` (§5.6.3).
pub open spec fn is_bws_ensures(s: Seq<u8>, output: bool) -> bool {
    output == is_bws(s)
}

/// Contract for `field_values_named(&[FieldLine], &[u8]) -> Vec<Vec<u8>>`
/// (§5.2, §5.3).
pub open spec fn field_values_named_ensures(section: Seq<FieldLine>, name: Seq<u8>, output: Seq<Seq<u8>>) -> bool {
    output == field_values_named(section, name)
}

/// Contract for `combine(&[Vec<u8>]) -> Vec<u8>` (§5.3).
pub open spec fn combine_ensures(values: Seq<Seq<u8>>, output: Seq<u8>) -> bool {
    output == combine(values)
}

/// Contract for `combined_field_value(&[FieldLine], &[u8]) -> Option<Vec<u8>>`
/// (§5.2, §5.3).
pub open spec fn combined_field_value_ensures(section: Seq<FieldLine>, name: Seq<u8>, output: Option<Seq<u8>>) -> bool {
    output == combined_field_value(section, name)
}

/// Contract for `set_cookie_lines(&[FieldLine]) -> Vec<Vec<u8>>` (§5.3).
pub open spec fn set_cookie_lines_ensures(section: Seq<FieldLine>, output: Seq<Seq<u8>>) -> bool {
    output == set_cookie_lines(section)
}

/// Contract for `split_values(&[u8]) -> Vec<Vec<u8>>` (§5.6.1).
pub open spec fn split_values_ensures(input: Seq<u8>, output: Seq<Seq<u8>>) -> bool {
    output == split_values(input)
}

/// Contract for `list_elements(&[u8]) -> Vec<Vec<u8>>` (§5.6.1.2).
pub open spec fn list_elements_ensures(input: Seq<u8>, output: Seq<Seq<u8>>) -> bool {
    output == list_elements(input)
}

/// Contract for `parse_quoted_string(&[u8]) -> Option<(Vec<u8>, usize)>`
/// (§5.6.4): the value, and the position where the string ends (what
/// follows it is `input.skip(position)`).
pub open spec fn parse_quoted_string_ensures(input: Seq<u8>, output: Option<(Seq<u8>, nat)>) -> bool {
    match output {
        Some((value, position)) => position <= input.len()
            && parse_quoted_string(input) == Some((value, input.skip(position as int))),
        None => parse_quoted_string(input) is None,
    }
}

/// Precondition of `quote(&[u8]) -> Vec<u8>`: every octet can be sent in a
/// quoted string.
pub open spec fn quote_requires(v: Seq<u8>) -> bool {
    is_quotable(v)
}

/// Contract for `quote(&[u8]) -> Vec<u8>` (§5.6.4).
pub open spec fn quote_ensures(v: Seq<u8>, output: Seq<u8>) -> bool {
    output == quote(v)
}

/// Contract for `parse_parameters(&[u8], ParameterGrammar) ->
/// Option<Vec<Parameter>>` (§5.6.6, §10.1.4).
pub open spec fn parse_parameters_ensures(input: Seq<u8>, grammar: ParameterGrammar, output: Option<Seq<Parameter>>) -> bool {
    output == parse_parameters(input, grammar)
}

/// Contract for `parse_transfer_encoding(&[u8]) -> Option<Vec<TransferCoding>>`
/// (RFC 9112 §6.1, §10.1.4).
pub open spec fn parse_transfer_encoding_ensures(value: Seq<u8>, output: Option<Seq<TransferCoding>>) -> bool {
    output == parse_transfer_encoding(value)
}

/// Contract for `parse_connection(&[u8]) -> Option<Vec<Vec<u8>>>` (§7.6.1).
pub open spec fn parse_connection_ensures(value: Seq<u8>, output: Option<Seq<Seq<u8>>>) -> bool {
    output == parse_connection(value)
}

/// Contract for `parse_content_length(&[u8]) -> Result<u64,
/// ContentLengthError>` (§8.6): a value that fits in a `u64` is returned
/// as is, a value that does not is `TooLarge`, and anything that is not
/// a `Content-Length` is `Invalid`.
pub open spec fn parse_content_length_ensures(value: Seq<u8>, output: Result<u64, ContentLengthError>) -> bool {
    match output {
        Ok(n) => parse_content_length(value) == Some(n as nat),
        Err(ContentLengthError::TooLarge) => parse_content_length(value) is Some
            && parse_content_length(value)->Some_0 > u64::MAX,
        Err(ContentLengthError::Invalid) => parse_content_length(value) is None,
    }
}

/// Contract for `parse_content_length_lines(&[Vec<u8>]) -> Result<u64,
/// ContentLengthError>`: as [`parse_content_length_ensures`], for the
/// field line values of every `Content-Length` line.
pub open spec fn parse_content_length_lines_ensures(lines: Seq<Seq<u8>>, output: Result<u64, ContentLengthError>) -> bool {
    match output {
        Ok(n) => parse_content_length_lines(lines) == Some(n as nat),
        Err(ContentLengthError::TooLarge) => parse_content_length_lines(lines) is Some
            && parse_content_length_lines(lines)->Some_0 > u64::MAX,
        Err(ContentLengthError::Invalid) => parse_content_length_lines(lines) is None,
    }
}

} // verus!
