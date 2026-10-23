//! Termination of the recursive loops in [`super::spec`]. Verus needs these
//! facts to accept the spec's `decreases` clause (it names a `via`
//! function in `spec.rs`, which only calls these); they say nothing else
//! about the spec.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// A run is never longer than the string.
pub proof fn lemma_run_len_le(class: Class, s: Seq<u8>)
    ensures
        run_len(class, s) <= s.len(),
    decreases s.len()
{
    if s.len() > 0 && in_class(class, s[0]) {
        lemma_run_len_le(class, s.drop_first());
    }
}

/// What follows a quoted string is shorter than its input.
pub proof fn lemma_quoted_body_rest(input: Seq<u8>, value: Seq<u8>)
    ensures
        match quoted_body(input, value) {
            Some((_, rest)) => rest.len() < input.len(),
            None => true,
        },
    decreases input.len()
{
    if input.len() > 0 && input[0] != 0x22 {
        if input[0] == 0x5C {
            if input.len() >= 2 && is_quoted_pair_octet(input[1]) {
                lemma_quoted_body_rest(input.drop_first().drop_first(), value.push(input[1]));
            }
        } else if is_qdtext(input[0]) {
            lemma_quoted_body_rest(input.drop_first(), value.push(input[0]));
        }
    }
}

/// A parameter consumes at least its name: what follows it is shorter than
/// its input.
pub proof fn lemma_parse_parameter_rest(input: Seq<u8>, grammar: ParameterGrammar)
    ensures
        match parse_parameter(input, grammar) {
            Some((_, rest)) => rest.len() < input.len(),
            None => true,
        },
{
    let n = run_len(Class::Tchar, input);
    lemma_run_len_le(Class::Tchar, input);
    if n > 0 {
        let after_name = input.skip(n as int);
        lemma_run_len_le(Class::Ows, after_name);
        let before_equals = match grammar {
            ParameterGrammar::Parameters => after_name,
            ParameterGrammar::TransferCoding => strip_leading_ows(after_name),
        };
        if before_equals.len() > 0 && before_equals[0] == 0x3D {
            lemma_run_len_le(Class::Ows, before_equals.drop_first());
            let after_equals = match grammar {
                ParameterGrammar::Parameters => before_equals.drop_first(),
                ParameterGrammar::TransferCoding => strip_leading_ows(before_equals.drop_first()),
            };
            lemma_parameter_value_rest(after_equals);
        }
    }
}

/// What follows a parameter value is no longer than its input.
pub proof fn lemma_parameter_value_rest(input: Seq<u8>)
    ensures
        match parse_parameter_value(input) {
            Some((_, rest)) => rest.len() <= input.len(),
            None => true,
        },
{
    if input.len() > 0 && input[0] == 0x22 {
        lemma_quoted_body_rest(input.drop_first(), seq![]);
    } else {
        lemma_run_len_le(Class::Tchar, input);
    }
}

} // verus!
