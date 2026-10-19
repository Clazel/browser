//! The executable MIME type parser, proven to meet [`super::contract`].
//!
//! The code mirrors the spec: [`collect_code_points`] is Infra's "collect a
//! sequence of code points", [`collect_quoted_string`] is Fetch's "collect
//! an HTTP quoted string" (with extract-value true), and [`parse`] is
//! "parse a MIME type" with its step 11 loop. Each is proven equal to its
//! spec function, so the step comments live in [`super::spec`].

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

use super::record::{
    MimeType, append, ascii_lowercase_exec, at, remove_leading_and_trailing_http_whitespace_exec,
    remove_trailing_http_whitespace_exec, slice_eq,
    solely_http_quoted_string_token_code_points_exec, solely_http_token_code_points_exec,
};

verus! {

/// Does `c` meet `condition`?
fn meets_exec(condition: &Condition, c: u32) -> (r: bool)
    ensures
        r == meets(*condition, c),
{
    match condition {
        Condition::NotSolidus => c != 0x2F,
        Condition::NotSemicolon => c != 0x3B,
        Condition::NotSemicolonOrEqualsSign => c != 0x3B && c != 0x3D,
        Condition::HttpWhitespace => c == 0x0A || c == 0x0D || c == 0x09 || c == 0x20,
        Condition::NotQuotationMarkOrReverseSolidus => c != 0x22 && c != 0x5C,
    }
}

/// Collect a sequence of code points meeting `condition` from `input`,
/// given `position`. Returns (result, position).
fn collect_code_points(condition: &Condition, input: &[u32], position: usize) -> (r: (Vec<u32>, usize))
    requires
        position <= input.len(),
    ensures
        (r.0@, r.1 as nat) == collect(*condition, input@, position as nat),
        position <= r.1 <= input.len(),
{
    proof {
        super::termination::lemma_collect_loop_position(*condition, input@, position as nat, seq![]);
    }
    let ghost target = collect(*condition, input@, position as nat);
    let mut result: Vec<u32> = Vec::new();
    let mut pos = position;
    loop
        invariant
            position <= pos <= input.len(),
            target == collect(*condition, input@, position as nat),
            collect_loop(*condition, input@, pos as nat, result@) == target,
        decreases input.len() - pos,
    {
        match at(input, pos) {
            Some(c) => {
                if !meets_exec(condition, c) {
                    return (result, pos);
                }
                result.push(c);
                // Never saturates: pos < input.len().
                pos = pos.saturating_add(1);
            },
            None => return (result, pos),
        }
    }
}

/// Collect an HTTP quoted string from `input`, given `position` and
/// extract-value true. Returns (value, position).
fn collect_quoted_string(input: &[u32], position: usize) -> (r: (Vec<u32>, usize))
    requires
        position < input.len(),
    ensures
        (r.0@, r.1 as nat) == collect_an_http_quoted_string(input@, position as nat, true),
        position < r.1 <= input.len(),
{
    let ghost target = quoted_string_loop(input@, position as nat + 1, seq![]);
    let mut value: Vec<u32> = Vec::new();
    // Never saturates: position < input.len().
    let mut pos = position.saturating_add(1);
    loop
        invariant
            position < pos <= input.len(),
            target == collect_an_http_quoted_string(input@, position as nat, true),
            quoted_string_loop(input@, pos as nat, value@) == target,
        decreases input.len() - pos,
    {
        let (collected, p) = collect_code_points(&Condition::NotQuotationMarkOrReverseSolidus, input, pos);
        append(&mut value, collected.as_slice());
        pos = p;
        match at(input, pos) {
            None => return (value, pos),
            Some(quote_or_backslash) => {
                // Never saturates: pos < input.len().
                pos = pos.saturating_add(1);
                if quote_or_backslash == 0x5C {
                    match at(input, pos) {
                        None => {
                            value.push(0x5C);
                            return (value, pos);
                        },
                        Some(c) => {
                            value.push(c);
                            // Never saturates: pos < input.len().
                            pos = pos.saturating_add(1);
                        },
                    }
                } else {
                    return (value, pos);
                }
            },
        }
    }
}

/// Does `parameters` have an entry named `name`?
fn map_exists_exec(parameters: &[(Vec<u32>, Vec<u32>)], name: &[u32]) -> (r: bool)
    ensures
        r == map_exists(super::record::parameters_view(parameters@), name@),
{
    let ghost map = super::record::parameters_view(parameters@);
    proof {
        super::lemmas::lemma_map_exists(map, name@);
    }
    let mut i: usize = 0;
    while i < parameters.len()
        invariant
            i <= parameters.len(),
            map == super::record::parameters_view(parameters@),
            map_exists(map, name@) <==> exists|j: int| 0 <= j < map.len() && (#[trigger] map[j]).0 == name@,
            forall|j: int| 0 <= j < i ==> (#[trigger] map[j]).0 != name@,
        decreases parameters.len() - i,
    {
        if let Some(entry) = parameters.get(i) {
            assert(map[i as int].0 == entry.0@);
            if slice_eq(entry.0.as_slice(), name) {
                return true;
            }
        }
        // Never saturates: i < parameters.len().
        i = i.saturating_add(1);
    }
    false
}

/// Parse a MIME type, step 11.10.
fn set_parameter_if_valid_exec(mime_type: &mut MimeType, parameter_name: Vec<u32>, parameter_value: Vec<u32>)
    ensures
        final(mime_type)@ == set_parameter_if_valid(old(mime_type)@, parameter_name@, parameter_value@),
{
    if !parameter_name.is_empty() && solely_http_token_code_points_exec(parameter_name.as_slice())
        && solely_http_quoted_string_token_code_points_exec(parameter_value.as_slice())
        && !map_exists_exec(mime_type.parameters.as_slice(), parameter_name.as_slice())
    {
        let ghost before = mime_type@;
        proof {
            super::lemmas::lemma_map_set_new(before.parameters, parameter_name@, parameter_value@);
        }
        mime_type.parameters.push((parameter_name, parameter_value));
        assert(mime_type@.parameters =~= before.parameters.push((parameter_name@, parameter_value@)));
    }
}

/// Parse a MIME type, step 11's loop, from `position`, adding to `mime_type`.
fn parse_parameters_exec(input: &[u32], position: usize, mime_type: &mut MimeType)
    requires
        position <= input.len(),
    ensures
        final(mime_type)@ == parse_parameters(input@, position as nat, old(mime_type)@),
{
    let ghost target = parse_parameters(input@, position as nat, mime_type@);
    let mut pos = position;
    loop
        invariant
            pos <= input.len(),
            target == parse_parameters(input@, position as nat, old(mime_type)@),
            parse_parameters(input@, pos as nat, mime_type@) == target,
        decreases input.len() - pos,
    {
        if pos >= input.len() {
            return;
        }
        // Never saturates: pos < input.len().
        pos = pos.saturating_add(1);
        let (_, p) = collect_code_points(&Condition::HttpWhitespace, input, pos);
        let (parameter_name, p) = collect_code_points(&Condition::NotSemicolonOrEqualsSign, input, p);
        pos = p;
        let parameter_name = ascii_lowercase_exec(parameter_name.as_slice());
        if at(input, pos) == Some(0x3Bu32) {
            continue;
        }
        if pos < input.len() {
            // Never saturates: pos < input.len().
            pos = pos.saturating_add(1);
        }
        match at(input, pos) {
            None => return,
            Some(c) => {
                if c == 0x22 {
                    let (parameter_value, p) = collect_quoted_string(input, pos);
                    let (_, p) = collect_code_points(&Condition::NotSemicolon, input, p);
                    pos = p;
                    set_parameter_if_valid_exec(mime_type, parameter_name, parameter_value);
                } else {
                    let (parameter_value, p) = collect_code_points(&Condition::NotSemicolon, input, pos);
                    pos = p;
                    let parameter_value = remove_trailing_http_whitespace_exec(parameter_value.as_slice());
                    if parameter_value.is_empty() {
                        continue;
                    }
                    set_parameter_if_valid_exec(mime_type, parameter_name, parameter_value);
                }
            },
        }
    }
}

/// Parse a MIME type (MIME Sniffing §4.4). `None` is failure.
pub fn parse(input: &[u32]) -> (output: Option<MimeType>)
    ensures
        super::contract::parse_ensures(input@, super::record::option_view(output)),
{
    let input = remove_leading_and_trailing_http_whitespace_exec(input);
    let input = input.as_slice();
    let (type_, position) = collect_code_points(&Condition::NotSolidus, input, 0);
    if type_.is_empty() || !solely_http_token_code_points_exec(type_.as_slice()) {
        return None;
    }
    if position >= input.len() {
        return None;
    }
    // Never saturates: position < input.len().
    let position = position.saturating_add(1);
    let (subtype, position) = collect_code_points(&Condition::NotSemicolon, input, position);
    let subtype = remove_trailing_http_whitespace_exec(subtype.as_slice());
    if subtype.is_empty() || !solely_http_token_code_points_exec(subtype.as_slice()) {
        return None;
    }
    let mut mime_type = MimeType {
        type_: ascii_lowercase_exec(type_.as_slice()),
        subtype: ascii_lowercase_exec(subtype.as_slice()),
        parameters: Vec::new(),
    };
    assert(mime_type@.parameters =~= seq![]);
    parse_parameters_exec(input, position, &mut mime_type);
    Some(mime_type)
}

/// Parse a MIME type from bytes (MIME Sniffing §4.4). `None` is failure.
pub fn parse_from_bytes(input: &[u8]) -> (output: Option<MimeType>)
    ensures
        super::contract::parse_from_bytes_ensures(input@, super::record::option_view(output)),
{
    let mut string: Vec<u32> = Vec::new();
    let mut i: usize = 0;
    while i < input.len()
        invariant
            i <= input.len(),
            string@ == isomorphic_decode(input@).subrange(0, i as int),
        decreases input.len() - i,
    {
        if let Some(b) = input.get(i) {
            string.push(*b as u32);
        }
        assert(string@ =~= isomorphic_decode(input@).subrange(0, i as int + 1));
        // Never saturates: i < input.len().
        i = i.saturating_add(1);
    }
    assert(string@ =~= isomorphic_decode(input@));
    parse(string.as_slice())
}

} // verus!

#[cfg(test)]
mod tests {
    use super::{parse, parse_from_bytes};
    use crate::mime_type::serialize::serialize;

    fn u(s: &str) -> Vec<u32> {
        s.chars().map(u32::from).collect()
    }

    fn round(s: &str) -> Option<String> {
        parse(&u(s)).map(|m| {
            serialize(&m)
                .into_iter()
                .filter_map(char::from_u32)
                .collect()
        })
    }

    #[test]
    fn standard_examples() {
        // §4.4, the example under step 11.8.2.
        assert_eq!(
            round("text/html;charset=\"shift_jis\"iso-2022-jp").as_deref(),
            Some("text/html;charset=shift_jis")
        );
        // §4.3: "text/html;" parses as "text/html" does.
        assert_eq!(round("text/html;").as_deref(), Some("text/html"));
        assert_eq!(
            round(" TEXT/Html ; A=\"b c\" ; a=d").as_deref(),
            Some("text/html;a=\"b c\"")
        );
        assert_eq!(round("text/"), None);
        assert_eq!(round("/html"), None);
        assert_eq!(round("text"), None);
        let from_bytes = parse_from_bytes(b"text/plain;x=\xFF");
        assert_eq!(
            from_bytes.map(|m| m.parameters),
            Some(vec![(u("x"), vec![0xFF])])
        );
    }
}
