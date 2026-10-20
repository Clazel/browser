//! The executable MIME type serializer, proven to meet [`super::contract`].
//! It mirrors "serialize a MIME type" (§4.5); the step comments live in
//! [`super::spec`].

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

use super::record::{MimeType, append, copy, solely_http_token_code_points_exec};

verus! {

/// Serialize a MIME type, step 2.4.1, appended to `out`.
fn precede_quotes_and_backslashes_exec(value: &[u32], out: &mut Vec<u32>)
    ensures
        final(out)@ == old(out)@ + precede_quotes_and_backslashes(value@),
{
    let ghost start = out@;
    let mut i: usize = 0;
    assert(value@.subrange(0, value.len() as int) =~= value@);
    while i < value.len()
        invariant
            i <= value.len(),
            start + precede_quotes_and_backslashes(value@) == out@ + precede_quotes_and_backslashes(value@.subrange(i as int, value.len() as int)),
        decreases value.len() - i,
    {
        let ghost rest = value@.subrange(i as int, value.len() as int);
        assert(rest.drop_first() =~= value@.subrange(i as int + 1, value.len() as int));
        if let Some(c) = value.get(i) {
            let c = *c;
            assert(rest[0] == c);
            if c == 0x22 || c == 0x5C {
                out.push(0x5C);
            }
            out.push(c);
        }
        // Never saturates: i < value.len().
        i = i.saturating_add(1);
        assert(out@ + precede_quotes_and_backslashes(value@.subrange(i as int, value.len() as int))
            =~= start + precede_quotes_and_backslashes(value@));
    }
    assert(value@.subrange(i as int, value.len() as int) =~= seq![]);
    assert(out@ + seq![] =~= out@);
}

/// Serialize a MIME type, step 2.4: append the value as serialized.
fn serialize_value_exec(value: &[u32], out: &mut Vec<u32>)
    ensures
        final(out)@ == old(out)@ + serialize_value(value@),
{
    if !solely_http_token_code_points_exec(value) || value.is_empty() {
        let ghost start = out@;
        out.push(0x22);
        precede_quotes_and_backslashes_exec(value, out);
        out.push(0x22);
        assert(out@ =~= start + (seq![0x22u32] + precede_quotes_and_backslashes(value@) + seq![0x22u32]));
    } else {
        append(out, value);
    }
}

/// Serialize a MIME type (MIME Sniffing §4.5).
pub fn serialize(mime_type: &MimeType) -> (output: Vec<u32>)
    ensures
        super::contract::serialize_ensures(mime_type@, output@),
{
    let ghost parameters = super::record::parameters_view(mime_type.parameters@);
    let mut out = copy(mime_type.type_.as_slice());
    out.push(0x2F);
    append(&mut out, mime_type.subtype.as_slice());
    assert(out@ =~= mime_type@.type_ + seq![0x2Fu32] + mime_type@.subtype);
    let ghost target = serialize_a_mime_type(mime_type@);
    let mut i: usize = 0;
    while i < mime_type.parameters.len()
        invariant
            i <= mime_type.parameters.len(),
            parameters == super::record::parameters_view(mime_type.parameters@),
            parameters == mime_type@.parameters,
            target == serialize_a_mime_type(mime_type@),
            serialize_parameters(parameters, i as nat, out@) == target,
        decreases mime_type.parameters.len() - i,
    {
        if let Some(entry) = mime_type.parameters.get(i) {
            assert(parameters[i as int] == (entry.0@, entry.1@));
            let ghost before = out@;
            out.push(0x3B);
            append(&mut out, entry.0.as_slice());
            out.push(0x3D);
            serialize_value_exec(entry.1.as_slice(), &mut out);
            assert(out@ =~= before + seq![0x3Bu32] + entry.0@ + seq![0x3Du32] + serialize_value(entry.1@));
        }
        // Never saturates: i < mime_type.parameters.len().
        i = i.saturating_add(1);
    }
    out
}

/// Serialize a MIME type to bytes (MIME Sniffing §4.5).
pub fn serialize_to_bytes(mime_type: &MimeType) -> (output: Vec<u8>)
    requires
        super::contract::serialize_to_bytes_requires(mime_type@),
    ensures
        super::contract::serialize_to_bytes_ensures(mime_type@, output@),
{
    let string = serialize(mime_type);
    let mut out: Vec<u8> = Vec::new();
    let mut i: usize = 0;
    while i < string.len()
        invariant
            i <= string.len(),
            out@ == isomorphic_encode(string@).subrange(0, i as int),
        decreases string.len() - i,
    {
        if let Some(c) = string.get(i) {
            // Isomorphic encode's assertion holds: *c <= 0xFF (the precondition).
            out.push(*c as u8);
        }
        assert(out@ =~= isomorphic_encode(string@).subrange(0, i as int + 1));
        // Never saturates: i < string.len().
        i = i.saturating_add(1);
    }
    assert(out@ =~= isomorphic_encode(string@));
    out
}

} // verus!
