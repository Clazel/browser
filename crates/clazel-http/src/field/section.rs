//! Executable field sections: the lines of one name, the combined field
//! value, and the `Set-Cookie` lines (§5.2, §5.3). Each function is proven
//! to meet [`super::contract`].

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

use super::string::{append, copy, field_name_eq};
use super::types::FieldLineBuf;

verus! {

/// The field line values of the lines of `section` named `name`, in
/// order (§5.2, §5.3).
pub fn field_values_named(section: &[FieldLineBuf], name: &[u8]) -> (out: Vec<Vec<u8>>)
    ensures
        super::contract::field_values_named_ensures(super::types::lines_view(section@), name@, super::types::strings_view(out@)),
{
    let ghost lines = super::types::lines_view(section@);
    assert(lines.skip(0) =~= lines);
    let mut out: Vec<Vec<u8>> = Vec::new();
    let mut i: usize = 0;
    while i < section.len()
        invariant
            i <= section.len(),
            lines == super::types::lines_view(section@),
            super::spec::field_values_named(lines, name@) == super::types::strings_view(out@) + super::spec::field_values_named(lines.skip(i as int), name@),
        decreases section.len() - i,
    {
        if let Some(line) = section.get(i) {
            assert(lines.skip(i as int)[0] == section@[i as int]@);
            assert(lines.skip(i as int).drop_first() =~= lines.skip(i as int + 1));
            let same = field_name_eq(line.name.as_slice(), name);
            if same {
                let ghost before = super::types::strings_view(out@);
                out.push(copy(line.value.as_slice()));
                assert(super::types::strings_view(out@) =~= before.push(line.value@));
                assert(before + super::spec::field_values_named(lines.skip(i as int), name@)
                    =~= super::types::strings_view(out@) + super::spec::field_values_named(lines.skip(i as int + 1), name@));
            } else {
                assert(super::types::strings_view(out@) + super::spec::field_values_named(lines.skip(i as int), name@)
                    =~= super::types::strings_view(out@) + super::spec::field_values_named(lines.skip(i as int + 1), name@));
            }
        }
        // Never saturates: i < section.len().
        i = i.saturating_add(1);
    }
    assert(lines.skip(section.len() as int).len() == 0);
    assert(super::types::strings_view(out@) + super::spec::field_values_named(lines.skip(section.len() as int), name@) =~= super::types::strings_view(out@));
    out
}

/// The values joined with ", " (§5.3).
pub fn combine(values: &[Vec<u8>]) -> (out: Vec<u8>)
    ensures
        super::contract::combine_ensures(super::types::strings_view(values@), out@),
{
    let ghost view = super::types::strings_view(values@);
    let mut out: Vec<u8> = Vec::new();
    assert(view.take(0) =~= Seq::<Seq<u8>>::empty());
    let mut i: usize = 0;
    while i < values.len()
        invariant
            i <= values.len(),
            view == super::types::strings_view(values@),
            out@ == super::spec::combine(view.take(i as int)),
        decreases values.len() - i,
    {
        if let Some(value) = values.get(i) {
            proof {
                super::lemmas::lemma_combine_push(view.take(i as int), value@);
            }
            assert(view.take(i as int + 1) =~= view.take(i as int).push(value@));
            if i > 0 {
                out.push(0x2C);
                out.push(0x20);
            }
            append(&mut out, value.as_slice());
            if i > 0 {
                assert(out@ =~= super::spec::combine(view.take(i as int)) + seq![0x2Cu8, 0x20u8] + value@);
            }
        }
        // Never saturates: i < values.len().
        i = i.saturating_add(1);
    }
    assert(view.take(values.len() as int) =~= view);
    out
}

/// Is `name` `Set-Cookie` (§5.3's note)?
fn is_set_cookie_exec(name: &[u8]) -> (r: bool)
    ensures
        r == is_set_cookie(name@),
{
    field_name_eq(&[0x73, 0x65, 0x74, 0x2D, 0x63, 0x6F, 0x6F, 0x6B, 0x69, 0x65], name)
}

/// The combined field value of `name` in `section` (§5.2, §5.3): `None`
/// if there is no such line, and for `Set-Cookie`.
pub fn combined_field_value(section: &[FieldLineBuf], name: &[u8]) -> (out: Option<Vec<u8>>)
    ensures
        super::contract::combined_field_value_ensures(super::types::lines_view(section@), name@, match out {
            Some(v) => Some(v@),
            None => None,
        }),
{
    if is_set_cookie_exec(name) {
        return None;
    }
    let values = field_values_named(section, name);
    if values.is_empty() {
        return None;
    }
    Some(combine(values.as_slice()))
}

/// The `Set-Cookie` lines of `section`, each on its own (§5.3's note).
pub fn set_cookie_lines(section: &[FieldLineBuf]) -> (out: Vec<Vec<u8>>)
    ensures
        super::contract::set_cookie_lines_ensures(super::types::lines_view(section@), super::types::strings_view(out@)),
{
    field_values_named(section, &[0x73, 0x65, 0x74, 0x2D, 0x63, 0x6F, 0x6F, 0x6B, 0x69, 0x65])
}

} // verus!
