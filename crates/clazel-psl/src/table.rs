//! The spec view of the generated tables: [`psl_rules`] is the Public
//! Suffix List `cargo xtask tables` generated (`xtask/src/psl.rs` says how
//! `public_suffix_list.dat` becomes the tables), as the [`Rule`]s of
//! [`super::spec`].

use super::data::*;
use super::spec::Rule;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Label `k` of the list's labels, as a string.
pub open spec fn label_text(k: int) -> Seq<u32> {
    let row = psl_labels_at(k);
    Seq::new(row.len as nat, |c: int| psl_chars_at(row.start as int + c) as u32)
}

/// Rule `i` of the list.
pub open spec fn table_rule(i: int) -> Rule {
    let row = psl_rules_at(i);
    Rule {
        labels: Seq::new(row.count as nat, |j: int| label_text(row.first as int + j)),
        exception: row.exception,
    }
}

/// The Public Suffix List, rule by rule, in file order.
pub open spec fn psl_rules() -> Seq<Rule> {
    Seq::new(PSL_RULES_LEN as nat, |i: int| table_rule(i))
}

} // verus!
