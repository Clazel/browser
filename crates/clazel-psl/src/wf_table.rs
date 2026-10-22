//! The generated tables are well formed ([`super::wf::rules_wf`]), proven.
//!
//! `cargo xtask tables` also checks this when it generates the tables, but
//! no proof rests on that check: Verus is shown the table contents (the
//! `reveal`s below) and proves
//! - every rule has at least one label (`count >= 1`, for all 10396 rows);
//! - exactly eight rows are exception rules, at the listed indices (for all
//!   10396 rows, one chunk of the table at a time);
//! - those eight rules are, label by label, the texts listed in
//!   [`exc_list`] (checked against the characters table);
//! - [`exc_list`] meets the exception conditions of [`super::wf::rules_wf`] (two or
//!   more labels, none `*`, none a label suffix of another), which Verus
//!   evaluates (`compute_only`) on the eight concrete rules.
//!
//! Measured: the scan over the 10396 rows is done by the SMT solver on each
//! chunk of the rules table (evaluating them with `compute` exceeds Verus's
//! default limit for it). Reading characters is the other way round: the
//! SMT solver cannot take the revealed 16000-character chunk into a query
//! with the label texts (rlimit exceeded), so the characters are read by
//! `compute_only` in functions whose only conclusions are facts about
//! `super::data::psl_chars_at`, and the texts are assembled from those facts elsewhere.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {


/// The exception rules of the list, in file order, as texts (the rows listed
/// in [`is_exception_row`]).
pub open spec fn exc_list() -> Seq<Rule> {
    seq![
        Rule { labels: seq![seq![0x77u32, 0x77u32, 0x77u32], seq![0x63u32, 0x6Bu32]], exception: true }, // !www.ck (row 635)
        Rule { labels: seq![seq![0x63u32, 0x69u32, 0x74u32, 0x79u32], seq![0x6Bu32, 0x61u32, 0x77u32, 0x61u32, 0x73u32, 0x61u32, 0x6Bu32, 0x69u32], seq![0x6Au32, 0x70u32]], exception: true }, // !city.kawasaki.jp (row 1740)
        Rule { labels: seq![seq![0x63u32, 0x69u32, 0x74u32, 0x79u32], seq![0x6Bu32, 0x69u32, 0x74u32, 0x61u32, 0x6Bu32, 0x79u32, 0x75u32, 0x73u32, 0x68u32, 0x75u32], seq![0x6Au32, 0x70u32]], exception: true }, // !city.kitakyushu.jp (row 1742)
        Rule { labels: seq![seq![0x63u32, 0x69u32, 0x74u32, 0x79u32], seq![0x6Bu32, 0x6Fu32, 0x62u32, 0x65u32], seq![0x6Au32, 0x70u32]], exception: true }, // !city.kobe.jp (row 1744)
        Rule { labels: seq![seq![0x63u32, 0x69u32, 0x74u32, 0x79u32], seq![0x6Eu32, 0x61u32, 0x67u32, 0x6Fu32, 0x79u32, 0x61u32], seq![0x6Au32, 0x70u32]], exception: true }, // !city.nagoya.jp (row 1746)
        Rule { labels: seq![seq![0x63u32, 0x69u32, 0x74u32, 0x79u32], seq![0x73u32, 0x61u32, 0x70u32, 0x70u32, 0x6Fu32, 0x72u32, 0x6Fu32], seq![0x6Au32, 0x70u32]], exception: true }, // !city.sapporo.jp (row 1748)
        Rule { labels: seq![seq![0x63u32, 0x69u32, 0x74u32, 0x79u32], seq![0x73u32, 0x65u32, 0x6Eu32, 0x64u32, 0x61u32, 0x69u32], seq![0x6Au32, 0x70u32]], exception: true }, // !city.sendai.jp (row 1750)
        Rule { labels: seq![seq![0x63u32, 0x69u32, 0x74u32, 0x79u32], seq![0x79u32, 0x6Fu32, 0x6Bu32, 0x6Fu32, 0x68u32, 0x61u32, 0x6Du32, 0x61u32], seq![0x6Au32, 0x70u32]], exception: true }, // !city.yokohama.jp (row 1752)
    ]
}

/// The rows of the list that are exception rules.
pub open spec fn is_exception_row(i: int) -> bool {
    i == 635 || i == 1740 || i == 1742 || i == 1744 || i == 1746 || i == 1748 || i == 1750 || i == 1752
}

/// The row of the `k`-th exception rule.
pub open spec fn exc_row(k: int) -> int {
    seq![635int, 1740, 1742, 1744, 1746, 1748, 1750, 1752][k]
}

/// No label of the rule is `*`, from the `x`-th on.
pub open spec fn star_free_from(labels: Seq<Seq<u32>>, x: nat) -> bool
    decreases labels.len() - x,
{
    if x >= labels.len() {
        true
    } else {
        labels[x as int] != star_label() && star_free_from(labels, x + 1)
    }
}

/// The exception-rule conditions of [`super::wf::rules_wf`] on one rule.
pub open spec fn exception_rule_ok(a: Rule) -> bool {
    a.labels.len() >= 2 && star_free_from(a.labels, 0)
}

/// `a` is not a label suffix of `b`.
pub open spec fn not_suffix(a: Rule, b: Rule) -> bool {
    !(a.labels.len() <= b.labels.len() && a.labels == b.labels.skip((b.labels.len() - a.labels.len()) as int))
}

/// [`not_suffix`] of `l[i]` and `l[j]` for every `j` from the given one on
/// other than `i`.
pub open spec fn row_ok(l: Seq<Rule>, i: nat, j: nat) -> bool
    decreases l.len() - j,
{
    if j >= l.len() {
        true
    } else {
        (i == j || not_suffix(l[i as int], l[j as int])) && row_ok(l, i, j + 1)
    }
}

/// Every rule from the `i`-th on is ok, and not a suffix of another.
pub open spec fn all_ok(l: Seq<Rule>, i: nat) -> bool
    decreases l.len() - i,
{
    if i >= l.len() {
        true
    } else {
        exception_rule_ok(l[i as int]) && row_ok(l, i, 0) && all_ok(l, i + 1)
    }
}

/// The eight exception rules meet the conditions: Verus evaluates it.
proof fn lemma_exc_list_ok()
    ensures
        all_ok(exc_list(), 0),
{
    assert(all_ok(exc_list(), 0)) by (compute_only);
}

proof fn lemma_star_free(labels: Seq<Seq<u32>>, x: nat)
    requires
        star_free_from(labels, x),
    ensures
        forall|y: int| x <= y < labels.len() ==> (#[trigger] labels[y]) != star_label(),
    decreases labels.len() - x,
{
    if x < labels.len() {
        lemma_star_free(labels, x + 1);
    }
}

proof fn lemma_row_ok(l: Seq<Rule>, i: nat, j: nat)
    requires
        row_ok(l, i, j),
    ensures
        forall|y: int| j <= y < l.len() && y != i ==> not_suffix(l[i as int], #[trigger] l[y]),
    decreases l.len() - j,
{
    if j < l.len() {
        lemma_row_ok(l, i, j + 1);
    }
}

proof fn lemma_all_ok(l: Seq<Rule>, i: nat)
    requires
        all_ok(l, i),
    ensures
        forall|x: int| i <= x < l.len() ==> exception_rule_ok(#[trigger] l[x]),
        forall|x: int, y: int| i <= x < l.len() && 0 <= y < l.len() && x != y ==> not_suffix(#[trigger] l[x], #[trigger] l[y]),
    decreases l.len() - i,
{
    if i < l.len() {
        lemma_all_ok(l, i + 1);
        lemma_row_ok(l, i, 0);
    }
}

/// A label row whose characters are the given ones has that text.
proof fn lemma_label_text(row: super::tables::LabelRow, text: Seq<u32>)
    requires
        row.len as int == text.len(),
        forall|c: int| 0 <= c < text.len() ==> super::data::psl_chars_at(row.start as int + c) as u32 == #[trigger] text[c],
    ensures
        super::table::label_row_text(row) =~= text,
{
}

proof fn fact_row_635()
    ensures
        super::data::psl_rules_at(635) == (super::tables::RuleRow { first: 1265, count: 2, exception: true }),
{
    reveal(super::data::PSL_RULES_0);
    assert(super::data::psl_rules_at(635) == (super::tables::RuleRow { first: 1265, count: 2, exception: true })) by (compute_only);
}

proof fn fact_label_1265()
    ensures
        super::data::psl_labels_at(1265) == (super::tables::LabelRow { start: 4085, len: 3 }),
        super::data::psl_chars_at(4085) == 0x77u8 && super::data::psl_chars_at(4086) == 0x77u8 && super::data::psl_chars_at(4087) == 0x77u8,
{
    reveal(super::data::PSL_LABELS_0);
    reveal(super::data::PSL_CHARS_0);
    assert(super::data::psl_labels_at(1265) == (super::tables::LabelRow { start: 4085, len: 3 })) by (compute_only);
    assert(super::data::psl_chars_at(4085) == 0x77u8 && super::data::psl_chars_at(4086) == 0x77u8 && super::data::psl_chars_at(4087) == 0x77u8) by (compute_only);
}


proof fn fact_label_1266()
    ensures
        super::data::psl_labels_at(1266) == (super::tables::LabelRow { start: 4088, len: 2 }),
        super::data::psl_chars_at(4088) == 0x63u8 && super::data::psl_chars_at(4089) == 0x6Bu8,
{
    reveal(super::data::PSL_LABELS_0);
    reveal(super::data::PSL_CHARS_0);
    assert(super::data::psl_labels_at(1266) == (super::tables::LabelRow { start: 4088, len: 2 })) by (compute_only);
    assert(super::data::psl_chars_at(4088) == 0x63u8 && super::data::psl_chars_at(4089) == 0x6Bu8) by (compute_only);
}

/// Row 635 of the list is `!www.ck`.
pub proof fn lemma_exception_rule_635()
    ensures
        super::table::table_rule(635) == exc_list()[0],
{
    fact_row_635();
    fact_label_1265();
    assert forall|c: int| 0 <= c < 3 implies super::data::psl_chars_at(4085 + c) as u32 == (seq![0x77u32, 0x77u32, 0x77u32])[c] by {
        assert(c == 0 || c == 1 || c == 2);
        if c == 0 {
            assert(super::data::psl_chars_at(4085) as u32 == seq![0x77u32, 0x77u32, 0x77u32][0]);
        }
        if c == 1 {
            assert(super::data::psl_chars_at(4086) as u32 == seq![0x77u32, 0x77u32, 0x77u32][1]);
        }
        if c == 2 {
            assert(super::data::psl_chars_at(4087) as u32 == seq![0x77u32, 0x77u32, 0x77u32][2]);
        }
    }
    lemma_label_text(super::data::psl_labels_at(1265), seq![0x77u32, 0x77u32, 0x77u32]);
    fact_label_1266();
    assert forall|c: int| 0 <= c < 2 implies super::data::psl_chars_at(4088 + c) as u32 == (seq![0x63u32, 0x6Bu32])[c] by {
        assert(c == 0 || c == 1);
        if c == 0 {
            assert(super::data::psl_chars_at(4088) as u32 == seq![0x63u32, 0x6Bu32][0]);
        }
        if c == 1 {
            assert(super::data::psl_chars_at(4089) as u32 == seq![0x63u32, 0x6Bu32][1]);
        }
    }
    lemma_label_text(super::data::psl_labels_at(1266), seq![0x63u32, 0x6Bu32]);
    assert(super::table::table_rule(635).labels =~= exc_list()[0].labels);
    assert(super::table::table_rule(635).exception == exc_list()[0].exception);
}

proof fn fact_row_1740()
    ensures
        super::data::psl_rules_at(1740) == (super::tables::RuleRow { first: 3404, count: 3, exception: true }),
{
    reveal(super::data::PSL_RULES_1);
    assert(super::data::psl_rules_at(1740) == (super::tables::RuleRow { first: 3404, count: 3, exception: true })) by (compute_only);
}

proof fn fact_label_3404()
    ensures
        super::data::psl_labels_at(3404) == (super::tables::LabelRow { start: 12372, len: 4 }),
        super::data::psl_chars_at(12372) == 0x63u8 && super::data::psl_chars_at(12373) == 0x69u8 && super::data::psl_chars_at(12374) == 0x74u8 && super::data::psl_chars_at(12375) == 0x79u8,
{
    reveal(super::data::PSL_LABELS_1);
    reveal(super::data::PSL_CHARS_0);
    assert(super::data::psl_labels_at(3404) == (super::tables::LabelRow { start: 12372, len: 4 })) by (compute_only);
    assert(super::data::psl_chars_at(12372) == 0x63u8 && super::data::psl_chars_at(12373) == 0x69u8 && super::data::psl_chars_at(12374) == 0x74u8 && super::data::psl_chars_at(12375) == 0x79u8) by (compute_only);
}


proof fn fact_label_3405()
    ensures
        super::data::psl_labels_at(3405) == (super::tables::LabelRow { start: 12376, len: 8 }),
        super::data::psl_chars_at(12376) == 0x6Bu8 && super::data::psl_chars_at(12377) == 0x61u8 && super::data::psl_chars_at(12378) == 0x77u8 && super::data::psl_chars_at(12379) == 0x61u8 && super::data::psl_chars_at(12380) == 0x73u8 && super::data::psl_chars_at(12381) == 0x61u8 && super::data::psl_chars_at(12382) == 0x6Bu8 && super::data::psl_chars_at(12383) == 0x69u8,
{
    reveal(super::data::PSL_LABELS_1);
    reveal(super::data::PSL_CHARS_0);
    assert(super::data::psl_labels_at(3405) == (super::tables::LabelRow { start: 12376, len: 8 })) by (compute_only);
    assert(super::data::psl_chars_at(12376) == 0x6Bu8 && super::data::psl_chars_at(12377) == 0x61u8 && super::data::psl_chars_at(12378) == 0x77u8 && super::data::psl_chars_at(12379) == 0x61u8 && super::data::psl_chars_at(12380) == 0x73u8 && super::data::psl_chars_at(12381) == 0x61u8 && super::data::psl_chars_at(12382) == 0x6Bu8 && super::data::psl_chars_at(12383) == 0x69u8) by (compute_only);
}


proof fn fact_label_3406()
    ensures
        super::data::psl_labels_at(3406) == (super::tables::LabelRow { start: 12384, len: 2 }),
        super::data::psl_chars_at(12384) == 0x6Au8 && super::data::psl_chars_at(12385) == 0x70u8,
{
    reveal(super::data::PSL_LABELS_1);
    reveal(super::data::PSL_CHARS_0);
    assert(super::data::psl_labels_at(3406) == (super::tables::LabelRow { start: 12384, len: 2 })) by (compute_only);
    assert(super::data::psl_chars_at(12384) == 0x6Au8 && super::data::psl_chars_at(12385) == 0x70u8) by (compute_only);
}

/// Row 1740 of the list is `!city.kawasaki.jp`.
pub proof fn lemma_exception_rule_1740()
    ensures
        super::table::table_rule(1740) == exc_list()[1],
{
    fact_row_1740();
    fact_label_3404();
    assert forall|c: int| 0 <= c < 4 implies super::data::psl_chars_at(12372 + c) as u32 == (seq![0x63u32, 0x69u32, 0x74u32, 0x79u32])[c] by {
        assert(c == 0 || c == 1 || c == 2 || c == 3);
        if c == 0 {
            assert(super::data::psl_chars_at(12372) as u32 == seq![0x63u32, 0x69u32, 0x74u32, 0x79u32][0]);
        }
        if c == 1 {
            assert(super::data::psl_chars_at(12373) as u32 == seq![0x63u32, 0x69u32, 0x74u32, 0x79u32][1]);
        }
        if c == 2 {
            assert(super::data::psl_chars_at(12374) as u32 == seq![0x63u32, 0x69u32, 0x74u32, 0x79u32][2]);
        }
        if c == 3 {
            assert(super::data::psl_chars_at(12375) as u32 == seq![0x63u32, 0x69u32, 0x74u32, 0x79u32][3]);
        }
    }
    lemma_label_text(super::data::psl_labels_at(3404), seq![0x63u32, 0x69u32, 0x74u32, 0x79u32]);
    fact_label_3405();
    assert forall|c: int| 0 <= c < 8 implies super::data::psl_chars_at(12376 + c) as u32 == (seq![0x6Bu32, 0x61u32, 0x77u32, 0x61u32, 0x73u32, 0x61u32, 0x6Bu32, 0x69u32])[c] by {
        assert(c == 0 || c == 1 || c == 2 || c == 3 || c == 4 || c == 5 || c == 6 || c == 7);
        if c == 0 {
            assert(super::data::psl_chars_at(12376) as u32 == seq![0x6Bu32, 0x61u32, 0x77u32, 0x61u32, 0x73u32, 0x61u32, 0x6Bu32, 0x69u32][0]);
        }
        if c == 1 {
            assert(super::data::psl_chars_at(12377) as u32 == seq![0x6Bu32, 0x61u32, 0x77u32, 0x61u32, 0x73u32, 0x61u32, 0x6Bu32, 0x69u32][1]);
        }
        if c == 2 {
            assert(super::data::psl_chars_at(12378) as u32 == seq![0x6Bu32, 0x61u32, 0x77u32, 0x61u32, 0x73u32, 0x61u32, 0x6Bu32, 0x69u32][2]);
        }
        if c == 3 {
            assert(super::data::psl_chars_at(12379) as u32 == seq![0x6Bu32, 0x61u32, 0x77u32, 0x61u32, 0x73u32, 0x61u32, 0x6Bu32, 0x69u32][3]);
        }
        if c == 4 {
            assert(super::data::psl_chars_at(12380) as u32 == seq![0x6Bu32, 0x61u32, 0x77u32, 0x61u32, 0x73u32, 0x61u32, 0x6Bu32, 0x69u32][4]);
        }
        if c == 5 {
            assert(super::data::psl_chars_at(12381) as u32 == seq![0x6Bu32, 0x61u32, 0x77u32, 0x61u32, 0x73u32, 0x61u32, 0x6Bu32, 0x69u32][5]);
        }
        if c == 6 {
            assert(super::data::psl_chars_at(12382) as u32 == seq![0x6Bu32, 0x61u32, 0x77u32, 0x61u32, 0x73u32, 0x61u32, 0x6Bu32, 0x69u32][6]);
        }
        if c == 7 {
            assert(super::data::psl_chars_at(12383) as u32 == seq![0x6Bu32, 0x61u32, 0x77u32, 0x61u32, 0x73u32, 0x61u32, 0x6Bu32, 0x69u32][7]);
        }
    }
    lemma_label_text(super::data::psl_labels_at(3405), seq![0x6Bu32, 0x61u32, 0x77u32, 0x61u32, 0x73u32, 0x61u32, 0x6Bu32, 0x69u32]);
    fact_label_3406();
    assert forall|c: int| 0 <= c < 2 implies super::data::psl_chars_at(12384 + c) as u32 == (seq![0x6Au32, 0x70u32])[c] by {
        assert(c == 0 || c == 1);
        if c == 0 {
            assert(super::data::psl_chars_at(12384) as u32 == seq![0x6Au32, 0x70u32][0]);
        }
        if c == 1 {
            assert(super::data::psl_chars_at(12385) as u32 == seq![0x6Au32, 0x70u32][1]);
        }
    }
    lemma_label_text(super::data::psl_labels_at(3406), seq![0x6Au32, 0x70u32]);
    assert(super::table::table_rule(1740).labels =~= exc_list()[1].labels);
    assert(super::table::table_rule(1740).exception == exc_list()[1].exception);
}

proof fn fact_row_1742()
    ensures
        super::data::psl_rules_at(1742) == (super::tables::RuleRow { first: 3410, count: 3, exception: true }),
{
    reveal(super::data::PSL_RULES_1);
    assert(super::data::psl_rules_at(1742) == (super::tables::RuleRow { first: 3410, count: 3, exception: true })) by (compute_only);
}

proof fn fact_label_3410()
    ensures
        super::data::psl_labels_at(3410) == (super::tables::LabelRow { start: 12399, len: 4 }),
        super::data::psl_chars_at(12399) == 0x63u8 && super::data::psl_chars_at(12400) == 0x69u8 && super::data::psl_chars_at(12401) == 0x74u8 && super::data::psl_chars_at(12402) == 0x79u8,
{
    reveal(super::data::PSL_LABELS_1);
    reveal(super::data::PSL_CHARS_0);
    assert(super::data::psl_labels_at(3410) == (super::tables::LabelRow { start: 12399, len: 4 })) by (compute_only);
    assert(super::data::psl_chars_at(12399) == 0x63u8 && super::data::psl_chars_at(12400) == 0x69u8 && super::data::psl_chars_at(12401) == 0x74u8 && super::data::psl_chars_at(12402) == 0x79u8) by (compute_only);
}


proof fn fact_label_3411()
    ensures
        super::data::psl_labels_at(3411) == (super::tables::LabelRow { start: 12403, len: 10 }),
        super::data::psl_chars_at(12403) == 0x6Bu8 && super::data::psl_chars_at(12404) == 0x69u8 && super::data::psl_chars_at(12405) == 0x74u8 && super::data::psl_chars_at(12406) == 0x61u8 && super::data::psl_chars_at(12407) == 0x6Bu8 && super::data::psl_chars_at(12408) == 0x79u8 && super::data::psl_chars_at(12409) == 0x75u8 && super::data::psl_chars_at(12410) == 0x73u8 && super::data::psl_chars_at(12411) == 0x68u8 && super::data::psl_chars_at(12412) == 0x75u8,
{
    reveal(super::data::PSL_LABELS_1);
    reveal(super::data::PSL_CHARS_0);
    assert(super::data::psl_labels_at(3411) == (super::tables::LabelRow { start: 12403, len: 10 })) by (compute_only);
    assert(super::data::psl_chars_at(12403) == 0x6Bu8 && super::data::psl_chars_at(12404) == 0x69u8 && super::data::psl_chars_at(12405) == 0x74u8 && super::data::psl_chars_at(12406) == 0x61u8 && super::data::psl_chars_at(12407) == 0x6Bu8 && super::data::psl_chars_at(12408) == 0x79u8 && super::data::psl_chars_at(12409) == 0x75u8 && super::data::psl_chars_at(12410) == 0x73u8 && super::data::psl_chars_at(12411) == 0x68u8 && super::data::psl_chars_at(12412) == 0x75u8) by (compute_only);
}


proof fn fact_label_3412()
    ensures
        super::data::psl_labels_at(3412) == (super::tables::LabelRow { start: 12413, len: 2 }),
        super::data::psl_chars_at(12413) == 0x6Au8 && super::data::psl_chars_at(12414) == 0x70u8,
{
    reveal(super::data::PSL_LABELS_1);
    reveal(super::data::PSL_CHARS_0);
    assert(super::data::psl_labels_at(3412) == (super::tables::LabelRow { start: 12413, len: 2 })) by (compute_only);
    assert(super::data::psl_chars_at(12413) == 0x6Au8 && super::data::psl_chars_at(12414) == 0x70u8) by (compute_only);
}

/// Row 1742 of the list is `!city.kitakyushu.jp`.
pub proof fn lemma_exception_rule_1742()
    ensures
        super::table::table_rule(1742) == exc_list()[2],
{
    fact_row_1742();
    fact_label_3410();
    assert forall|c: int| 0 <= c < 4 implies super::data::psl_chars_at(12399 + c) as u32 == (seq![0x63u32, 0x69u32, 0x74u32, 0x79u32])[c] by {
        assert(c == 0 || c == 1 || c == 2 || c == 3);
        if c == 0 {
            assert(super::data::psl_chars_at(12399) as u32 == seq![0x63u32, 0x69u32, 0x74u32, 0x79u32][0]);
        }
        if c == 1 {
            assert(super::data::psl_chars_at(12400) as u32 == seq![0x63u32, 0x69u32, 0x74u32, 0x79u32][1]);
        }
        if c == 2 {
            assert(super::data::psl_chars_at(12401) as u32 == seq![0x63u32, 0x69u32, 0x74u32, 0x79u32][2]);
        }
        if c == 3 {
            assert(super::data::psl_chars_at(12402) as u32 == seq![0x63u32, 0x69u32, 0x74u32, 0x79u32][3]);
        }
    }
    lemma_label_text(super::data::psl_labels_at(3410), seq![0x63u32, 0x69u32, 0x74u32, 0x79u32]);
    fact_label_3411();
    assert forall|c: int| 0 <= c < 10 implies super::data::psl_chars_at(12403 + c) as u32 == (seq![0x6Bu32, 0x69u32, 0x74u32, 0x61u32, 0x6Bu32, 0x79u32, 0x75u32, 0x73u32, 0x68u32, 0x75u32])[c] by {
        assert(c == 0 || c == 1 || c == 2 || c == 3 || c == 4 || c == 5 || c == 6 || c == 7 || c == 8 || c == 9);
        if c == 0 {
            assert(super::data::psl_chars_at(12403) as u32 == seq![0x6Bu32, 0x69u32, 0x74u32, 0x61u32, 0x6Bu32, 0x79u32, 0x75u32, 0x73u32, 0x68u32, 0x75u32][0]);
        }
        if c == 1 {
            assert(super::data::psl_chars_at(12404) as u32 == seq![0x6Bu32, 0x69u32, 0x74u32, 0x61u32, 0x6Bu32, 0x79u32, 0x75u32, 0x73u32, 0x68u32, 0x75u32][1]);
        }
        if c == 2 {
            assert(super::data::psl_chars_at(12405) as u32 == seq![0x6Bu32, 0x69u32, 0x74u32, 0x61u32, 0x6Bu32, 0x79u32, 0x75u32, 0x73u32, 0x68u32, 0x75u32][2]);
        }
        if c == 3 {
            assert(super::data::psl_chars_at(12406) as u32 == seq![0x6Bu32, 0x69u32, 0x74u32, 0x61u32, 0x6Bu32, 0x79u32, 0x75u32, 0x73u32, 0x68u32, 0x75u32][3]);
        }
        if c == 4 {
            assert(super::data::psl_chars_at(12407) as u32 == seq![0x6Bu32, 0x69u32, 0x74u32, 0x61u32, 0x6Bu32, 0x79u32, 0x75u32, 0x73u32, 0x68u32, 0x75u32][4]);
        }
        if c == 5 {
            assert(super::data::psl_chars_at(12408) as u32 == seq![0x6Bu32, 0x69u32, 0x74u32, 0x61u32, 0x6Bu32, 0x79u32, 0x75u32, 0x73u32, 0x68u32, 0x75u32][5]);
        }
        if c == 6 {
            assert(super::data::psl_chars_at(12409) as u32 == seq![0x6Bu32, 0x69u32, 0x74u32, 0x61u32, 0x6Bu32, 0x79u32, 0x75u32, 0x73u32, 0x68u32, 0x75u32][6]);
        }
        if c == 7 {
            assert(super::data::psl_chars_at(12410) as u32 == seq![0x6Bu32, 0x69u32, 0x74u32, 0x61u32, 0x6Bu32, 0x79u32, 0x75u32, 0x73u32, 0x68u32, 0x75u32][7]);
        }
        if c == 8 {
            assert(super::data::psl_chars_at(12411) as u32 == seq![0x6Bu32, 0x69u32, 0x74u32, 0x61u32, 0x6Bu32, 0x79u32, 0x75u32, 0x73u32, 0x68u32, 0x75u32][8]);
        }
        if c == 9 {
            assert(super::data::psl_chars_at(12412) as u32 == seq![0x6Bu32, 0x69u32, 0x74u32, 0x61u32, 0x6Bu32, 0x79u32, 0x75u32, 0x73u32, 0x68u32, 0x75u32][9]);
        }
    }
    lemma_label_text(super::data::psl_labels_at(3411), seq![0x6Bu32, 0x69u32, 0x74u32, 0x61u32, 0x6Bu32, 0x79u32, 0x75u32, 0x73u32, 0x68u32, 0x75u32]);
    fact_label_3412();
    assert forall|c: int| 0 <= c < 2 implies super::data::psl_chars_at(12413 + c) as u32 == (seq![0x6Au32, 0x70u32])[c] by {
        assert(c == 0 || c == 1);
        if c == 0 {
            assert(super::data::psl_chars_at(12413) as u32 == seq![0x6Au32, 0x70u32][0]);
        }
        if c == 1 {
            assert(super::data::psl_chars_at(12414) as u32 == seq![0x6Au32, 0x70u32][1]);
        }
    }
    lemma_label_text(super::data::psl_labels_at(3412), seq![0x6Au32, 0x70u32]);
    assert(super::table::table_rule(1742).labels =~= exc_list()[2].labels);
    assert(super::table::table_rule(1742).exception == exc_list()[2].exception);
}

proof fn fact_row_1744()
    ensures
        super::data::psl_rules_at(1744) == (super::tables::RuleRow { first: 3416, count: 3, exception: true }),
{
    reveal(super::data::PSL_RULES_1);
    assert(super::data::psl_rules_at(1744) == (super::tables::RuleRow { first: 3416, count: 3, exception: true })) by (compute_only);
}

proof fn fact_label_3416()
    ensures
        super::data::psl_labels_at(3416) == (super::tables::LabelRow { start: 12422, len: 4 }),
        super::data::psl_chars_at(12422) == 0x63u8 && super::data::psl_chars_at(12423) == 0x69u8 && super::data::psl_chars_at(12424) == 0x74u8 && super::data::psl_chars_at(12425) == 0x79u8,
{
    reveal(super::data::PSL_LABELS_1);
    reveal(super::data::PSL_CHARS_0);
    assert(super::data::psl_labels_at(3416) == (super::tables::LabelRow { start: 12422, len: 4 })) by (compute_only);
    assert(super::data::psl_chars_at(12422) == 0x63u8 && super::data::psl_chars_at(12423) == 0x69u8 && super::data::psl_chars_at(12424) == 0x74u8 && super::data::psl_chars_at(12425) == 0x79u8) by (compute_only);
}


proof fn fact_label_3417()
    ensures
        super::data::psl_labels_at(3417) == (super::tables::LabelRow { start: 12426, len: 4 }),
        super::data::psl_chars_at(12426) == 0x6Bu8 && super::data::psl_chars_at(12427) == 0x6Fu8 && super::data::psl_chars_at(12428) == 0x62u8 && super::data::psl_chars_at(12429) == 0x65u8,
{
    reveal(super::data::PSL_LABELS_1);
    reveal(super::data::PSL_CHARS_0);
    assert(super::data::psl_labels_at(3417) == (super::tables::LabelRow { start: 12426, len: 4 })) by (compute_only);
    assert(super::data::psl_chars_at(12426) == 0x6Bu8 && super::data::psl_chars_at(12427) == 0x6Fu8 && super::data::psl_chars_at(12428) == 0x62u8 && super::data::psl_chars_at(12429) == 0x65u8) by (compute_only);
}


proof fn fact_label_3418()
    ensures
        super::data::psl_labels_at(3418) == (super::tables::LabelRow { start: 12430, len: 2 }),
        super::data::psl_chars_at(12430) == 0x6Au8 && super::data::psl_chars_at(12431) == 0x70u8,
{
    reveal(super::data::PSL_LABELS_1);
    reveal(super::data::PSL_CHARS_0);
    assert(super::data::psl_labels_at(3418) == (super::tables::LabelRow { start: 12430, len: 2 })) by (compute_only);
    assert(super::data::psl_chars_at(12430) == 0x6Au8 && super::data::psl_chars_at(12431) == 0x70u8) by (compute_only);
}

/// Row 1744 of the list is `!city.kobe.jp`.
pub proof fn lemma_exception_rule_1744()
    ensures
        super::table::table_rule(1744) == exc_list()[3],
{
    fact_row_1744();
    fact_label_3416();
    assert forall|c: int| 0 <= c < 4 implies super::data::psl_chars_at(12422 + c) as u32 == (seq![0x63u32, 0x69u32, 0x74u32, 0x79u32])[c] by {
        assert(c == 0 || c == 1 || c == 2 || c == 3);
        if c == 0 {
            assert(super::data::psl_chars_at(12422) as u32 == seq![0x63u32, 0x69u32, 0x74u32, 0x79u32][0]);
        }
        if c == 1 {
            assert(super::data::psl_chars_at(12423) as u32 == seq![0x63u32, 0x69u32, 0x74u32, 0x79u32][1]);
        }
        if c == 2 {
            assert(super::data::psl_chars_at(12424) as u32 == seq![0x63u32, 0x69u32, 0x74u32, 0x79u32][2]);
        }
        if c == 3 {
            assert(super::data::psl_chars_at(12425) as u32 == seq![0x63u32, 0x69u32, 0x74u32, 0x79u32][3]);
        }
    }
    lemma_label_text(super::data::psl_labels_at(3416), seq![0x63u32, 0x69u32, 0x74u32, 0x79u32]);
    fact_label_3417();
    assert forall|c: int| 0 <= c < 4 implies super::data::psl_chars_at(12426 + c) as u32 == (seq![0x6Bu32, 0x6Fu32, 0x62u32, 0x65u32])[c] by {
        assert(c == 0 || c == 1 || c == 2 || c == 3);
        if c == 0 {
            assert(super::data::psl_chars_at(12426) as u32 == seq![0x6Bu32, 0x6Fu32, 0x62u32, 0x65u32][0]);
        }
        if c == 1 {
            assert(super::data::psl_chars_at(12427) as u32 == seq![0x6Bu32, 0x6Fu32, 0x62u32, 0x65u32][1]);
        }
        if c == 2 {
            assert(super::data::psl_chars_at(12428) as u32 == seq![0x6Bu32, 0x6Fu32, 0x62u32, 0x65u32][2]);
        }
        if c == 3 {
            assert(super::data::psl_chars_at(12429) as u32 == seq![0x6Bu32, 0x6Fu32, 0x62u32, 0x65u32][3]);
        }
    }
    lemma_label_text(super::data::psl_labels_at(3417), seq![0x6Bu32, 0x6Fu32, 0x62u32, 0x65u32]);
    fact_label_3418();
    assert forall|c: int| 0 <= c < 2 implies super::data::psl_chars_at(12430 + c) as u32 == (seq![0x6Au32, 0x70u32])[c] by {
        assert(c == 0 || c == 1);
        if c == 0 {
            assert(super::data::psl_chars_at(12430) as u32 == seq![0x6Au32, 0x70u32][0]);
        }
        if c == 1 {
            assert(super::data::psl_chars_at(12431) as u32 == seq![0x6Au32, 0x70u32][1]);
        }
    }
    lemma_label_text(super::data::psl_labels_at(3418), seq![0x6Au32, 0x70u32]);
    assert(super::table::table_rule(1744).labels =~= exc_list()[3].labels);
    assert(super::table::table_rule(1744).exception == exc_list()[3].exception);
}

proof fn fact_row_1746()
    ensures
        super::data::psl_rules_at(1746) == (super::tables::RuleRow { first: 3422, count: 3, exception: true }),
{
    reveal(super::data::PSL_RULES_1);
    assert(super::data::psl_rules_at(1746) == (super::tables::RuleRow { first: 3422, count: 3, exception: true })) by (compute_only);
}

proof fn fact_label_3422()
    ensures
        super::data::psl_labels_at(3422) == (super::tables::LabelRow { start: 12441, len: 4 }),
        super::data::psl_chars_at(12441) == 0x63u8 && super::data::psl_chars_at(12442) == 0x69u8 && super::data::psl_chars_at(12443) == 0x74u8 && super::data::psl_chars_at(12444) == 0x79u8,
{
    reveal(super::data::PSL_LABELS_1);
    reveal(super::data::PSL_CHARS_0);
    assert(super::data::psl_labels_at(3422) == (super::tables::LabelRow { start: 12441, len: 4 })) by (compute_only);
    assert(super::data::psl_chars_at(12441) == 0x63u8 && super::data::psl_chars_at(12442) == 0x69u8 && super::data::psl_chars_at(12443) == 0x74u8 && super::data::psl_chars_at(12444) == 0x79u8) by (compute_only);
}


proof fn fact_label_3423()
    ensures
        super::data::psl_labels_at(3423) == (super::tables::LabelRow { start: 12445, len: 6 }),
        super::data::psl_chars_at(12445) == 0x6Eu8 && super::data::psl_chars_at(12446) == 0x61u8 && super::data::psl_chars_at(12447) == 0x67u8 && super::data::psl_chars_at(12448) == 0x6Fu8 && super::data::psl_chars_at(12449) == 0x79u8 && super::data::psl_chars_at(12450) == 0x61u8,
{
    reveal(super::data::PSL_LABELS_1);
    reveal(super::data::PSL_CHARS_0);
    assert(super::data::psl_labels_at(3423) == (super::tables::LabelRow { start: 12445, len: 6 })) by (compute_only);
    assert(super::data::psl_chars_at(12445) == 0x6Eu8 && super::data::psl_chars_at(12446) == 0x61u8 && super::data::psl_chars_at(12447) == 0x67u8 && super::data::psl_chars_at(12448) == 0x6Fu8 && super::data::psl_chars_at(12449) == 0x79u8 && super::data::psl_chars_at(12450) == 0x61u8) by (compute_only);
}


proof fn fact_label_3424()
    ensures
        super::data::psl_labels_at(3424) == (super::tables::LabelRow { start: 12451, len: 2 }),
        super::data::psl_chars_at(12451) == 0x6Au8 && super::data::psl_chars_at(12452) == 0x70u8,
{
    reveal(super::data::PSL_LABELS_1);
    reveal(super::data::PSL_CHARS_0);
    assert(super::data::psl_labels_at(3424) == (super::tables::LabelRow { start: 12451, len: 2 })) by (compute_only);
    assert(super::data::psl_chars_at(12451) == 0x6Au8 && super::data::psl_chars_at(12452) == 0x70u8) by (compute_only);
}

/// Row 1746 of the list is `!city.nagoya.jp`.
pub proof fn lemma_exception_rule_1746()
    ensures
        super::table::table_rule(1746) == exc_list()[4],
{
    fact_row_1746();
    fact_label_3422();
    assert forall|c: int| 0 <= c < 4 implies super::data::psl_chars_at(12441 + c) as u32 == (seq![0x63u32, 0x69u32, 0x74u32, 0x79u32])[c] by {
        assert(c == 0 || c == 1 || c == 2 || c == 3);
        if c == 0 {
            assert(super::data::psl_chars_at(12441) as u32 == seq![0x63u32, 0x69u32, 0x74u32, 0x79u32][0]);
        }
        if c == 1 {
            assert(super::data::psl_chars_at(12442) as u32 == seq![0x63u32, 0x69u32, 0x74u32, 0x79u32][1]);
        }
        if c == 2 {
            assert(super::data::psl_chars_at(12443) as u32 == seq![0x63u32, 0x69u32, 0x74u32, 0x79u32][2]);
        }
        if c == 3 {
            assert(super::data::psl_chars_at(12444) as u32 == seq![0x63u32, 0x69u32, 0x74u32, 0x79u32][3]);
        }
    }
    lemma_label_text(super::data::psl_labels_at(3422), seq![0x63u32, 0x69u32, 0x74u32, 0x79u32]);
    fact_label_3423();
    assert forall|c: int| 0 <= c < 6 implies super::data::psl_chars_at(12445 + c) as u32 == (seq![0x6Eu32, 0x61u32, 0x67u32, 0x6Fu32, 0x79u32, 0x61u32])[c] by {
        assert(c == 0 || c == 1 || c == 2 || c == 3 || c == 4 || c == 5);
        if c == 0 {
            assert(super::data::psl_chars_at(12445) as u32 == seq![0x6Eu32, 0x61u32, 0x67u32, 0x6Fu32, 0x79u32, 0x61u32][0]);
        }
        if c == 1 {
            assert(super::data::psl_chars_at(12446) as u32 == seq![0x6Eu32, 0x61u32, 0x67u32, 0x6Fu32, 0x79u32, 0x61u32][1]);
        }
        if c == 2 {
            assert(super::data::psl_chars_at(12447) as u32 == seq![0x6Eu32, 0x61u32, 0x67u32, 0x6Fu32, 0x79u32, 0x61u32][2]);
        }
        if c == 3 {
            assert(super::data::psl_chars_at(12448) as u32 == seq![0x6Eu32, 0x61u32, 0x67u32, 0x6Fu32, 0x79u32, 0x61u32][3]);
        }
        if c == 4 {
            assert(super::data::psl_chars_at(12449) as u32 == seq![0x6Eu32, 0x61u32, 0x67u32, 0x6Fu32, 0x79u32, 0x61u32][4]);
        }
        if c == 5 {
            assert(super::data::psl_chars_at(12450) as u32 == seq![0x6Eu32, 0x61u32, 0x67u32, 0x6Fu32, 0x79u32, 0x61u32][5]);
        }
    }
    lemma_label_text(super::data::psl_labels_at(3423), seq![0x6Eu32, 0x61u32, 0x67u32, 0x6Fu32, 0x79u32, 0x61u32]);
    fact_label_3424();
    assert forall|c: int| 0 <= c < 2 implies super::data::psl_chars_at(12451 + c) as u32 == (seq![0x6Au32, 0x70u32])[c] by {
        assert(c == 0 || c == 1);
        if c == 0 {
            assert(super::data::psl_chars_at(12451) as u32 == seq![0x6Au32, 0x70u32][0]);
        }
        if c == 1 {
            assert(super::data::psl_chars_at(12452) as u32 == seq![0x6Au32, 0x70u32][1]);
        }
    }
    lemma_label_text(super::data::psl_labels_at(3424), seq![0x6Au32, 0x70u32]);
    assert(super::table::table_rule(1746).labels =~= exc_list()[4].labels);
    assert(super::table::table_rule(1746).exception == exc_list()[4].exception);
}

proof fn fact_row_1748()
    ensures
        super::data::psl_rules_at(1748) == (super::tables::RuleRow { first: 3428, count: 3, exception: true }),
{
    reveal(super::data::PSL_RULES_1);
    assert(super::data::psl_rules_at(1748) == (super::tables::RuleRow { first: 3428, count: 3, exception: true })) by (compute_only);
}

proof fn fact_label_3428()
    ensures
        super::data::psl_labels_at(3428) == (super::tables::LabelRow { start: 12463, len: 4 }),
        super::data::psl_chars_at(12463) == 0x63u8 && super::data::psl_chars_at(12464) == 0x69u8 && super::data::psl_chars_at(12465) == 0x74u8 && super::data::psl_chars_at(12466) == 0x79u8,
{
    reveal(super::data::PSL_LABELS_1);
    reveal(super::data::PSL_CHARS_0);
    assert(super::data::psl_labels_at(3428) == (super::tables::LabelRow { start: 12463, len: 4 })) by (compute_only);
    assert(super::data::psl_chars_at(12463) == 0x63u8 && super::data::psl_chars_at(12464) == 0x69u8 && super::data::psl_chars_at(12465) == 0x74u8 && super::data::psl_chars_at(12466) == 0x79u8) by (compute_only);
}


proof fn fact_label_3429()
    ensures
        super::data::psl_labels_at(3429) == (super::tables::LabelRow { start: 12467, len: 7 }),
        super::data::psl_chars_at(12467) == 0x73u8 && super::data::psl_chars_at(12468) == 0x61u8 && super::data::psl_chars_at(12469) == 0x70u8 && super::data::psl_chars_at(12470) == 0x70u8 && super::data::psl_chars_at(12471) == 0x6Fu8 && super::data::psl_chars_at(12472) == 0x72u8 && super::data::psl_chars_at(12473) == 0x6Fu8,
{
    reveal(super::data::PSL_LABELS_1);
    reveal(super::data::PSL_CHARS_0);
    assert(super::data::psl_labels_at(3429) == (super::tables::LabelRow { start: 12467, len: 7 })) by (compute_only);
    assert(super::data::psl_chars_at(12467) == 0x73u8 && super::data::psl_chars_at(12468) == 0x61u8 && super::data::psl_chars_at(12469) == 0x70u8 && super::data::psl_chars_at(12470) == 0x70u8 && super::data::psl_chars_at(12471) == 0x6Fu8 && super::data::psl_chars_at(12472) == 0x72u8 && super::data::psl_chars_at(12473) == 0x6Fu8) by (compute_only);
}


proof fn fact_label_3430()
    ensures
        super::data::psl_labels_at(3430) == (super::tables::LabelRow { start: 12474, len: 2 }),
        super::data::psl_chars_at(12474) == 0x6Au8 && super::data::psl_chars_at(12475) == 0x70u8,
{
    reveal(super::data::PSL_LABELS_1);
    reveal(super::data::PSL_CHARS_0);
    assert(super::data::psl_labels_at(3430) == (super::tables::LabelRow { start: 12474, len: 2 })) by (compute_only);
    assert(super::data::psl_chars_at(12474) == 0x6Au8 && super::data::psl_chars_at(12475) == 0x70u8) by (compute_only);
}

/// Row 1748 of the list is `!city.sapporo.jp`.
pub proof fn lemma_exception_rule_1748()
    ensures
        super::table::table_rule(1748) == exc_list()[5],
{
    fact_row_1748();
    fact_label_3428();
    assert forall|c: int| 0 <= c < 4 implies super::data::psl_chars_at(12463 + c) as u32 == (seq![0x63u32, 0x69u32, 0x74u32, 0x79u32])[c] by {
        assert(c == 0 || c == 1 || c == 2 || c == 3);
        if c == 0 {
            assert(super::data::psl_chars_at(12463) as u32 == seq![0x63u32, 0x69u32, 0x74u32, 0x79u32][0]);
        }
        if c == 1 {
            assert(super::data::psl_chars_at(12464) as u32 == seq![0x63u32, 0x69u32, 0x74u32, 0x79u32][1]);
        }
        if c == 2 {
            assert(super::data::psl_chars_at(12465) as u32 == seq![0x63u32, 0x69u32, 0x74u32, 0x79u32][2]);
        }
        if c == 3 {
            assert(super::data::psl_chars_at(12466) as u32 == seq![0x63u32, 0x69u32, 0x74u32, 0x79u32][3]);
        }
    }
    lemma_label_text(super::data::psl_labels_at(3428), seq![0x63u32, 0x69u32, 0x74u32, 0x79u32]);
    fact_label_3429();
    assert forall|c: int| 0 <= c < 7 implies super::data::psl_chars_at(12467 + c) as u32 == (seq![0x73u32, 0x61u32, 0x70u32, 0x70u32, 0x6Fu32, 0x72u32, 0x6Fu32])[c] by {
        assert(c == 0 || c == 1 || c == 2 || c == 3 || c == 4 || c == 5 || c == 6);
        if c == 0 {
            assert(super::data::psl_chars_at(12467) as u32 == seq![0x73u32, 0x61u32, 0x70u32, 0x70u32, 0x6Fu32, 0x72u32, 0x6Fu32][0]);
        }
        if c == 1 {
            assert(super::data::psl_chars_at(12468) as u32 == seq![0x73u32, 0x61u32, 0x70u32, 0x70u32, 0x6Fu32, 0x72u32, 0x6Fu32][1]);
        }
        if c == 2 {
            assert(super::data::psl_chars_at(12469) as u32 == seq![0x73u32, 0x61u32, 0x70u32, 0x70u32, 0x6Fu32, 0x72u32, 0x6Fu32][2]);
        }
        if c == 3 {
            assert(super::data::psl_chars_at(12470) as u32 == seq![0x73u32, 0x61u32, 0x70u32, 0x70u32, 0x6Fu32, 0x72u32, 0x6Fu32][3]);
        }
        if c == 4 {
            assert(super::data::psl_chars_at(12471) as u32 == seq![0x73u32, 0x61u32, 0x70u32, 0x70u32, 0x6Fu32, 0x72u32, 0x6Fu32][4]);
        }
        if c == 5 {
            assert(super::data::psl_chars_at(12472) as u32 == seq![0x73u32, 0x61u32, 0x70u32, 0x70u32, 0x6Fu32, 0x72u32, 0x6Fu32][5]);
        }
        if c == 6 {
            assert(super::data::psl_chars_at(12473) as u32 == seq![0x73u32, 0x61u32, 0x70u32, 0x70u32, 0x6Fu32, 0x72u32, 0x6Fu32][6]);
        }
    }
    lemma_label_text(super::data::psl_labels_at(3429), seq![0x73u32, 0x61u32, 0x70u32, 0x70u32, 0x6Fu32, 0x72u32, 0x6Fu32]);
    fact_label_3430();
    assert forall|c: int| 0 <= c < 2 implies super::data::psl_chars_at(12474 + c) as u32 == (seq![0x6Au32, 0x70u32])[c] by {
        assert(c == 0 || c == 1);
        if c == 0 {
            assert(super::data::psl_chars_at(12474) as u32 == seq![0x6Au32, 0x70u32][0]);
        }
        if c == 1 {
            assert(super::data::psl_chars_at(12475) as u32 == seq![0x6Au32, 0x70u32][1]);
        }
    }
    lemma_label_text(super::data::psl_labels_at(3430), seq![0x6Au32, 0x70u32]);
    assert(super::table::table_rule(1748).labels =~= exc_list()[5].labels);
    assert(super::table::table_rule(1748).exception == exc_list()[5].exception);
}

proof fn fact_row_1750()
    ensures
        super::data::psl_rules_at(1750) == (super::tables::RuleRow { first: 3434, count: 3, exception: true }),
{
    reveal(super::data::PSL_RULES_1);
    assert(super::data::psl_rules_at(1750) == (super::tables::RuleRow { first: 3434, count: 3, exception: true })) by (compute_only);
}

proof fn fact_label_3434()
    ensures
        super::data::psl_labels_at(3434) == (super::tables::LabelRow { start: 12485, len: 4 }),
        super::data::psl_chars_at(12485) == 0x63u8 && super::data::psl_chars_at(12486) == 0x69u8 && super::data::psl_chars_at(12487) == 0x74u8 && super::data::psl_chars_at(12488) == 0x79u8,
{
    reveal(super::data::PSL_LABELS_1);
    reveal(super::data::PSL_CHARS_0);
    assert(super::data::psl_labels_at(3434) == (super::tables::LabelRow { start: 12485, len: 4 })) by (compute_only);
    assert(super::data::psl_chars_at(12485) == 0x63u8 && super::data::psl_chars_at(12486) == 0x69u8 && super::data::psl_chars_at(12487) == 0x74u8 && super::data::psl_chars_at(12488) == 0x79u8) by (compute_only);
}


proof fn fact_label_3435()
    ensures
        super::data::psl_labels_at(3435) == (super::tables::LabelRow { start: 12489, len: 6 }),
        super::data::psl_chars_at(12489) == 0x73u8 && super::data::psl_chars_at(12490) == 0x65u8 && super::data::psl_chars_at(12491) == 0x6Eu8 && super::data::psl_chars_at(12492) == 0x64u8 && super::data::psl_chars_at(12493) == 0x61u8 && super::data::psl_chars_at(12494) == 0x69u8,
{
    reveal(super::data::PSL_LABELS_1);
    reveal(super::data::PSL_CHARS_0);
    assert(super::data::psl_labels_at(3435) == (super::tables::LabelRow { start: 12489, len: 6 })) by (compute_only);
    assert(super::data::psl_chars_at(12489) == 0x73u8 && super::data::psl_chars_at(12490) == 0x65u8 && super::data::psl_chars_at(12491) == 0x6Eu8 && super::data::psl_chars_at(12492) == 0x64u8 && super::data::psl_chars_at(12493) == 0x61u8 && super::data::psl_chars_at(12494) == 0x69u8) by (compute_only);
}


proof fn fact_label_3436()
    ensures
        super::data::psl_labels_at(3436) == (super::tables::LabelRow { start: 12495, len: 2 }),
        super::data::psl_chars_at(12495) == 0x6Au8 && super::data::psl_chars_at(12496) == 0x70u8,
{
    reveal(super::data::PSL_LABELS_1);
    reveal(super::data::PSL_CHARS_0);
    assert(super::data::psl_labels_at(3436) == (super::tables::LabelRow { start: 12495, len: 2 })) by (compute_only);
    assert(super::data::psl_chars_at(12495) == 0x6Au8 && super::data::psl_chars_at(12496) == 0x70u8) by (compute_only);
}

/// Row 1750 of the list is `!city.sendai.jp`.
pub proof fn lemma_exception_rule_1750()
    ensures
        super::table::table_rule(1750) == exc_list()[6],
{
    fact_row_1750();
    fact_label_3434();
    assert forall|c: int| 0 <= c < 4 implies super::data::psl_chars_at(12485 + c) as u32 == (seq![0x63u32, 0x69u32, 0x74u32, 0x79u32])[c] by {
        assert(c == 0 || c == 1 || c == 2 || c == 3);
        if c == 0 {
            assert(super::data::psl_chars_at(12485) as u32 == seq![0x63u32, 0x69u32, 0x74u32, 0x79u32][0]);
        }
        if c == 1 {
            assert(super::data::psl_chars_at(12486) as u32 == seq![0x63u32, 0x69u32, 0x74u32, 0x79u32][1]);
        }
        if c == 2 {
            assert(super::data::psl_chars_at(12487) as u32 == seq![0x63u32, 0x69u32, 0x74u32, 0x79u32][2]);
        }
        if c == 3 {
            assert(super::data::psl_chars_at(12488) as u32 == seq![0x63u32, 0x69u32, 0x74u32, 0x79u32][3]);
        }
    }
    lemma_label_text(super::data::psl_labels_at(3434), seq![0x63u32, 0x69u32, 0x74u32, 0x79u32]);
    fact_label_3435();
    assert forall|c: int| 0 <= c < 6 implies super::data::psl_chars_at(12489 + c) as u32 == (seq![0x73u32, 0x65u32, 0x6Eu32, 0x64u32, 0x61u32, 0x69u32])[c] by {
        assert(c == 0 || c == 1 || c == 2 || c == 3 || c == 4 || c == 5);
        if c == 0 {
            assert(super::data::psl_chars_at(12489) as u32 == seq![0x73u32, 0x65u32, 0x6Eu32, 0x64u32, 0x61u32, 0x69u32][0]);
        }
        if c == 1 {
            assert(super::data::psl_chars_at(12490) as u32 == seq![0x73u32, 0x65u32, 0x6Eu32, 0x64u32, 0x61u32, 0x69u32][1]);
        }
        if c == 2 {
            assert(super::data::psl_chars_at(12491) as u32 == seq![0x73u32, 0x65u32, 0x6Eu32, 0x64u32, 0x61u32, 0x69u32][2]);
        }
        if c == 3 {
            assert(super::data::psl_chars_at(12492) as u32 == seq![0x73u32, 0x65u32, 0x6Eu32, 0x64u32, 0x61u32, 0x69u32][3]);
        }
        if c == 4 {
            assert(super::data::psl_chars_at(12493) as u32 == seq![0x73u32, 0x65u32, 0x6Eu32, 0x64u32, 0x61u32, 0x69u32][4]);
        }
        if c == 5 {
            assert(super::data::psl_chars_at(12494) as u32 == seq![0x73u32, 0x65u32, 0x6Eu32, 0x64u32, 0x61u32, 0x69u32][5]);
        }
    }
    lemma_label_text(super::data::psl_labels_at(3435), seq![0x73u32, 0x65u32, 0x6Eu32, 0x64u32, 0x61u32, 0x69u32]);
    fact_label_3436();
    assert forall|c: int| 0 <= c < 2 implies super::data::psl_chars_at(12495 + c) as u32 == (seq![0x6Au32, 0x70u32])[c] by {
        assert(c == 0 || c == 1);
        if c == 0 {
            assert(super::data::psl_chars_at(12495) as u32 == seq![0x6Au32, 0x70u32][0]);
        }
        if c == 1 {
            assert(super::data::psl_chars_at(12496) as u32 == seq![0x6Au32, 0x70u32][1]);
        }
    }
    lemma_label_text(super::data::psl_labels_at(3436), seq![0x6Au32, 0x70u32]);
    assert(super::table::table_rule(1750).labels =~= exc_list()[6].labels);
    assert(super::table::table_rule(1750).exception == exc_list()[6].exception);
}

proof fn fact_row_1752()
    ensures
        super::data::psl_rules_at(1752) == (super::tables::RuleRow { first: 3440, count: 3, exception: true }),
{
    reveal(super::data::PSL_RULES_1);
    assert(super::data::psl_rules_at(1752) == (super::tables::RuleRow { first: 3440, count: 3, exception: true })) by (compute_only);
}

proof fn fact_label_3440()
    ensures
        super::data::psl_labels_at(3440) == (super::tables::LabelRow { start: 12508, len: 4 }),
        super::data::psl_chars_at(12508) == 0x63u8 && super::data::psl_chars_at(12509) == 0x69u8 && super::data::psl_chars_at(12510) == 0x74u8 && super::data::psl_chars_at(12511) == 0x79u8,
{
    reveal(super::data::PSL_LABELS_1);
    reveal(super::data::PSL_CHARS_0);
    assert(super::data::psl_labels_at(3440) == (super::tables::LabelRow { start: 12508, len: 4 })) by (compute_only);
    assert(super::data::psl_chars_at(12508) == 0x63u8 && super::data::psl_chars_at(12509) == 0x69u8 && super::data::psl_chars_at(12510) == 0x74u8 && super::data::psl_chars_at(12511) == 0x79u8) by (compute_only);
}


proof fn fact_label_3441()
    ensures
        super::data::psl_labels_at(3441) == (super::tables::LabelRow { start: 12512, len: 8 }),
        super::data::psl_chars_at(12512) == 0x79u8 && super::data::psl_chars_at(12513) == 0x6Fu8 && super::data::psl_chars_at(12514) == 0x6Bu8 && super::data::psl_chars_at(12515) == 0x6Fu8 && super::data::psl_chars_at(12516) == 0x68u8 && super::data::psl_chars_at(12517) == 0x61u8 && super::data::psl_chars_at(12518) == 0x6Du8 && super::data::psl_chars_at(12519) == 0x61u8,
{
    reveal(super::data::PSL_LABELS_1);
    reveal(super::data::PSL_CHARS_0);
    assert(super::data::psl_labels_at(3441) == (super::tables::LabelRow { start: 12512, len: 8 })) by (compute_only);
    assert(super::data::psl_chars_at(12512) == 0x79u8 && super::data::psl_chars_at(12513) == 0x6Fu8 && super::data::psl_chars_at(12514) == 0x6Bu8 && super::data::psl_chars_at(12515) == 0x6Fu8 && super::data::psl_chars_at(12516) == 0x68u8 && super::data::psl_chars_at(12517) == 0x61u8 && super::data::psl_chars_at(12518) == 0x6Du8 && super::data::psl_chars_at(12519) == 0x61u8) by (compute_only);
}


proof fn fact_label_3442()
    ensures
        super::data::psl_labels_at(3442) == (super::tables::LabelRow { start: 12520, len: 2 }),
        super::data::psl_chars_at(12520) == 0x6Au8 && super::data::psl_chars_at(12521) == 0x70u8,
{
    reveal(super::data::PSL_LABELS_1);
    reveal(super::data::PSL_CHARS_0);
    assert(super::data::psl_labels_at(3442) == (super::tables::LabelRow { start: 12520, len: 2 })) by (compute_only);
    assert(super::data::psl_chars_at(12520) == 0x6Au8 && super::data::psl_chars_at(12521) == 0x70u8) by (compute_only);
}

/// Row 1752 of the list is `!city.yokohama.jp`.
pub proof fn lemma_exception_rule_1752()
    ensures
        super::table::table_rule(1752) == exc_list()[7],
{
    fact_row_1752();
    fact_label_3440();
    assert forall|c: int| 0 <= c < 4 implies super::data::psl_chars_at(12508 + c) as u32 == (seq![0x63u32, 0x69u32, 0x74u32, 0x79u32])[c] by {
        assert(c == 0 || c == 1 || c == 2 || c == 3);
        if c == 0 {
            assert(super::data::psl_chars_at(12508) as u32 == seq![0x63u32, 0x69u32, 0x74u32, 0x79u32][0]);
        }
        if c == 1 {
            assert(super::data::psl_chars_at(12509) as u32 == seq![0x63u32, 0x69u32, 0x74u32, 0x79u32][1]);
        }
        if c == 2 {
            assert(super::data::psl_chars_at(12510) as u32 == seq![0x63u32, 0x69u32, 0x74u32, 0x79u32][2]);
        }
        if c == 3 {
            assert(super::data::psl_chars_at(12511) as u32 == seq![0x63u32, 0x69u32, 0x74u32, 0x79u32][3]);
        }
    }
    lemma_label_text(super::data::psl_labels_at(3440), seq![0x63u32, 0x69u32, 0x74u32, 0x79u32]);
    fact_label_3441();
    assert forall|c: int| 0 <= c < 8 implies super::data::psl_chars_at(12512 + c) as u32 == (seq![0x79u32, 0x6Fu32, 0x6Bu32, 0x6Fu32, 0x68u32, 0x61u32, 0x6Du32, 0x61u32])[c] by {
        assert(c == 0 || c == 1 || c == 2 || c == 3 || c == 4 || c == 5 || c == 6 || c == 7);
        if c == 0 {
            assert(super::data::psl_chars_at(12512) as u32 == seq![0x79u32, 0x6Fu32, 0x6Bu32, 0x6Fu32, 0x68u32, 0x61u32, 0x6Du32, 0x61u32][0]);
        }
        if c == 1 {
            assert(super::data::psl_chars_at(12513) as u32 == seq![0x79u32, 0x6Fu32, 0x6Bu32, 0x6Fu32, 0x68u32, 0x61u32, 0x6Du32, 0x61u32][1]);
        }
        if c == 2 {
            assert(super::data::psl_chars_at(12514) as u32 == seq![0x79u32, 0x6Fu32, 0x6Bu32, 0x6Fu32, 0x68u32, 0x61u32, 0x6Du32, 0x61u32][2]);
        }
        if c == 3 {
            assert(super::data::psl_chars_at(12515) as u32 == seq![0x79u32, 0x6Fu32, 0x6Bu32, 0x6Fu32, 0x68u32, 0x61u32, 0x6Du32, 0x61u32][3]);
        }
        if c == 4 {
            assert(super::data::psl_chars_at(12516) as u32 == seq![0x79u32, 0x6Fu32, 0x6Bu32, 0x6Fu32, 0x68u32, 0x61u32, 0x6Du32, 0x61u32][4]);
        }
        if c == 5 {
            assert(super::data::psl_chars_at(12517) as u32 == seq![0x79u32, 0x6Fu32, 0x6Bu32, 0x6Fu32, 0x68u32, 0x61u32, 0x6Du32, 0x61u32][5]);
        }
        if c == 6 {
            assert(super::data::psl_chars_at(12518) as u32 == seq![0x79u32, 0x6Fu32, 0x6Bu32, 0x6Fu32, 0x68u32, 0x61u32, 0x6Du32, 0x61u32][6]);
        }
        if c == 7 {
            assert(super::data::psl_chars_at(12519) as u32 == seq![0x79u32, 0x6Fu32, 0x6Bu32, 0x6Fu32, 0x68u32, 0x61u32, 0x6Du32, 0x61u32][7]);
        }
    }
    lemma_label_text(super::data::psl_labels_at(3441), seq![0x79u32, 0x6Fu32, 0x6Bu32, 0x6Fu32, 0x68u32, 0x61u32, 0x6Du32, 0x61u32]);
    fact_label_3442();
    assert forall|c: int| 0 <= c < 2 implies super::data::psl_chars_at(12520 + c) as u32 == (seq![0x6Au32, 0x70u32])[c] by {
        assert(c == 0 || c == 1);
        if c == 0 {
            assert(super::data::psl_chars_at(12520) as u32 == seq![0x6Au32, 0x70u32][0]);
        }
        if c == 1 {
            assert(super::data::psl_chars_at(12521) as u32 == seq![0x6Au32, 0x70u32][1]);
        }
    }
    lemma_label_text(super::data::psl_labels_at(3442), seq![0x6Au32, 0x70u32]);
    assert(super::table::table_rule(1752).labels =~= exc_list()[7].labels);
    assert(super::table::table_rule(1752).exception == exc_list()[7].exception);
}
/// Chunk 0 of the rules table: every rule has a label, and the exception rules are the ones listed.
proof fn lemma_rules_chunk_0()
    ensures
        forall|i: int| 0 <= i < 1333 ==> (super::data::PSL_RULES_0@[i].count >= 1 && (super::data::PSL_RULES_0@[i].exception <==> (i == 635))),
{
    reveal(super::data::PSL_RULES_0);
}

/// Chunk 1 of the rules table: every rule has a label, and the exception rules are the ones listed.
proof fn lemma_rules_chunk_1()
    ensures
        forall|i: int| 0 <= i < 1333 ==> (super::data::PSL_RULES_1@[i].count >= 1 && (super::data::PSL_RULES_1@[i].exception <==> (i == 407 || i == 409 || i == 411 || i == 413 || i == 415 || i == 417 || i == 419))),
{
    reveal(super::data::PSL_RULES_1);
}

/// Chunk 2 of the rules table: every rule has a label, and the exception rules are the ones listed.
proof fn lemma_rules_chunk_2()
    ensures
        forall|i: int| 0 <= i < 1333 ==> (super::data::PSL_RULES_2@[i].count >= 1 && (super::data::PSL_RULES_2@[i].exception <==> (false))),
{
    reveal(super::data::PSL_RULES_2);
}

/// Chunk 3 of the rules table: every rule has a label, and the exception rules are the ones listed.
proof fn lemma_rules_chunk_3()
    ensures
        forall|i: int| 0 <= i < 1333 ==> (super::data::PSL_RULES_3@[i].count >= 1 && (super::data::PSL_RULES_3@[i].exception <==> (false))),
{
    reveal(super::data::PSL_RULES_3);
}

/// Chunk 4 of the rules table: every rule has a label, and the exception rules are the ones listed.
proof fn lemma_rules_chunk_4()
    ensures
        forall|i: int| 0 <= i < 1333 ==> (super::data::PSL_RULES_4@[i].count >= 1 && (super::data::PSL_RULES_4@[i].exception <==> (false))),
{
    reveal(super::data::PSL_RULES_4);
}

/// Chunk 5 of the rules table: every rule has a label, and the exception rules are the ones listed.
proof fn lemma_rules_chunk_5()
    ensures
        forall|i: int| 0 <= i < 1333 ==> (super::data::PSL_RULES_5@[i].count >= 1 && (super::data::PSL_RULES_5@[i].exception <==> (false))),
{
    reveal(super::data::PSL_RULES_5);
}

/// Chunk 6 of the rules table: every rule has a label, and the exception rules are the ones listed.
proof fn lemma_rules_chunk_6()
    ensures
        forall|i: int| 0 <= i < 1333 ==> (super::data::PSL_RULES_6@[i].count >= 1 && (super::data::PSL_RULES_6@[i].exception <==> (false))),
{
    reveal(super::data::PSL_RULES_6);
}

/// Chunk 7 of the rules table: every rule has a label, and the exception rules are the ones listed.
proof fn lemma_rules_chunk_7()
    ensures
        forall|i: int| 0 <= i < 1065 ==> (super::data::PSL_RULES_7@[i].count >= 1 && (super::data::PSL_RULES_7@[i].exception <==> (false))),
{
    reveal(super::data::PSL_RULES_7);
}
/// Every rule of the table has a label, and the exception rules are the
/// listed rows.
proof fn lemma_row_facts(i: int)
    requires
        0 <= i < super::data::PSL_RULES_LEN,
    ensures
        super::data::psl_rules_at(i).count >= 1,
        super::data::psl_rules_at(i).exception <==> is_exception_row(i),
{
    lemma_rules_chunk_0();
    lemma_rules_chunk_1();
    lemma_rules_chunk_2();
    lemma_rules_chunk_3();
    lemma_rules_chunk_4();
    lemma_rules_chunk_5();
    lemma_rules_chunk_6();
    lemma_rules_chunk_7();
}

/// An exception row is the `k`-th exception rule, for some `k`.
proof fn lemma_exception_index(i: int)
    requires
        is_exception_row(i),
    ensures
        exists|k: int| 0 <= k < 8 && i == exc_row(k) && super::table::table_rule(i) == exc_list()[k],
{
    lemma_exception_rule_635();
    lemma_exception_rule_1740();
    lemma_exception_rule_1742();
    lemma_exception_rule_1744();
    lemma_exception_rule_1746();
    lemma_exception_rule_1748();
    lemma_exception_rule_1750();
    lemma_exception_rule_1752();
    if i == 635 {
        assert(exc_row(0) == 635);
    } else if i == 1740 {
        assert(exc_row(1) == 1740);
    } else if i == 1742 {
        assert(exc_row(2) == 1742);
    } else if i == 1744 {
        assert(exc_row(3) == 1744);
    } else if i == 1746 {
        assert(exc_row(4) == 1746);
    } else if i == 1748 {
        assert(exc_row(5) == 1748);
    } else if i == 1750 {
        assert(exc_row(6) == 1750);
    } else {
        assert(exc_row(7) == 1752);
    }
}

/// The generated Public Suffix List is well formed.
pub proof fn lemma_table_wf()
    ensures
        super::wf::rules_wf(super::table::psl_rules()),
{
    lemma_exc_list_ok();
    lemma_all_ok(exc_list(), 0);
    let rules = super::table::psl_rules();
    assert forall|i: int| 0 <= i < rules.len() implies (#[trigger] rules[i]).labels.len() >= 1 by {
        lemma_row_facts(i);
        assert(rules[i] == super::table::table_rule(i));
        assert(rules[i].labels.len() == super::data::psl_rules_at(i).count);
    }
    assert forall|i: int| 0 <= i < rules.len() && (#[trigger] rules[i]).exception implies rules[i].labels.len() >= 2 && forall|x: int|
        0 <= x < rules[i].labels.len() ==> (#[trigger] rules[i].labels[x]) != star_label() by {
        lemma_row_facts(i);
        assert(rules[i] == super::table::table_rule(i));
        assert(super::data::psl_rules_at(i).exception);
        lemma_exception_index(i);
        let k = choose|k: int| 0 <= k < 8 && i == exc_row(k) && super::table::table_rule(i) == exc_list()[k];
        lemma_star_free(exc_list()[k].labels, 0);
    }
    assert forall|i: int, j: int|
        0 <= i < rules.len() && 0 <= j < rules.len() && i != j && (#[trigger] rules[i]).exception && (#[trigger] rules[j]).exception implies !(
        rules[i].labels.len() <= rules[j].labels.len() && rules[i].labels == rules[j].labels.skip((rules[j].labels.len() - rules[i].labels.len()) as int)) by {
        lemma_row_facts(i);
        lemma_row_facts(j);
        assert(rules[i] == super::table::table_rule(i));
        assert(rules[j] == super::table::table_rule(j));
        assert(super::data::psl_rules_at(i).exception);
        assert(super::data::psl_rules_at(j).exception);
        lemma_exception_index(i);
        lemma_exception_index(j);
        let ki = choose|k: int| 0 <= k < 8 && i == exc_row(k) && super::table::table_rule(i) == exc_list()[k];
        let kj = choose|k: int| 0 <= k < 8 && j == exc_row(k) && super::table::table_rule(j) == exc_list()[k];
        assert(ki != kj);
        assert(not_suffix(exc_list()[ki], exc_list()[kj]));
    }
}

} // verus!
