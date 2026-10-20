//! Executable UTS #46 processing, ToASCII, ToUnicode and the URL
//! Standard's domain parser, proven to meet [`super::contract`] (relative
//! to the tables). Each function mirrors the spec function of the same
//! name; the step comments and quotes live in [`super::spec`].

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

use super::spec::Flags;
use super::tables::{BidiClass, JoiningType, Status};

verus! {

/// The labels' strings.
pub open spec fn labels_view(v: Seq<Vec<u32>>) -> Seq<Seq<u32>> {
    v.map_values(|x: Vec<u32>| x@)
}

// ---------------------------------------------------------------------------
// Lookups.
// ---------------------------------------------------------------------------

fn status_exec(c: u32) -> (r: Status)
    ensures
        r == status(c),
{
    match super::tables::idna_find_exec(c) {
        Some(i) => super::data::idna_mapping_at_exec(i).status,
        None => Status::Disallowed,
    }
}

fn is_mark_exec(c: u32) -> (r: bool)
    ensures
        r == is_mark(c),
{
    super::tables::mark_find_exec(c).is_some()
}

fn bidi_class_exec(c: u32) -> (r: Option<BidiClass>)
    ensures
        r == bidi_class(c),
{
    let i = super::tables::bidi_class_find_exec(c)?;
    Some(super::data::bidi_class_at_exec(i).class)
}

fn joining_type_exec(c: u32) -> (r: Option<JoiningType>)
    ensures
        r == joining_type(c),
{
    let i = super::tables::joining_type_find_exec(c)?;
    Some(super::data::joining_type_at_exec(i).joining_type)
}

// ---------------------------------------------------------------------------
// Step 1, Map.
// ---------------------------------------------------------------------------

fn push_mapped(out: &mut Vec<u32>, c: u32)
    ensures
        final(out)@ == old(out)@ + map_code_point(c),
{
    match super::tables::idna_find_exec(c) {
        Some(i) => {
            let row = super::data::idna_mapping_at_exec(i);
            match row.status {
                Status::Disallowed | Status::Deviation | Status::Valid => out.push(c),
                Status::Ignored => {
                    assert(old(out)@ + Seq::<u32>::empty() =~= old(out)@);
                },
                Status::Mapped => super::tables::push_idna_mapping_data(out, row.mapping_start, row.mapping_len),
            }
        },
        None => out.push(c),
    }
}

fn map_exec(s: &[u32]) -> (out: Vec<u32>)
    ensures
        out@ == map(s@),
{
    let mut out: Vec<u32> = Vec::new();
    let mut i: usize = 0;
    while i < s.len()
        invariant
            i <= s.len(),
            out@ == map(s@.subrange(0, i as int)),
        decreases s.len() - i
    {
        proof {
            let next = s@.subrange(0, i as int + 1);
            assert(next.drop_last() =~= s@.subrange(0, i as int));
        }
        if let Some(&c) = s.get(i) {
            push_mapped(&mut out, c);
        }
        i = i.saturating_add(1);
    }
    assert(s@.subrange(0, s.len() as int) =~= s@);
    out
}

// ---------------------------------------------------------------------------
// Step 3, Break, and joining.
// ---------------------------------------------------------------------------

fn break_exec(s: &[u32]) -> (labels: Vec<Vec<u32>>)
    ensures
        labels_view(labels@) == break_labels(s@),
{
    let mut labels: Vec<Vec<u32>> = Vec::new();
    labels.push(Vec::new());
    let mut i: usize = 0;
    assert(labels_view(labels@) =~= break_labels(s@.subrange(0, 0)));
    while i < s.len()
        invariant
            i <= s.len(),
            labels.len() >= 1,
            labels_view(labels@) == break_labels(s@.subrange(0, i as int)),
        decreases s.len() - i
    {
        let ghost prev = labels_view(labels@);
        proof {
            let next = s@.subrange(0, i as int + 1);
            assert(next.drop_last() =~= s@.subrange(0, i as int));
        }
        let c = match s.get(i) {
            Some(&c) => c,
            None => 0,
        };
        if c == 0x2E {
            labels.push(Vec::new());
            assert(labels_view(labels@) =~= prev.push(seq![]));
        } else {
            let mut last = labels.pop().unwrap_or_default();
            last.push(c);
            labels.push(last);
            assert(labels_view(labels@) =~= prev.update(prev.len() - 1, prev.last().push(c)));
        }
        i = i.saturating_add(1);
    }
    assert(s@.subrange(0, s.len() as int) =~= s@);
    labels
}

fn join_exec(labels: &[Vec<u32>]) -> (out: Vec<u32>)
    ensures
        out@ == join_labels(labels_view(labels@)),
{
    let mut out: Vec<u32> = Vec::new();
    let mut k: usize = 0;
    assert(labels_view(labels@).subrange(0, 0) =~= Seq::<Seq<u32>>::empty());
    while k < labels.len()
        invariant
            k <= labels.len(),
            out@ == join_labels(labels_view(labels@).subrange(0, k as int)),
        decreases labels.len() - k
    {
        let ghost all = labels_view(labels@);
        proof {
            let next = all.subrange(0, k as int + 1);
            assert(next.drop_last() =~= all.subrange(0, k as int));
            assert(next.last() == labels@[k as int]@);
            if k == 0 {
                assert(next =~= seq![labels@[0]@]);
            }
        }
        if k > 0 {
            out.push(0x2E);
        }
        if let Some(label) = labels.get(k) {
            let ghost before = out@;
            let mut j: usize = 0;
            while j < label.len()
                invariant
                    j <= label.len(),
                    out@ == before + label@.subrange(0, j as int),
                decreases label.len() - j
            {
                if let Some(&c) = label.get(j) {
                    out.push(c);
                }
                assert(out@ =~= before + label@.subrange(0, j as int + 1));
                j = j.saturating_add(1);
            }
            assert(label@.subrange(0, label.len() as int) =~= label@);
        }
        k = k.saturating_add(1);
    }
    assert(labels_view(labels@).subrange(0, labels.len() as int) =~= labels_view(labels@));
    out
}

// ---------------------------------------------------------------------------
// Step 4's conversion.
// ---------------------------------------------------------------------------

fn contains_non_ascii_exec(s: &[u32]) -> (r: bool)
    ensures
        r == contains_non_ascii(s@),
{
    let mut i: usize = 0;
    while i < s.len()
        invariant
            i <= s.len(),
            !contains_non_ascii(s@.subrange(0, i as int)),
        decreases s.len() - i
    {
        proof {
            let next = s@.subrange(0, i as int + 1);
            assert(next.drop_last() =~= s@.subrange(0, i as int));
        }
        match s.get(i) {
            Some(&c) if c > 0x7F => {
                proof {
                    super::lemmas::lemma_contains_non_ascii(s@, i as int);
                }
                return true;
            },
            _ => {},
        }
        i = i.saturating_add(1);
    }
    assert(s@.subrange(0, s.len() as int) =~= s@);
    false
}

fn starts_with_xn_exec(s: &[u32]) -> (r: bool)
    ensures
        r == starts_with_xn(s@),
{
    s.len() >= 4 && s.first() == Some(&0x78) && s.get(1) == Some(&0x6E) && s.get(2) == Some(&0x2D) && s.get(3)
        == Some(&0x2D)
}

/// An executable [`Converted`].
pub struct ConvertedExec {
    /// The label.
    pub label: Vec<u32>,
    /// Whether the conversion recorded an error.
    pub error: bool,
    /// Whether the label is checked against the validity criteria.
    pub validate: bool,
}

/// The spec's view of a [`ConvertedExec`].
pub open spec fn converted_view(c: ConvertedExec) -> Converted {
    Converted { label: c.label@, error: c.error, validate: c.validate }
}

/// The spec's view of a sequence of [`ConvertedExec`].
pub open spec fn converted_views(v: Seq<ConvertedExec>) -> Seq<Converted> {
    v.map_values(|c: ConvertedExec| converted_view(c))
}

fn convert_label_exec(label: Vec<u32>) -> (r: ConvertedExec)
    ensures
        converted_view(r) == convert_label(label@),
{
    if starts_with_xn_exec(&label) {
        if contains_non_ascii_exec(&label) {
            ConvertedExec { label, error: true, validate: false }
        } else {
            let rest = match label.split_at_checked(4) {
                Some((_, rest)) => rest,
                None => &label,
            };
            assert(rest@ =~= label@.subrange(4, label.len() as int));
            match crate::punycode::decode::decode(rest) {
                None => ConvertedExec { label, error: true, validate: false },
                Some(decoded) => {
                    let error = decoded.is_empty() || !contains_non_ascii_exec(&decoded);
                    ConvertedExec { label: decoded, error, validate: true }
                },
            }
        }
    } else {
        ConvertedExec { label, error: false, validate: true }
    }
}

// ---------------------------------------------------------------------------
// RFC 5893: the Bidi rule.
// ---------------------------------------------------------------------------

fn is_r_al_an_exec(c: u32) -> (r: bool)
    ensures
        r == is_r_al_an(c),
{
    matches!(bidi_class_exec(c), Some(BidiClass::RightToLeft) | Some(BidiClass::ArabicLetter) | Some(BidiClass::ArabicNumber))
}

fn is_rtl_label_exec(label: &[u32]) -> (r: bool)
    ensures
        r == is_rtl_label(label@),
{
    let mut i: usize = 0;
    while i < label.len()
        invariant
            i <= label.len(),
            !is_rtl_label(label@.subrange(0, i as int)),
        decreases label.len() - i
    {
        proof {
            let next = label@.subrange(0, i as int + 1);
            assert(next.drop_last() =~= label@.subrange(0, i as int));
        }
        match label.get(i) {
            Some(&c) if is_r_al_an_exec(c) => {
                proof {
                    super::lemmas::lemma_is_rtl_label(label@, i as int);
                }
                return true;
            },
            _ => {},
        }
        i = i.saturating_add(1);
    }
    assert(label@.subrange(0, label.len() as int) =~= label@);
    false
}

fn rtl_allowed_exec(class: Option<BidiClass>) -> (r: bool)
    ensures
        r == rtl_allowed(class),
{
    matches!(class, Some(BidiClass::RightToLeft) | Some(BidiClass::ArabicLetter) | Some(BidiClass::ArabicNumber) | Some( BidiClass::EuropeanNumber, ) | Some(BidiClass::EuropeanSeparator) | Some(BidiClass::CommonSeparator) | Some( BidiClass::EuropeanTerminator, ) | Some(BidiClass::OtherNeutral) | Some(BidiClass::BoundaryNeutral) | Some(BidiClass::NonspacingMark))
}

fn ltr_allowed_exec(class: Option<BidiClass>) -> (r: bool)
    ensures
        r == ltr_allowed(class),
{
    matches!(class, Some(BidiClass::LeftToRight) | Some(BidiClass::EuropeanNumber) | Some(BidiClass::EuropeanSeparator) | Some( BidiClass::CommonSeparator, ) | Some(BidiClass::EuropeanTerminator) | Some(BidiClass::OtherNeutral) | Some(BidiClass::BoundaryNeutral) | Some(BidiClass::NonspacingMark))
}

fn all_allowed_exec(label: &[u32], rtl: bool) -> (r: bool)
    ensures
        r == all_allowed(label@, rtl),
{
    let mut i: usize = 0;
    while i < label.len()
        invariant
            i <= label.len(),
            all_allowed(label@.subrange(0, i as int), rtl),
        decreases label.len() - i
    {
        proof {
            let next = label@.subrange(0, i as int + 1);
            assert(next.drop_last() =~= label@.subrange(0, i as int));
        }
        let c = match label.get(i) {
            Some(&c) => c,
            None => 0,
        };
        let class = bidi_class_exec(c);
        let ok = if rtl {
            rtl_allowed_exec(class)
        } else {
            ltr_allowed_exec(class)
        };
        if !ok {
            proof {
                super::lemmas::lemma_all_allowed(label@, i as int, rtl);
            }
            return false;
        }
        i = i.saturating_add(1);
    }
    assert(label@.subrange(0, label.len() as int) =~= label@);
    true
}

fn ends_correctly_exec(label: &[u32], rtl: bool) -> (r: bool)
    ensures
        r == ends_correctly(label@, rtl),
{
    let mut k = label.len();
    assert(label@.subrange(0, k as int) =~= label@);
    while k > 0
        invariant
            k <= label.len(),
            ends_correctly(label@, rtl) == ends_correctly(label@.subrange(0, k as int), rtl),
        decreases k
    {
        let prev = k.saturating_sub(1);
        proof {
            let p = label@.subrange(0, k as int);
            assert(p.drop_last() =~= label@.subrange(0, prev as int));
        }
        let c = match label.get(prev) {
            Some(&c) => c,
            None => 0,
        };
        match bidi_class_exec(c) {
            Some(BidiClass::NonspacingMark) => {},
            Some(BidiClass::RightToLeft) | Some(BidiClass::ArabicLetter) | Some(BidiClass::ArabicNumber) => {
                return rtl;
            },
            Some(BidiClass::EuropeanNumber) => {
                return true;
            },
            Some(BidiClass::LeftToRight) => {
                return !rtl;
            },
            _ => {
                return false;
            },
        }
        k = prev;
    }
    false
}

fn contains_en_exec(label: &[u32]) -> (r: bool)
    ensures
        r == contains_class(label@, BidiClass::EuropeanNumber),
{
    let mut i: usize = 0;
    while i < label.len()
        invariant
            i <= label.len(),
            !contains_class(label@.subrange(0, i as int), BidiClass::EuropeanNumber),
        decreases label.len() - i
    {
        proof {
            let next = label@.subrange(0, i as int + 1);
            assert(next.drop_last() =~= label@.subrange(0, i as int));
        }
        let c = match label.get(i) {
            Some(&c) => c,
            None => 0,
        };
        if let Some(BidiClass::EuropeanNumber) = bidi_class_exec(c) {
            proof {
                super::lemmas::lemma_contains_class(label@, i as int, BidiClass::EuropeanNumber);
            }
            return true;
        }
        i = i.saturating_add(1);
    }
    assert(label@.subrange(0, label.len() as int) =~= label@);
    false
}

fn contains_an_exec(label: &[u32]) -> (r: bool)
    ensures
        r == contains_class(label@, BidiClass::ArabicNumber),
{
    let mut i: usize = 0;
    while i < label.len()
        invariant
            i <= label.len(),
            !contains_class(label@.subrange(0, i as int), BidiClass::ArabicNumber),
        decreases label.len() - i
    {
        proof {
            let next = label@.subrange(0, i as int + 1);
            assert(next.drop_last() =~= label@.subrange(0, i as int));
        }
        let c = match label.get(i) {
            Some(&c) => c,
            None => 0,
        };
        if let Some(BidiClass::ArabicNumber) = bidi_class_exec(c) {
            proof {
                super::lemmas::lemma_contains_class(label@, i as int, BidiClass::ArabicNumber);
            }
            return true;
        }
        i = i.saturating_add(1);
    }
    assert(label@.subrange(0, label.len() as int) =~= label@);
    false
}

fn bidi_rule_exec(label: &[u32]) -> (r: bool)
    requires
        label.len() > 0,
    ensures
        r == bidi_rule(label@),
{
    let first = match label.first() {
        Some(&c) => bidi_class_exec(c),
        None => None,
    };
    match first {
        Some(BidiClass::RightToLeft) | Some(BidiClass::ArabicLetter) => {
            all_allowed_exec(label, true) && ends_correctly_exec(label, true) && !(contains_en_exec(label)
                && contains_an_exec(label))
        },
        Some(BidiClass::LeftToRight) => all_allowed_exec(label, false) && ends_correctly_exec(label, false),
        _ => false,
    }
}

// ---------------------------------------------------------------------------
// RFC 5892: the ContextJ rules.
// ---------------------------------------------------------------------------

/// [`joins_left`] from position `i - 1`.
fn joins_left_exec(label: &[u32], i: usize) -> (r: bool)
    requires
        i <= label.len(),
    ensures
        r == joins_left(label@, i as int - 1),
{
    let mut k = i;
    while k > 0
        invariant
            k <= i <= label.len(),
            joins_left(label@, i as int - 1) == joins_left(label@, k as int - 1),
        decreases k
    {
        let prev = k.saturating_sub(1);
        let c = match label.get(prev) {
            Some(&c) => c,
            None => 0,
        };
        match joining_type_exec(c) {
            Some(JoiningType::Transparent) => {},
            Some(JoiningType::LeftJoining) | Some(JoiningType::DualJoining) => {
                return true;
            },
            _ => {
                return false;
            },
        }
        k = prev;
    }
    false
}

/// [`joins_right`] from position `j`.
fn joins_right_exec(label: &[u32], j: usize) -> (r: bool)
    ensures
        r == joins_right(label@, j as int),
{
    let mut k = j;
    while k < label.len()
        invariant
            j <= k,
            joins_right(label@, j as int) == joins_right(label@, k as int),
        decreases label.len() - k
    {
        let c = match label.get(k) {
            Some(&c) => c,
            None => 0,
        };
        match joining_type_exec(c) {
            Some(JoiningType::Transparent) => {},
            Some(JoiningType::RightJoining) | Some(JoiningType::DualJoining) => {
                return true;
            },
            _ => {
                return false;
            },
        }
        k = k.saturating_add(1);
    }
    false
}

fn virama_before_exec(label: &[u32], i: usize) -> (r: bool)
    requires
        i <= label.len(),
    ensures
        r == virama_before(label@, i as int),
{
    i > 0 && match label.get(i.saturating_sub(1)) {
        Some(&c) => super::nfc::ccc_exec(c) == 9,
        None => false,
    }
}

fn context_j_exec(label: &[u32]) -> (r: bool)
    ensures
        r == context_j_from(label@, 0),
{
    let mut i: usize = 0;
    while i < label.len()
        invariant
            i <= label.len(),
            context_j_from(label@, 0) == context_j_from(label@, i as nat),
        decreases label.len() - i
    {
        let c = match label.get(i) {
            Some(&c) => c,
            None => 0,
        };
        let ok = if c == 0x200C {
            virama_before_exec(label, i) || (joins_left_exec(label, i) && joins_right_exec(
                label,
                i.saturating_add(1),
            ))
        } else if c == 0x200D {
            virama_before_exec(label, i)
        } else {
            true
        };
        if !ok {
            return false;
        }
        i = i.saturating_add(1);
    }
    true
}

// ---------------------------------------------------------------------------
// §4.1 Validity Criteria.
// ---------------------------------------------------------------------------

fn status_allowed_exec(c: u32, flags: Flags) -> (r: bool)
    ensures
        r == status_allowed(c, flags),
{
    let status_ok = matches!(status_exec(c), Status::Valid | Status::Deviation);
    status_ok && (!(flags.use_std3_ascii_rules && c <= 0x7F) || (0x61..=0x7A).contains(&c) || (0x30..=0x39).contains(
        &c,
    ) || c == 0x2D)
}

fn code_points_allowed_exec(label: &[u32], flags: Flags) -> (r: bool)
    ensures
        r == code_points_allowed(label@, flags),
{
    let mut i: usize = 0;
    while i < label.len()
        invariant
            i <= label.len(),
            code_points_allowed(label@.subrange(0, i as int), flags),
        decreases label.len() - i
    {
        proof {
            let next = label@.subrange(0, i as int + 1);
            assert(next.drop_last() =~= label@.subrange(0, i as int));
        }
        let c = match label.get(i) {
            Some(&c) => c,
            None => 0,
        };
        if c == 0x2E || !status_allowed_exec(c, flags) {
            proof {
                super::lemmas::lemma_code_points_allowed(label@, i as int, flags);
            }
            return false;
        }
        i = i.saturating_add(1);
    }
    assert(label@.subrange(0, label.len() as int) =~= label@);
    true
}

fn equal_exec(a: &[u32], b: &[u32]) -> (r: bool)
    ensures
        r == (a@ == b@),
{
    if a.len() != b.len() {
        return false;
    }
    let mut i: usize = 0;
    while i < a.len()
        invariant
            i <= a.len() == b.len(),
            a@.subrange(0, i as int) == b@.subrange(0, i as int),
        decreases a.len() - i
    {
        if a.get(i) != b.get(i) {
            return false;
        }
        assert(a@.subrange(0, i as int + 1) =~= a@.subrange(0, i as int).push(a@[i as int]));
        assert(b@.subrange(0, i as int + 1) =~= b@.subrange(0, i as int).push(b@[i as int]));
        i = i.saturating_add(1);
    }
    assert(a@.subrange(0, a.len() as int) =~= a@);
    assert(b@.subrange(0, b.len() as int) =~= b@);
    true
}

fn is_valid_label_exec(label: &[u32], flags: Flags, bidi_domain: bool) -> (r: bool)
    ensures
        r == is_valid_label(label@, flags, bidi_domain),
{
    let (first, last) = match (label.first(), label.last()) {
        (Some(&f), Some(&l)) => (f, l),
        _ => return true,
    };
    let normalized = super::nfc::nfc(label);
    if !equal_exec(&normalized, label) {
        return false;
    }
    if flags.check_hyphens {
        if label.len() >= 4 && label.get(2) == Some(&0x2D) && label.get(3) == Some(&0x2D) {
            return false;
        }
        if first == 0x2D || last == 0x2D {
            return false;
        }
    } else if starts_with_xn_exec(label) {
        return false;
    }
    if is_mark_exec(first) {
        return false;
    }
    if !code_points_allowed_exec(label, flags) {
        return false;
    }
    if flags.check_joiners && !context_j_exec(label) {
        return false;
    }
    if flags.check_bidi && bidi_domain && !bidi_rule_exec(label) {
        return false;
    }
    true
}

// ---------------------------------------------------------------------------
// §4 Processing.
// ---------------------------------------------------------------------------

/// UTS #46 §4 Processing: the converted labels, and whether an error was
/// recorded.
fn process_exec(domain_name: &[u32], flags: Flags) -> (r: (Vec<Vec<u32>>, bool))
    ensures
        labels_view(r.0@) == process(domain_name@, flags).labels,
        r.1 == process(domain_name@, flags).error,
{
    let mapped = map_exec(domain_name);
    let normalized = super::nfc::nfc(&mapped);
    let labels = break_exec(&normalized);
    let ghost spec_labels = labels_view(labels@);
    // The conversion, label by label.
    let mut converted: Vec<ConvertedExec> = Vec::new();
    let mut k: usize = 0;
    let n = labels.len();
    assert(converted_views(converted@) =~= convert_labels(spec_labels.subrange(0, 0)));
    while k < n
        invariant
            k <= n,
            n == labels.len(),
            spec_labels == labels_view(labels@),
            converted_views(converted@) == convert_labels(spec_labels.subrange(0, k as int)),
        decreases n - k
    {
        let ghost before = converted_views(converted@);
        let label = match labels.get(k) {
            Some(l) => l.clone(),
            None => Vec::new(),
        };
        assert(label@ == spec_labels[k as int]);
        let c = convert_label_exec(label);
        converted.push(c);
        proof {
            let next = spec_labels.subrange(0, k as int + 1);
            assert(next.drop_last() =~= spec_labels.subrange(0, k as int));
            assert(converted_views(converted@) =~= before.push(convert_label(spec_labels[k as int])));
        }
        k = k.saturating_add(1);
    }
    assert(spec_labels.subrange(0, n as int) =~= spec_labels);
    let ghost all = converted_views(converted@);
    // Whether the domain name is a Bidi domain name.
    let mut bidi_domain = false;
    let mut k: usize = 0;
    while k < converted.len()
        invariant
            k <= converted.len(),
            all == converted_views(converted@),
            bidi_domain == is_bidi_domain_name(all.subrange(0, k as int)),
        decreases converted.len() - k
    {
        proof {
            let next = all.subrange(0, k as int + 1);
            assert(next.drop_last() =~= all.subrange(0, k as int));
        }
        match converted.get(k) {
            Some(c) if !bidi_domain => bidi_domain = is_rtl_label_exec(&c.label),
            _ => {},
        }
        k = k.saturating_add(1);
    }
    assert(all.subrange(0, converted.len() as int) =~= all);
    // The errors, and the labels' strings.
    let mut error = false;
    let mut out: Vec<Vec<u32>> = Vec::new();
    let m = converted.len();
    let mut k: usize = 0;
    assert(labels_view(out@) =~= converted_labels(all.subrange(0, 0)));
    while k < m
        invariant
            k <= m,
            m == converted.len(),
            all == converted_views(converted@),
            error == any_error(all.subrange(0, k as int), flags, bidi_domain),
            bidi_domain == is_bidi_domain_name(all),
            labels_view(out@) == converted_labels(all.subrange(0, k as int)),
        decreases m - k
    {
        let ghost before = labels_view(out@);
        if let Some(c) = converted.get(k) {
            assert(converted_view(*c) == all[k as int]);
            let bad = c.error || (c.validate && !is_valid_label_exec(&c.label, flags, bidi_domain));
            error = error || bad;
            out.push(c.label.clone());
        }
        proof {
            let next = all.subrange(0, k as int + 1);
            assert(next.drop_last() =~= all.subrange(0, k as int));
            assert(labels_view(out@) =~= before.push(all[k as int].label));
        }
        k = k.saturating_add(1);
    }
    assert(all.subrange(0, m as int) =~= all);
    (out, error)
}

// ---------------------------------------------------------------------------
// §4.2 ToASCII and §4.3 ToUnicode.
// ---------------------------------------------------------------------------

/// Appends `s` to `out`.
fn extend_exec(out: &mut Vec<u32>, s: &[u32])
    ensures
        final(out)@ == old(out)@ + s@,
{
    let ghost before = old(out)@;
    let mut j: usize = 0;
    while j < s.len()
        invariant
            j <= s.len(),
            out@ == before + s@.subrange(0, j as int),
        decreases s.len() - j
    {
        if let Some(&c) = s.get(j) {
            out.push(c);
        }
        assert(out@ =~= before + s@.subrange(0, j as int + 1));
        j = j.saturating_add(1);
    }
    assert(s@.subrange(0, s.len() as int) =~= s@);
}

fn to_ascii_label_exec(label: Vec<u32>) -> (r: Option<Vec<u32>>)
    ensures
        match r {
            Some(v) => to_ascii_label(label@) == Some(v@),
            None => to_ascii_label(label@) is None,
        },
{
    if contains_non_ascii_exec(&label) {
        match crate::punycode::encode::encode(&label) {
            Some(encoded) => {
                let mut out: Vec<u32> = Vec::new();
                extend_exec(&mut out, &[0x78, 0x6E, 0x2D, 0x2D]);
                extend_exec(&mut out, &encoded);
                assert(out@ =~= seq![0x78u32, 0x6E, 0x2D, 0x2D] + encoded@);
                Some(out)
            },
            None => None,
        }
    } else {
        Some(label)
    }
}

fn label_lengths_ok_exec(labels: &[Vec<u32>]) -> (r: bool)
    ensures
        r == label_lengths_ok(labels_view(labels@)),
{
    let ghost all = labels_view(labels@);
    let mut k: usize = 0;
    assert(all.subrange(0, 0) =~= Seq::<Seq<u32>>::empty());
    while k < labels.len()
        invariant
            k <= labels.len(),
            all == labels_view(labels@),
            label_lengths_ok(all.subrange(0, k as int)),
        decreases labels.len() - k
    {
        proof {
            let next = all.subrange(0, k as int + 1);
            assert(next.drop_last() =~= all.subrange(0, k as int));
        }
        let len = match labels.get(k) {
            Some(l) => l.len(),
            None => 0,
        };
        if !(1..=63).contains(&len) {
            proof {
                super::lemmas::lemma_label_lengths_ok(all, k as int);
            }
            return false;
        }
        k = k.saturating_add(1);
    }
    assert(all.subrange(0, labels.len() as int) =~= all);
    true
}

/// UTS #46 §4.2 ToASCII. `None` is a failure value.
pub fn to_ascii(domain_name: &[u32], flags: Flags, verify_dns_length: bool) -> (r: Option<Vec<u32>>)
    ensures
        super::contract::to_ascii_ensures(
            domain_name@,
            flags,
            verify_dns_length,
            match r {
                Some(v) => Some(v@),
                None => None,
            },
        ),
{
    let (labels, error) = process_exec(domain_name, flags);
    let ghost spec_labels = labels_view(labels@);
    let n = labels.len();
    let mut out: Vec<Vec<u32>> = Vec::new();
    let mut k: usize = 0;
    assert(labels_view(out@) =~= Seq::<Seq<u32>>::empty());
    assert(spec_labels.subrange(0, 0) =~= Seq::<Seq<u32>>::empty());
    while k < n
        invariant
            k <= n,
            n == labels.len(),
            spec_labels == labels_view(labels@),
            spec_labels == process(domain_name@, flags).labels,
            to_ascii_labels(spec_labels.subrange(0, k as int)) == Some(labels_view(out@)),
        decreases n - k
    {
        let ghost before = labels_view(out@);
        let label = match labels.get(k) {
            Some(l) => l.clone(),
            None => Vec::new(),
        };
        assert(label@ == spec_labels[k as int]);
        proof {
            let next = spec_labels.subrange(0, k as int + 1);
            assert(next.drop_last() =~= spec_labels.subrange(0, k as int));
            super::lemmas::lemma_to_ascii_labels_none(spec_labels, k as int);
        }
        match to_ascii_label_exec(label) {
            Some(v) => out.push(v),
            None => {
                return None;
            },
        }
        assert(labels_view(out@) =~= before.push(labels_view(out@).last()));
        k = k.saturating_add(1);
    }
    assert(spec_labels.subrange(0, n as int) =~= spec_labels);
    if error {
        return None;
    }
    let joined = join_exec(&out);
    if verify_dns_length {
        let length = match joined.last() {
            Some(&0x2E) => joined.len().saturating_sub(1),
            _ => joined.len(),
        };
        if !label_lengths_ok_exec(&out) || !(1..=253).contains(&length) {
            return None;
        }
    }
    Some(joined)
}

/// UTS #46 §4.3 ToUnicode: the string, and whether an error was recorded.
pub fn to_unicode(domain_name: &[u32], flags: Flags) -> (r: (Vec<u32>, bool))
    ensures
        super::contract::to_unicode_ensures(domain_name@, flags, r.0@, r.1),
{
    let (labels, error) = process_exec(domain_name, flags);
    (join_exec(&labels), error)
}

// ---------------------------------------------------------------------------
// URL Standard §3.3.
// ---------------------------------------------------------------------------

fn url_flags_exec(be_strict: bool) -> (r: Flags)
    ensures
        r == url_flags(be_strict),
{
    Flags { use_std3_ascii_rules: be_strict, check_hyphens: be_strict, check_bidi: true, check_joiners: true }
}

/// URL §3.3 "domain parser ToASCII".
pub fn domain_parser_to_ascii(domain: &[u32], be_strict: bool) -> (r: Option<Vec<u32>>)
    ensures
        super::contract::domain_parser_to_ascii_ensures(
            domain@,
            be_strict,
            match r {
                Some(v) => Some(v@),
                None => None,
            },
        ),
{
    to_ascii(domain, url_flags_exec(be_strict), be_strict)
}

fn contains_forbidden_exec(s: &[u32]) -> (r: bool)
    ensures
        r == contains_forbidden_domain_code_point(s@),
{
    let mut i: usize = 0;
    while i < s.len()
        invariant
            i <= s.len(),
            !contains_forbidden_domain_code_point(s@.subrange(0, i as int)),
        decreases s.len() - i
    {
        proof {
            let next = s@.subrange(0, i as int + 1);
            assert(next.drop_last() =~= s@.subrange(0, i as int));
        }
        let c = match s.get(i) {
            Some(&c) => c,
            None => 0,
        };
        let forbidden = c == 0x00 || c == 0x09 || c == 0x0A || c == 0x0D || c == 0x20 || c == 0x23 || c == 0x2F
            || c == 0x3A || c == 0x3C || c == 0x3E || c == 0x3F || c == 0x40 || c == 0x5B || c == 0x5C || c
            == 0x5D || c == 0x5E || c == 0x7C || c <= 0x1F || c == 0x25 || c == 0x7F;
        if forbidden {
            proof {
                super::lemmas::lemma_contains_forbidden(s@, i as int);
            }
            return true;
        }
        i = i.saturating_add(1);
    }
    assert(s@.subrange(0, s.len() as int) =~= s@);
    false
}

fn ascii_lowercase_exec(s: &[u32]) -> (r: Vec<u32>)
    ensures
        r@ == ascii_lowercase(s@),
{
    let mut out: Vec<u32> = Vec::new();
    let mut i: usize = 0;
    while i < s.len()
        invariant
            i <= s.len(),
            out@ == ascii_lowercase(s@.subrange(0, i as int)),
        decreases s.len() - i
    {
        proof {
            let next = s@.subrange(0, i as int + 1);
            assert(next.drop_last() =~= s@.subrange(0, i as int));
        }
        if let Some(&c) = s.get(i) {
            // Never saturates: c <= 0x5A.
            out.push(
                if (0x41..=0x5A).contains(&c) {
                    c.saturating_add(0x20)
                } else {
                    c
                },
            );
        }
        i = i.saturating_add(1);
    }
    assert(s@.subrange(0, s.len() as int) =~= s@);
    out
}

/// URL §3.3 "domain parser". `None` is failure.
pub fn domain_parser(domain: &[u32], be_strict: bool) -> (r: Option<Vec<u32>>)
    ensures
        super::contract::domain_parser_ensures(
            domain@,
            be_strict,
            match r {
                Some(v) => Some(v@),
                None => None,
            },
        ),
{
    if be_strict {
        return domain_parser_to_ascii(domain, true);
    }
    let result = if !contains_non_ascii_exec(domain) {
        ascii_lowercase_exec(domain)
    } else {
        domain_parser_to_ascii(domain, false)?
    };
    if result.is_empty() || contains_forbidden_exec(&result) {
        return None;
    }
    Some(result)
}

/// URL §3.3 "domain to Unicode".
pub fn domain_to_unicode(domain: &[u32]) -> (r: Vec<u32>)
    ensures
        super::contract::domain_to_unicode_ensures(domain@, r@),
{
    let (result, error) = to_unicode(domain, url_flags_exec(false));
    if error {
        let mut copy: Vec<u32> = Vec::new();
        let mut i: usize = 0;
        while i < domain.len()
            invariant
                i <= domain.len(),
                copy@ == domain@.subrange(0, i as int),
            decreases domain.len() - i
        {
            if let Some(&c) = domain.get(i) {
                copy.push(c);
            }
            assert(copy@ =~= domain@.subrange(0, i as int + 1));
            i = i.saturating_add(1);
        }
        assert(domain@.subrange(0, domain.len() as int) =~= domain@);
        copy
    } else {
        result
    }
}

} // verus!

#[cfg(test)]
mod tests {
    use super::{domain_parser, domain_parser_to_ascii, domain_to_unicode};

    fn scalars(s: &str) -> Vec<u32> {
        s.chars().map(u32::from).collect()
    }

    fn string(v: &[u32]) -> String {
        v.iter().filter_map(|&c| char::from_u32(c)).collect()
    }

    fn to_ascii(s: &str, strict: bool) -> Option<String> {
        domain_parser_to_ascii(&scalars(s), strict).map(|v| string(&v))
    }

    #[test]
    fn examples() {
        assert_eq!(
            to_ascii("fa\u{DF}.de", false).as_deref(),
            Some("xn--fa-hia.de")
        );
        assert_eq!(
            to_ascii("B\u{FC}cher.de", false).as_deref(),
            Some("xn--bcher-kva.de")
        );
        assert_eq!(
            to_ascii("\u{2615}.example", false).as_deref(),
            Some("xn--53h.example")
        );
        assert_eq!(
            to_ascii("a\u{300}.\u{5D0}\u{308}", false).as_deref(),
            Some("xn--0ca.xn--ssa73l")
        );
        // Disallowed code point.
        assert_eq!(to_ascii("a\u{FFFD}b", false), None);
        // Bad Punycode.
        assert_eq!(to_ascii("xn--a.com", false), None);
        // Hyphens only matter when strict.
        assert_eq!(to_ascii("-x.com", false).as_deref(), Some("-x.com"));
        assert_eq!(to_ascii("-x.com", true), None);
        // DNS length only when strict: the empty root label.
        assert_eq!(to_ascii("x.com.", false).as_deref(), Some("x.com."));
        assert_eq!(to_ascii("x.com.", true), None);
        // The domain parser: ASCII is lowercased without IDNA.
        let parsed = domain_parser(&scalars("xn--8i7caa"), false).map(|v| string(&v));
        assert_eq!(parsed.as_deref(), Some("xn--8i7caa"));
        assert_eq!(domain_parser(&scalars("a%b"), false), None);
        assert_eq!(
            string(&domain_to_unicode(&scalars("xn--fa-hia.de"))),
            "fa\u{DF}.de"
        );
        assert_eq!(
            string(&domain_to_unicode(&scalars("xn--8i7caa"))),
            "xn--8i7caa"
        );
    }
}
