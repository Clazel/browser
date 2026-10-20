//! A second transcription of the parts of UTS #46 processing that other
//! documents define: RFC 5893 §2 (the Bidi rule), RFC 5892 Appendix A.1
//! and A.2 (the ContextJ rules), and the label-level validity criteria of
//! UTS #46 §4.1 that use them, written from those texts without reference
//! to [`super::spec`], and lemmas proving the two equal on every label.
//!
//! No second standard defines these rules, so the transcription differs
//! in form instead: each condition is a statement over positions in the
//! label ("for every character", "there is a character such that"), as
//! the RFCs word them, where the spec walks the label recursively. A
//! misreading in one form fails the equivalence.
//!
//! Modelling choices:
//! - Labels are `Seq<u32>`; a character's properties are read from the
//!   generated tables directly ([`super::tables`]): Bidi_Class (none above
//!   U+10FFFF), Joining_Type (none for U), Canonical_Combining_Class (0 if
//!   absent), Status (disallowed if absent), General_Category=Mark.
//! - RFC 5892's "RegExpMatch" for U+200C at position `i` is read as: the
//!   expression matches a substring of the label in which this U+200C is
//!   the `‌` of the expression.

#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The Bidi_Class at position `i`.
pub open spec fn class_at(label: Seq<u32>, i: int) -> Option<super::tables::BidiClass> {
    match super::tables::bidi_class_find(label[i], 0, super::data::BIDI_CLASS_LEN as int) {
        Some(row) => Some(super::data::bidi_class_at(row).class),
        None => None,
    }
}

/// The class is R or AL.
pub open spec fn is_r_or_al(c: Option<super::tables::BidiClass>) -> bool {
    c == Some(super::tables::BidiClass::RightToLeft) || c == Some(super::tables::BidiClass::ArabicLetter)
}

/// RFC 5893 condition 2's set: "R, AL, AN, EN, ES, CS, ET, ON, BN, or NSM".
pub open spec fn in_condition_2(c: Option<super::tables::BidiClass>) -> bool {
    is_r_or_al(c) || c == Some(super::tables::BidiClass::ArabicNumber) || c == Some(
        super::tables::BidiClass::EuropeanNumber,
    ) || c == Some(super::tables::BidiClass::EuropeanSeparator) || c == Some(
        super::tables::BidiClass::CommonSeparator,
    ) || c == Some(super::tables::BidiClass::EuropeanTerminator) || c == Some(
        super::tables::BidiClass::OtherNeutral,
    ) || c == Some(super::tables::BidiClass::BoundaryNeutral) || c == Some(
        super::tables::BidiClass::NonspacingMark,
    )
}

/// RFC 5893 condition 5's set: "L, EN, ES, CS, ET, ON, BN, or NSM".
pub open spec fn in_condition_5(c: Option<super::tables::BidiClass>) -> bool {
    c == Some(super::tables::BidiClass::LeftToRight) || c == Some(super::tables::BidiClass::EuropeanNumber)
        || c == Some(super::tables::BidiClass::EuropeanSeparator) || c == Some(
        super::tables::BidiClass::CommonSeparator,
    ) || c == Some(super::tables::BidiClass::EuropeanTerminator) || c == Some(
        super::tables::BidiClass::OtherNeutral,
    ) || c == Some(super::tables::BidiClass::BoundaryNeutral) || c == Some(
        super::tables::BidiClass::NonspacingMark,
    )
}

/// "the end of the label must be a character with Bidi property in
/// `ok`, followed by zero or more characters with Bidi property NSM".
pub open spec fn ends_with(label: Seq<u32>, rtl: bool) -> bool {
    exists|e: int|
        0 <= e < label.len() && (if rtl {
            is_r_or_al(#[trigger] class_at(label, e)) || class_at(label, e) == Some(
                super::tables::BidiClass::EuropeanNumber,
            ) || class_at(label, e) == Some(super::tables::BidiClass::ArabicNumber)
        } else {
            class_at(label, e) == Some(super::tables::BidiClass::LeftToRight) || class_at(label, e) == Some(
                super::tables::BidiClass::EuropeanNumber,
            )
        }) && forall|k: int| e < k < label.len() ==> #[trigger] class_at(label, k) == Some(
            super::tables::BidiClass::NonspacingMark,
        )
}

/// "an EN is present" (or AN, for `en` false).
pub open spec fn present(label: Seq<u32>, en: bool) -> bool {
    exists|i: int|
        0 <= i < label.len() && #[trigger] class_at(label, i) == Some(
            if en {
                super::tables::BidiClass::EuropeanNumber
            } else {
                super::tables::BidiClass::ArabicNumber
            },
        )
}

/// RFC 5893 §2: "All of the conditions must be satisfied", for a
/// non-empty label.
pub open spec fn rfc_5893_bidi_rule(label: Seq<u32>) -> bool {
    let first = class_at(label, 0);
    // 1. "The first character must be a character with Bidi property L,
    //    R, or AL. If it has the R or AL property, it is an RTL label; if
    //    it has the L property, it is an LTR label."
    &&& (first == Some(super::tables::BidiClass::LeftToRight) || is_r_or_al(first))
    // 2. "In an RTL label, only characters with the Bidi properties R, AL,
    //    AN, EN, ES, CS, ET, ON, BN, or NSM are allowed."
    &&& is_r_or_al(first) ==> forall|i: int| 0 <= i < label.len() ==> in_condition_2(#[trigger] class_at(label, i))
    // 3. "In an RTL label, the end of the label must be a character with
    //    Bidi property R, AL, EN, or AN, followed by zero or more
    //    characters with Bidi property NSM."
    &&& is_r_or_al(first) ==> ends_with(label, true)
    // 4. "In an RTL label, if an EN is present, no AN may be present, and
    //    vice versa."
    &&& is_r_or_al(first) ==> !(present(label, true) && present(label, false))
    // 5. "In an LTR label, only characters with the Bidi properties L, EN,
    //    ES, CS, ET, ON, BN, or NSM are allowed."
    &&& first == Some(super::tables::BidiClass::LeftToRight) ==> forall|i: int|
        0 <= i < label.len() ==> in_condition_5(#[trigger] class_at(label, i))
    // 6. "In an LTR label, the end of the label must be a character with
    //    Bidi property L or EN, followed by zero or more characters with
    //    Bidi property NSM."
    &&& first == Some(super::tables::BidiClass::LeftToRight) ==> ends_with(label, false)
}

/// The Joining_Type at position `i` (`None` is U).
pub open spec fn joining_at(label: Seq<u32>, i: int) -> Option<super::tables::JoiningType> {
    match super::tables::joining_type_find(label[i], 0, super::data::JOINING_TYPE_LEN as int) {
        Some(row) => Some(super::data::joining_type_at(row).joining_type),
        None => None,
    }
}

/// Canonical_Combining_Class at position `i`.
pub open spec fn class_of(c: u32) -> u8 {
    match super::tables::combining_class_find(c, 0, super::data::COMBINING_CLASS_LEN as int) {
        Some(row) => super::data::combining_class_at(row).class,
        None => 0,
    }
}

/// "If Canonical_Combining_Class(Before(cp)) .eq. Virama Then True"; the
/// Virama class is 9.
pub open spec fn after_virama(label: Seq<u32>, i: int) -> bool {
    1 <= i && class_of(label[i - 1]) == 9
}

/// "RegExpMatch((Joining_Type:{L,D})(Joining_Type:T)*‌
/// (Joining_Type:T)*(Joining_Type:{R,D}))" around the U+200C at `i`.
pub open spec fn regexp_match(label: Seq<u32>, i: int) -> bool {
    exists|k: int, m: int|
        0 <= k < i < m < label.len() && (#[trigger] joining_at(label, k) == Some(
            super::tables::JoiningType::LeftJoining,
        ) || joining_at(label, k) == Some(super::tables::JoiningType::DualJoining)) && (forall|x: int|
            k < x < i ==> #[trigger] joining_at(label, x) == Some(super::tables::JoiningType::Transparent)) && (
        forall|x: int| i < x < m ==> #[trigger] joining_at(label, x) == Some(super::tables::JoiningType::Transparent))
            && (#[trigger] joining_at(label, m) == Some(super::tables::JoiningType::RightJoining) || joining_at(
            label,
            m,
        ) == Some(super::tables::JoiningType::DualJoining))
}

/// RFC 5892 Appendix A.1 and A.2 for every U+200C and U+200D.
pub open spec fn rfc_5892_context_j(label: Seq<u32>) -> bool {
    forall|i: int|
        0 <= i < label.len() ==> {
            // A.1 ZERO WIDTH NON-JOINER: "False; If ... Virama Then True; If
            // RegExpMatch(...) Then True;"
            &&& #[trigger] label[i] == 0x200C ==> after_virama(label, i) || regexp_match(label, i)
            // A.2 ZERO WIDTH JOINER: "False; If ... Virama Then True;"
            &&& label[i] == 0x200D ==> after_virama(label, i)
        }
}

/// UTS #46 §5: the Status of `c` (disallowed if no row holds it).
pub open spec fn status_of(c: u32) -> super::tables::Status {
    match super::tables::idna_find(c, 0, super::data::IDNA_MAPPING_LEN as int) {
        Some(row) => super::data::idna_mapping_at(row).status,
        None => super::tables::Status::Disallowed,
    }
}

/// UTS #46 §4.1 criteria 5 and 7 for every code point: "The label must
/// not contain a U+002E ( . ) FULL STOP." "Each code point in the label
/// must only have certain Status values ... For Nontransitional
/// Processing, each value must be either valid or deviation. In addition,
/// if UseSTD3ASCIIRules=true and the code point is an ASCII code point
/// (U+0000..U+007F), then it must be a lowercase letter (a-z), a digit
/// (0-9), or a hyphen-minus (U+002D)."
pub open spec fn criteria_5_and_7(label: Seq<u32>, use_std3_ascii_rules: bool) -> bool {
    forall|i: int|
        0 <= i < label.len() ==> {
            &&& #[trigger] label[i] != 0x2E
            &&& (status_of(label[i]) == super::tables::Status::Valid || status_of(label[i])
                == super::tables::Status::Deviation)
            &&& use_std3_ascii_rules && label[i] < 0x80 ==> (0x61 <= label[i] <= 0x7A || 0x30 <= label[i] <= 0x39
                || label[i] == 0x2D)
        }
}

// ===========================================================================
// Equivalence with the spec.
// ===========================================================================

proof fn lemma_class_at(label: Seq<u32>, i: int)
    requires
        0 <= i < label.len(),
    ensures
        class_at(label, i) == super::spec::bidi_class(label[i]),
{
}

proof fn lemma_all_allowed_forall(label: Seq<u32>, rtl: bool)
    ensures
        super::spec::all_allowed(label, rtl) == forall|i: int|
            0 <= i < label.len() ==> (if rtl {
                in_condition_2(#[trigger] class_at(label, i))
            } else {
                in_condition_5(class_at(label, i))
            }),
    decreases label.len()
{
    if label.len() > 0 {
        let d = label.drop_last();
        lemma_all_allowed_forall(d, rtl);
        assert forall|i: int| 0 <= i < d.len() implies #[trigger] class_at(d, i) == class_at(label, i) by {
            assert(d[i] == label[i]);
        }
        let last = (label.len() - 1) as int;
        lemma_class_at(label, last);
        let c = class_at(label, last);
        assert(super::spec::rtl_allowed(c) == in_condition_2(c));
        assert(super::spec::ltr_allowed(c) == in_condition_5(c));
        if super::spec::all_allowed(label, rtl) {
            assert forall|i: int| 0 <= i < label.len() implies (if rtl {
                in_condition_2(#[trigger] class_at(label, i))
            } else {
                in_condition_5(class_at(label, i))
            }) by {
                if i < last {
                    assert(class_at(d, i) == class_at(label, i));
                }
            }
        } else {
            if (if rtl {
                in_condition_2(c)
            } else {
                in_condition_5(c)
            }) {
                let j = choose|j: int|
                    0 <= j < d.len() && !(if rtl {
                        in_condition_2(#[trigger] class_at(d, j))
                    } else {
                        in_condition_5(class_at(d, j))
                    });
                assert(class_at(d, j) == class_at(label, j));
            }
        }
    }
}

proof fn lemma_contains_present(label: Seq<u32>, en: bool)
    ensures
        super::spec::contains_class(
            label,
            if en {
                super::tables::BidiClass::EuropeanNumber
            } else {
                super::tables::BidiClass::ArabicNumber
            },
        ) == present(label, en),
    decreases label.len()
{
    if label.len() > 0 {
        let d = label.drop_last();
        lemma_contains_present(d, en);
        let last = (label.len() - 1) as int;
        lemma_class_at(label, last);
        if present(d, en) {
            let j = choose|j: int|
                0 <= j < d.len() && #[trigger] class_at(d, j) == Some(
                    if en {
                        super::tables::BidiClass::EuropeanNumber
                    } else {
                        super::tables::BidiClass::ArabicNumber
                    },
                );
            assert(d[j] == label[j]);
            assert(class_at(label, j) == class_at(d, j));
        }
        if present(label, en) {
            let j = choose|j: int|
                0 <= j < label.len() && #[trigger] class_at(label, j) == Some(
                    if en {
                        super::tables::BidiClass::EuropeanNumber
                    } else {
                        super::tables::BidiClass::ArabicNumber
                    },
                );
            if j < last {
                assert(d[j] == label[j]);
                assert(class_at(d, j) == class_at(label, j));
            }
        }
    }
}

proof fn lemma_ends_with(label: Seq<u32>, rtl: bool)
    ensures
        super::spec::ends_correctly(label, rtl) == ends_with(label, rtl),
    decreases label.len()
{
    if label.len() > 0 {
        let d = label.drop_last();
        lemma_ends_with(d, rtl);
        let last = (label.len() - 1) as int;
        lemma_class_at(label, last);
        assert forall|i: int| 0 <= i < d.len() implies #[trigger] class_at(d, i) == class_at(label, i) by {
            assert(d[i] == label[i]);
        }
        let c = class_at(label, last);
        if c == Some(super::tables::BidiClass::NonspacingMark) {
            // The spec skips it; so does the "followed by NSM" part.
            if ends_with(d, rtl) {
                let e = choose|e: int|
                    0 <= e < d.len() && (if rtl {
                        is_r_or_al(#[trigger] class_at(d, e)) || class_at(d, e) == Some(
                            super::tables::BidiClass::EuropeanNumber,
                        ) || class_at(d, e) == Some(super::tables::BidiClass::ArabicNumber)
                    } else {
                        class_at(d, e) == Some(super::tables::BidiClass::LeftToRight) || class_at(d, e) == Some(
                            super::tables::BidiClass::EuropeanNumber,
                        )
                    }) && forall|k: int| e < k < d.len() ==> #[trigger] class_at(d, k) == Some(
                        super::tables::BidiClass::NonspacingMark,
                    );
                assert(class_at(label, e) == class_at(d, e));
                assert forall|k: int| e < k < label.len() implies #[trigger] class_at(label, k) == Some(
                    super::tables::BidiClass::NonspacingMark,
                ) by {
                    if k < last {
                        assert(class_at(d, k) == class_at(label, k));
                    }
                }
            }
            if ends_with(label, rtl) {
                let e = choose|e: int|
                    0 <= e < label.len() && (if rtl {
                        is_r_or_al(#[trigger] class_at(label, e)) || class_at(label, e) == Some(
                            super::tables::BidiClass::EuropeanNumber,
                        ) || class_at(label, e) == Some(super::tables::BidiClass::ArabicNumber)
                    } else {
                        class_at(label, e) == Some(super::tables::BidiClass::LeftToRight) || class_at(label, e)
                            == Some(super::tables::BidiClass::EuropeanNumber)
                    }) && forall|k: int| e < k < label.len() ==> #[trigger] class_at(label, k) == Some(
                        super::tables::BidiClass::NonspacingMark,
                    );
                assert(e != last);
                assert(class_at(d, e) == class_at(label, e));
                assert forall|k: int| e < k < d.len() implies #[trigger] class_at(d, k) == Some(
                    super::tables::BidiClass::NonspacingMark,
                ) by {
                    assert(class_at(d, k) == class_at(label, k));
                }
            }
        } else {
            // The last character itself decides, for both.
            if ends_with(label, rtl) {
                let e = choose|e: int|
                    0 <= e < label.len() && (if rtl {
                        is_r_or_al(#[trigger] class_at(label, e)) || class_at(label, e) == Some(
                            super::tables::BidiClass::EuropeanNumber,
                        ) || class_at(label, e) == Some(super::tables::BidiClass::ArabicNumber)
                    } else {
                        class_at(label, e) == Some(super::tables::BidiClass::LeftToRight) || class_at(label, e)
                            == Some(super::tables::BidiClass::EuropeanNumber)
                    }) && forall|k: int| e < k < label.len() ==> #[trigger] class_at(label, k) == Some(
                        super::tables::BidiClass::NonspacingMark,
                    );
                if e < last {
                    assert(class_at(label, last) == Some(super::tables::BidiClass::NonspacingMark));
                }
            }
            if super::spec::ends_correctly(label, rtl) {
                assert(forall|k: int| last < k < label.len() ==> #[trigger] class_at(label, k) == Some(
                    super::tables::BidiClass::NonspacingMark,
                ));
            }
        }
    }
}

/// The Bidi rules agree on every non-empty label.
pub proof fn lemma_bidi_rule_equal(label: Seq<u32>)
    requires
        label.len() > 0,
    ensures
        rfc_5893_bidi_rule(label) == super::spec::bidi_rule(label),
{
    lemma_class_at(label, 0);
    lemma_all_allowed_forall(label, true);
    lemma_all_allowed_forall(label, false);
    lemma_ends_with(label, true);
    lemma_ends_with(label, false);
    lemma_contains_present(label, true);
    lemma_contains_present(label, false);
}

proof fn lemma_joining_at(label: Seq<u32>, i: int)
    requires
        0 <= i < label.len(),
    ensures
        joining_at(label, i) == super::spec::joining_type(label[i]),
{
}

/// The left half of the expression: some L or D at `k <= j`, with only T
/// after it up to `j`.
pub open spec fn left_match(label: Seq<u32>, j: int) -> bool {
    exists|k: int|
        0 <= k <= j && (#[trigger] joining_at(label, k) == Some(super::tables::JoiningType::LeftJoining)
            || joining_at(label, k) == Some(super::tables::JoiningType::DualJoining)) && forall|x: int|
            k < x <= j ==> #[trigger] joining_at(label, x) == Some(super::tables::JoiningType::Transparent)
}

/// The right half: some R or D at `m >= j`, with only T before it from `j`.
pub open spec fn right_match(label: Seq<u32>, j: int) -> bool {
    exists|m: int|
        j <= m < label.len() && (#[trigger] joining_at(label, m) == Some(
            super::tables::JoiningType::RightJoining,
        ) || joining_at(label, m) == Some(super::tables::JoiningType::DualJoining)) && forall|x: int|
            j <= x < m ==> #[trigger] joining_at(label, x) == Some(super::tables::JoiningType::Transparent)
}

proof fn lemma_joins_left(label: Seq<u32>, j: int)
    requires
        j < label.len(),
    ensures
        super::spec::joins_left(label, j) == left_match(label, j),
    decreases j + 1
{
    if j >= 0 {
        lemma_joining_at(label, j);
        let t = joining_at(label, j);
        if t == Some(super::tables::JoiningType::Transparent) {
            lemma_joins_left(label, j - 1);
            if left_match(label, j - 1) {
                let k = choose|k: int|
                    0 <= k <= j - 1 && (#[trigger] joining_at(label, k) == Some(
                        super::tables::JoiningType::LeftJoining,
                    ) || joining_at(label, k) == Some(super::tables::JoiningType::DualJoining)) && forall|x: int|
                        k < x <= j - 1 ==> #[trigger] joining_at(label, x) == Some(
                            super::tables::JoiningType::Transparent,
                        );
                assert(forall|x: int| k < x <= j ==> #[trigger] joining_at(label, x) == Some(
                    super::tables::JoiningType::Transparent,
                ));
            }
            if left_match(label, j) {
                let k = choose|k: int|
                    0 <= k <= j && (#[trigger] joining_at(label, k) == Some(super::tables::JoiningType::LeftJoining)
                        || joining_at(label, k) == Some(super::tables::JoiningType::DualJoining)) && forall|x: int|
                        k < x <= j ==> #[trigger] joining_at(label, x) == Some(
                            super::tables::JoiningType::Transparent,
                        );
                assert(k != j);
                assert(forall|x: int| k < x <= j - 1 ==> #[trigger] joining_at(label, x) == Some(
                    super::tables::JoiningType::Transparent,
                ));
            }
        } else {
            if left_match(label, j) {
                let k = choose|k: int|
                    0 <= k <= j && (#[trigger] joining_at(label, k) == Some(super::tables::JoiningType::LeftJoining)
                        || joining_at(label, k) == Some(super::tables::JoiningType::DualJoining)) && forall|x: int|
                        k < x <= j ==> #[trigger] joining_at(label, x) == Some(
                            super::tables::JoiningType::Transparent,
                        );
                if k < j {
                    assert(joining_at(label, j) == Some(super::tables::JoiningType::Transparent));
                }
            }
            if super::spec::joins_left(label, j) {
                assert(forall|x: int| j < x <= j ==> #[trigger] joining_at(label, x) == Some(
                    super::tables::JoiningType::Transparent,
                ));
            }
        }
    }
}

proof fn lemma_joins_right(label: Seq<u32>, j: int)
    requires
        0 <= j,
    ensures
        super::spec::joins_right(label, j) == right_match(label, j),
    decreases label.len() - j
{
    if j < label.len() {
        lemma_joining_at(label, j);
        let t = joining_at(label, j);
        if t == Some(super::tables::JoiningType::Transparent) {
            lemma_joins_right(label, j + 1);
            if right_match(label, j + 1) {
                let m = choose|m: int|
                    j + 1 <= m < label.len() && (#[trigger] joining_at(label, m) == Some(
                        super::tables::JoiningType::RightJoining,
                    ) || joining_at(label, m) == Some(super::tables::JoiningType::DualJoining)) && forall|x: int|
                        j + 1 <= x < m ==> #[trigger] joining_at(label, x) == Some(
                            super::tables::JoiningType::Transparent,
                        );
                assert(forall|x: int| j <= x < m ==> #[trigger] joining_at(label, x) == Some(
                    super::tables::JoiningType::Transparent,
                ));
            }
            if right_match(label, j) {
                let m = choose|m: int|
                    j <= m < label.len() && (#[trigger] joining_at(label, m) == Some(
                        super::tables::JoiningType::RightJoining,
                    ) || joining_at(label, m) == Some(super::tables::JoiningType::DualJoining)) && forall|x: int|
                        j <= x < m ==> #[trigger] joining_at(label, x) == Some(
                            super::tables::JoiningType::Transparent,
                        );
                assert(m != j);
                assert(forall|x: int| j + 1 <= x < m ==> #[trigger] joining_at(label, x) == Some(
                    super::tables::JoiningType::Transparent,
                ));
            }
        } else {
            if right_match(label, j) {
                let m = choose|m: int|
                    j <= m < label.len() && (#[trigger] joining_at(label, m) == Some(
                        super::tables::JoiningType::RightJoining,
                    ) || joining_at(label, m) == Some(super::tables::JoiningType::DualJoining)) && forall|x: int|
                        j <= x < m ==> #[trigger] joining_at(label, x) == Some(
                            super::tables::JoiningType::Transparent,
                        );
                if m > j {
                    assert(joining_at(label, j) == Some(super::tables::JoiningType::Transparent));
                }
            }
            if super::spec::joins_right(label, j) {
                assert(forall|x: int| j <= x < j ==> #[trigger] joining_at(label, x) == Some(
                    super::tables::JoiningType::Transparent,
                ));
            }
        }
    }
}

proof fn lemma_regexp(label: Seq<u32>, i: int)
    requires
        0 <= i < label.len(),
    ensures
        regexp_match(label, i) == (super::spec::joins_left(label, i - 1) && super::spec::joins_right(label, i + 1)),
{
    lemma_joins_left(label, i - 1);
    lemma_joins_right(label, i + 1);
    if left_match(label, i - 1) && right_match(label, i + 1) {
        let k = choose|k: int|
            0 <= k <= i - 1 && (#[trigger] joining_at(label, k) == Some(super::tables::JoiningType::LeftJoining)
                || joining_at(label, k) == Some(super::tables::JoiningType::DualJoining)) && forall|x: int|
                k < x <= i - 1 ==> #[trigger] joining_at(label, x) == Some(super::tables::JoiningType::Transparent);
        let m = choose|m: int|
            i + 1 <= m < label.len() && (#[trigger] joining_at(label, m) == Some(
                super::tables::JoiningType::RightJoining,
            ) || joining_at(label, m) == Some(super::tables::JoiningType::DualJoining)) && forall|x: int|
                i + 1 <= x < m ==> #[trigger] joining_at(label, x) == Some(super::tables::JoiningType::Transparent);
        assert(forall|x: int| k < x < i ==> #[trigger] joining_at(label, x) == Some(
            super::tables::JoiningType::Transparent,
        ));
        assert(forall|x: int| i < x < m ==> #[trigger] joining_at(label, x) == Some(
            super::tables::JoiningType::Transparent,
        ));
    }
    if regexp_match(label, i) {
        let (k, m) = choose|k: int, m: int|
            0 <= k < i < m < label.len() && (#[trigger] joining_at(label, k) == Some(
                super::tables::JoiningType::LeftJoining,
            ) || joining_at(label, k) == Some(super::tables::JoiningType::DualJoining)) && (forall|x: int|
                k < x < i ==> #[trigger] joining_at(label, x) == Some(super::tables::JoiningType::Transparent)) && (
            forall|x: int| i < x < m ==> #[trigger] joining_at(label, x) == Some(super::tables::JoiningType::Transparent))
                && (#[trigger] joining_at(label, m) == Some(super::tables::JoiningType::RightJoining) || joining_at(
                label,
                m,
            ) == Some(super::tables::JoiningType::DualJoining));
        assert(forall|x: int| k < x <= i - 1 ==> #[trigger] joining_at(label, x) == Some(
            super::tables::JoiningType::Transparent,
        ));
        assert(forall|x: int| i + 1 <= x < m ==> #[trigger] joining_at(label, x) == Some(
            super::tables::JoiningType::Transparent,
        ));
    }
}

proof fn lemma_context_j_from(label: Seq<u32>, i: nat)
    requires
        i <= label.len(),
    ensures
        super::spec::context_j_from(label, i) == forall|j: int|
            i <= j < label.len() ==> {
                &&& #[trigger] label[j] == 0x200C ==> after_virama(label, j) || regexp_match(label, j)
                &&& label[j] == 0x200D ==> after_virama(label, j)
            },
    decreases label.len() - i
{
    if i < label.len() {
        lemma_context_j_from(label, i + 1);
        lemma_regexp(label, i as int);
    }
}

/// Criteria 5 and 7 agree on every label.
pub proof fn lemma_criteria_5_and_7_equal(label: Seq<u32>, flags: super::spec::Flags)
    ensures
        criteria_5_and_7(label, flags.use_std3_ascii_rules) == super::spec::code_points_allowed(label, flags),
    decreases label.len()
{
    if label.len() > 0 {
        let d = label.drop_last();
        lemma_criteria_5_and_7_equal(d, flags);
        assert forall|i: int| 0 <= i < d.len() implies #[trigger] d[i] == label[i] by {}
        let last = (label.len() - 1) as int;
        let c = label[last];
        assert(super::spec::status(c) == status_of(c));
        if criteria_5_and_7(label, flags.use_std3_ascii_rules) {
            assert(label[last] == c);
            assert forall|i: int| 0 <= i < d.len() implies {
                &&& #[trigger] d[i] != 0x2E
                &&& (status_of(d[i]) == super::tables::Status::Valid || status_of(d[i])
                    == super::tables::Status::Deviation)
                &&& flags.use_std3_ascii_rules && d[i] < 0x80 ==> (0x61 <= d[i] <= 0x7A || 0x30 <= d[i] <= 0x39
                    || d[i] == 0x2D)
            } by {
                assert(d[i] == label[i]);
            }
        }
        if super::spec::code_points_allowed(label, flags) {
            assert forall|i: int| 0 <= i < label.len() implies {
                &&& #[trigger] label[i] != 0x2E
                &&& (status_of(label[i]) == super::tables::Status::Valid || status_of(label[i])
                    == super::tables::Status::Deviation)
                &&& flags.use_std3_ascii_rules && label[i] < 0x80 ==> (0x61 <= label[i] <= 0x7A || 0x30 <= label[i]
                    <= 0x39 || label[i] == 0x2D)
            } by {
                if i < last {
                    assert(d[i] == label[i]);
                }
            }
        }
    }
}

/// The ContextJ rules agree on every label.
pub proof fn lemma_context_j_equal(label: Seq<u32>)
    ensures
        rfc_5892_context_j(label) == super::spec::context_j_from(label, 0),
{
    lemma_context_j_from(label, 0);
}

} // verus!
