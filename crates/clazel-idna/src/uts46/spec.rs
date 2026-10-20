//! Executable-style specification of UTS #46 processing and of the URL
//! Standard's use of it. Nothing here runs; it defines what "correct"
//! means. Sources, each transcribed with its step numbers:
//!
//! - UTS #46, "Unicode IDNA Compatibility Processing", Version 18.0.0,
//!   Revision 36, 2026-08-31 (<https://www.unicode.org/reports/tr46/tr46-36.html>):
//!   §4 Processing, §4.1 Validity Criteria, §4.2 ToASCII, §4.3 ToUnicode.
//! - URL Standard §3.3 IDNA (<https://url.spec.whatwg.org/#idna>), commit
//!   `845bafca22fb0c5a42c4bf384a9bdea525a2f10d` (19 October 2026): "domain
//!   parser", "domain parser ToASCII", "domain to Unicode"; and §3.2's
//!   forbidden host and domain code points.
//! - The Unicode Standard, Version 18.0, §3.11 Normalization Forms (D68
//!   canonical decomposition, D107 starter, D108–D109 canonical ordering,
//!   D114 primary composite, D115 blocked, D117 canonical composition) and
//!   §3.12 Conjoining Jamo Behavior (Hangul syllable decomposition and
//!   composition): Normalization Form C, which UTS #46 step 2 and validity
//!   criterion 1 use.
//! - RFC 5892, Appendix A.1 (ZERO WIDTH NON-JOINER) and A.2 (ZERO WIDTH
//!   JOINER): the ContextJ rules of validity criterion 8.
//! - RFC 5893 §1.4 (Bidi domain name, RTL label) and §2 (the six
//!   conditions of the Bidi rule): validity criterion 9.
//!
//! **Proof scope.** The executable code is proven to compute these
//! functions *relative to the Unicode tables* in [`super::data`]: the IDNA
//! Mapping Table, canonical decompositions and primary composites,
//! Canonical_Combining_Class, General_Category=Mark, Bidi_Class and
//! Joining_Type, all of Unicode 18.0.0. The tables are not proven to equal
//! the Unicode data files; `cargo xtask tables` generates them from the
//! vendored files (hashes in `data/unicode-18.0.0/SOURCE.md`), and `cargo
//! xtask check` fails if they differ. What the generator derives (full
//! decompositions, the primary composite pairs) is listed in the generated
//! file's header. Looking up a code point is the bisection in
//! [`super::tables`], which finds the row holding the code point because
//! the generator emits sorted, disjoint rows.
//!
//! Modelling choices (each one is a deliberate, reviewable deviation in form,
//! never in meaning):
//! - Strings are `Seq<u32>`, one element per code point. Every value is
//!   looked up in the tables as it is; a value above U+10FFFF (which only
//!   Punycode can produce) is in no row, so it has Status disallowed, class
//!   0, no Bidi_Class and no Joining_Type.
//! - Transitional_Processing and IgnoreInvalidPunycode are false: the only
//!   values the URL Standard passes (its "domain parser ToASCII" and
//!   "domain to Unicode"). The branches they guard are not transcribed:
//!   "deviation" maps to itself, U+1E9E's special case is not reached, and
//!   a Punycode failure always records an error. The other flags
//!   (UseSTD3ASCIIRules, CheckHyphens, CheckBidi, CheckJoiners,
//!   VerifyDnsLength) are parameters ([`Flags`]).
//! - "Record that there was an error" is a boolean returned with the
//!   string; the steps never stop early except where UTS #46 says
//!   "continue with the next label".
//! - Step 3 "Break" gives a sequence of labels; ToASCII step 5 and the
//!   end of processing join them with U+002E. Splitting and joining are
//!   inverse, so the string in between is never needed.
//! - Step 4 is done in two passes: first each label is converted
//!   ([`convert_label`]), then each converted label is checked against
//!   the validity criteria. Criterion 9 asks whether "the domain name is
//!   a Bidi domain name", which depends on every label after conversion,
//!   so the converted labels must all exist first. Errors are only ever
//!   recorded, never read, so the order in which they are recorded does
//!   not matter.
//! - "If the label starts with 'xn--'" compares code points exactly; by
//!   then step 1 has mapped uppercase ASCII to lowercase.
//! - Normalization Form C is `compose(canonical_order(decompose(s)))`
//!   (D120: "the result of applying the canonical decomposition followed
//!   by canonical composition"; canonical decomposition, D68, includes the
//!   canonical ordering of D109). Each of the three is a fold over the
//!   string from the left, in "done" and "rest" form: the code points
//!   processed so far, and the one being processed:
//!   - canonical ordering (D109: "exchange the positions of the characters
//!     in each Reorderable Pair until the sequence contains no more
//!     Reorderable Pairs") moves each code point left past the code points
//!     whose class is greater than its own non-zero class
//!     ([`insert_ordered`]). Each move exchanges a Reorderable Pair (D108),
//!     and when the fold is done none is left; every order of exchanges
//!     ends at the same sequence, the stable sort of each run of
//!     non-starters by class.
//!   - canonical composition (D117: "Starting from the second character in
//!     the coded character sequence ... and proceeding sequentially to the
//!     final character") handles C, the first code point not yet
//!     processed: R1 "seek back" searches the processed part, and R2
//!     replaces L there and drops C ([`compose_step`]). The part after C is
//!     untouched by R1 and R2, so processing C needs only the part before.
//! - "a Primary Composite P which is canonically equivalent to the
//!   sequence <L, C>" is: for Hangul, §3.12's LV and LVT composition; for
//!   every other P, the composition table row (L, C, P), listing each
//!   primary composite whose Decomposition_Mapping is exactly <L, C>.
//!   Every non-Hangul primary composite has a two-code-point mapping
//!   (singletons and non-starter decompositions are Full_Composition_
//!   Exclusions, D114 and UAX #44), and composition only ever meets L as a
//!   starter that is itself either undecomposable or such a composite.
//! - RFC 5892's "Before(cp)" is the code point before, if any; with none,
//!   the comparison is false. Its regular expression is matched around
//!   the ZWNJ: skipping Joining_Type T code points to the left, an L or D
//!   must come; skipping T to the right, an R or D.
//! - VerifyDnsLength: "The length of the domain name, excluding the root
//!   label and its dot, is from 1 to 253" and "The length of each label is
//!   from 1 to 63", where "the empty root label is disallowed" when the
//!   flag is true: every label, including an empty last one, must have
//!   length 1 to 63, and the joined string without a final U+002E must
//!   have length 1 to 253. Lengths are in code points, which after
//!   ToASCII step 3 are all ASCII, so they equal octet counts.
//! - URL "domain parser" steps 1 and 2 only report a validation error; the
//!   result does not depend on them, and validation errors are not
//!   modelled. Failure is `None`.

#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ===========================================================================
// Table lookups (UTS #46 §5 and the Unicode Character Database).
// ===========================================================================

/// UTS #46 §5: the row of the IDNA Mapping Table for `c`, if any.
pub open spec fn idna_row(c: u32) -> Option<super::tables::IdnaRow> {
    match super::tables::idna_find(c, 0, super::data::IDNA_MAPPING_LEN as int) {
        Some(i) => Some(super::data::idna_mapping_at(i)),
        None => None,
    }
}

/// `c`'s super::tables::Status; a value in no row is disallowed (see the modelling
/// choices).
pub open spec fn status(c: u32) -> super::tables::Status {
    match idna_row(c) {
        Some(row) => row.status,
        None => super::tables::Status::Disallowed,
    }
}

/// "the value for the mapping in Section 5, IDNA Mapping Table".
pub open spec fn mapping(row: super::tables::IdnaRow) -> Seq<u32> {
    super::tables::idna_mapping_data_slice(row.mapping_start as int, row.mapping_len as nat)
}

/// Canonical_Combining_Class of `c` (0 if it has no row).
pub open spec fn ccc(c: u32) -> u8 {
    match super::tables::combining_class_find(c, 0, super::data::COMBINING_CLASS_LEN as int) {
        Some(i) => super::data::combining_class_at(i).class,
        None => 0,
    }
}

/// General_Category=Mark (Mn, Mc or Me).
pub open spec fn is_mark(c: u32) -> bool {
    super::tables::mark_find(c, 0, super::data::MARK_LEN as int) is Some
}

/// Bidi_Class of `c` (`None` above U+10FFFF).
pub open spec fn bidi_class(c: u32) -> Option<super::tables::BidiClass> {
    match super::tables::bidi_class_find(c, 0, super::data::BIDI_CLASS_LEN as int) {
        Some(i) => Some(super::data::bidi_class_at(i).class),
        None => None,
    }
}

/// Joining_Type of `c`; `None` is U (Non_Joining).
pub open spec fn joining_type(c: u32) -> Option<super::tables::JoiningType> {
    match super::tables::joining_type_find(c, 0, super::data::JOINING_TYPE_LEN as int) {
        Some(i) => Some(super::data::joining_type_at(i).joining_type),
        None => None,
    }
}

// ===========================================================================
// The Unicode Standard §3.12: Hangul syllables.
// ===========================================================================

/// SBase
pub open spec fn s_base() -> u32 {
    0xAC00
}

/// LBase
pub open spec fn l_base() -> u32 {
    0x1100
}

/// VBase
pub open spec fn v_base() -> u32 {
    0x1161
}

/// TBase
pub open spec fn t_base() -> u32 {
    0x11A7
}

/// LCount = 19
pub open spec fn l_count() -> u32 {
    19
}

/// VCount = 21
pub open spec fn v_count() -> u32 {
    21
}

/// TCount = 28
pub open spec fn t_count() -> u32 {
    28
}

/// NCount = VCount * TCount = 588
pub open spec fn n_count() -> u32 {
    588
}

/// SCount = LCount * NCount = 11172
pub open spec fn s_count() -> u32 {
    11172
}

/// §3.12 "Hangul Syllable Decomposition": SIndex = s - SBase; LIndex =
/// SIndex / NCount; VIndex = (SIndex % NCount) / TCount; TIndex = SIndex %
/// TCount; LPart = LBase + LIndex; VPart = VBase + VIndex; TPart = TBase +
/// TIndex, "if TIndex is not 0".
pub open spec fn hangul_decomposition(s: u32) -> Seq<u32> {
    let s_index = s - s_base();
    let l_part = (l_base() + s_index / n_count() as int) as u32;
    let v_part = (v_base() + (s_index % n_count() as int) / t_count() as int) as u32;
    let t_index = s_index % t_count() as int;
    if t_index == 0 {
        seq![l_part, v_part]
    } else {
        seq![l_part, v_part, (t_base() + t_index) as u32]
    }
}

/// `c` is a precomposed Hangul syllable: SBase <= c < SBase + SCount.
pub open spec fn is_hangul_syllable(c: u32) -> bool {
    s_base() <= c < s_base() + s_count()
}

// ===========================================================================
// The Unicode Standard §3.11: Normalization Form C.
// ===========================================================================

/// D68: the full canonical decomposition of one code point. Hangul
/// syllables by §3.12; otherwise the decomposition table (which holds the
/// mappings already applied recursively), or the code point itself.
pub open spec fn full_decomposition(c: u32) -> Seq<u32> {
    if is_hangul_syllable(c) {
        hangul_decomposition(c)
    } else {
        match super::tables::decomposition_find(c, 0, super::data::DECOMPOSITION_LEN as int) {
            Some(i) => super::tables::decomposition_data_slice(
                super::data::decomposition_at(i).start as int,
                super::data::decomposition_at(i).len as nat,
            ),
            None => seq![c],
        }
    }
}

/// The full canonical decomposition of each code point of `s`, in order
/// (D68, before canonical ordering).
pub open spec fn decompose(s: Seq<u32>) -> Seq<u32>
    decreases s.len()
{
    if s.len() == 0 {
        seq![]
    } else {
        decompose(s.drop_last()) + full_decomposition(s.last())
    }
}

/// D109: put `c` after `done`, exchanging it with each code point before
/// it whose class is greater than its own non-zero class (D108: "A
/// Reorderable Pair ... ccc(A) > ccc(B) > 0").
pub open spec fn insert_ordered(done: Seq<u32>, c: u32) -> Seq<u32>
    decreases done.len()
{
    if ccc(c) == 0 || done.len() == 0 || ccc(done.last()) <= ccc(c) {
        done.push(c)
    } else {
        insert_ordered(done.drop_last(), c).push(done.last())
    }
}

/// D109, the Canonical Ordering Algorithm, applied to `s`.
pub open spec fn canonical_order(s: Seq<u32>) -> Seq<u32>
    decreases s.len()
{
    if s.len() == 0 {
        seq![]
    } else {
        insert_ordered(canonical_order(s.drop_last()), s.last())
    }
}

/// D117 R1: "Seek back (left) in the coded character sequence from the
/// character C to find the last Starter L preceding C": the position of
/// the last code point of `done` with class 0 (D107), if any.
pub open spec fn last_starter(done: Seq<u32>) -> Option<nat>
    decreases done.len()
{
    if done.len() == 0 {
        None
    } else if ccc(done.last()) == 0 {
        Some((done.len() - 1) as nat)
    } else {
        last_starter(done.drop_last())
    }
}

/// D115, from position `b` of `done` on: "there exists some character B
/// between A and C ... and either ccc(B) = 0 or ccc(B) >= ccc(C)".
pub open spec fn blocked_from(done: Seq<u32>, b: nat, c: u32) -> bool
    decreases done.len() - b
{
    if b >= done.len() {
        false
    } else {
        ccc(done[b as int]) == 0 || ccc(done[b as int]) >= ccc(c) || blocked_from(done, b + 1, c)
    }
}

/// §3.12 "Hangul Syllable Composition" and the composition table: the
/// Primary Composite canonically equivalent to `<l, c>`, if there is one.
pub open spec fn primary_composite(l: u32, c: u32) -> Option<u32> {
    if l_base() <= l < l_base() + l_count() && v_base() <= c < v_base() + v_count() {
        // <LPart, VPart>: LVIndex = LIndex * NCount + VIndex * TCount.
        Some((s_base() + (l - l_base()) * n_count() + (c - v_base()) * t_count()) as u32)
    } else if is_hangul_syllable(l) && (l - s_base()) % t_count() as int == 0 && t_base() < c < t_base()
        + t_count() {
        // <LVPart, TPart>: s = LVPart + TIndex.
        Some((l + (c - t_base())) as u32)
    } else {
        match super::tables::composition_find(l, c, 0, super::data::COMPOSITION_LEN as int) {
            Some(i) => Some(super::data::composition_at(i).composite),
            None => None,
        }
    }
}

/// D117 for C = `c`, with `done` the sequence before it (see the modelling
/// choices).
pub open spec fn compose_step(done: Seq<u32>, c: u32) -> Seq<u32> {
    match last_starter(done) {
        // R1 found L.
        Some(l) => {
            // R2 "If there is such an L, and C is not blocked from L, and
            // there exists a Primary Composite P which is canonically
            // equivalent to the sequence <L, C>, then replace L by P in the
            // sequence and delete C from the sequence."
            if !blocked_from(done, l + 1, c) {
                match primary_composite(done[l as int], c) {
                    Some(p) => done.update(l as int, p),
                    None => done.push(c),
                }
            } else {
                done.push(c)
            }
        },
        None => done.push(c),
    }
}

/// D117, the Canonical Composition Algorithm, applied to `s`: the first
/// character is kept, and each later one is processed in turn.
pub open spec fn compose(s: Seq<u32>) -> Seq<u32>
    decreases s.len()
{
    if s.len() <= 1 {
        s
    } else {
        compose_step(compose(s.drop_last()), s.last())
    }
}

/// Normalization Form C (D120).
pub open spec fn nfc(s: Seq<u32>) -> Seq<u32> {
    compose(canonical_order(decompose(s)))
}

// ===========================================================================
// UTS #46 §4 Processing.
// ===========================================================================

/// The input flags that may vary (see the modelling choices).
#[derive(Clone, Copy)]
pub struct Flags {
    /// UseSTD3ASCIIRules
    pub use_std3_ascii_rules: bool,
    /// CheckHyphens
    pub check_hyphens: bool,
    /// CheckBidi
    pub check_bidi: bool,
    /// CheckJoiners
    pub check_joiners: bool,
}

/// U+002E ( . ) FULL STOP
pub open spec fn full_stop() -> u32 {
    0x2E
}

/// U+002D HYPHEN-MINUS
pub open spec fn hyphen() -> u32 {
    0x2D
}

/// Step 1, Map, for one code point.
pub open spec fn map_code_point(c: u32) -> Seq<u32> {
    match idna_row(c) {
        Some(row) => match row.status {
            // "disallowed: Leave the code point unchanged in the string."
            super::tables::Status::Disallowed => seq![c],
            // "ignored: Remove the code point from the string."
            super::tables::Status::Ignored => seq![],
            // "mapped: ... Replace the code point in the string by the value
            // for the mapping"
            super::tables::Status::Mapped => mapping(row),
            // "deviation: ... Otherwise, leave the code point unchanged"
            super::tables::Status::Deviation => seq![c],
            // "valid: Leave the code point unchanged in the string."
            super::tables::Status::Valid => seq![c],
        },
        None => seq![c],
    }
}

/// Step 1, Map: "For each code point in the domain_name string, look up
/// the super::tables::Status value in Section 5, IDNA Mapping Table, and take the
/// following actions".
pub open spec fn map(s: Seq<u32>) -> Seq<u32>
    decreases s.len()
{
    if s.len() == 0 {
        seq![]
    } else {
        map(s.drop_last()) + map_code_point(s.last())
    }
}

/// Step 3, Break: "Break the string into labels at U+002E ( . ) FULL
/// STOP." There is always at least one label.
pub open spec fn break_labels(s: Seq<u32>) -> Seq<Seq<u32>>
    decreases s.len()
{
    if s.len() == 0 {
        seq![seq![]]
    } else {
        let labels = break_labels(s.drop_last());
        if s.last() == full_stop() {
            labels.push(seq![])
        } else {
            labels.update(labels.len() - 1, labels.last().push(s.last()))
        }
    }
}

/// Labels joined with U+002E FULL STOP.
pub open spec fn join_labels(labels: Seq<Seq<u32>>) -> Seq<u32>
    decreases labels.len()
{
    if labels.len() == 0 {
        seq![]
    } else if labels.len() == 1 {
        labels[0]
    } else {
        join_labels(labels.drop_last()).push(full_stop()) + labels.last()
    }
}

/// "starts with 'xn--'"
pub open spec fn starts_with_xn(label: Seq<u32>) -> bool {
    label.len() >= 4 && label[0] == 0x78 && label[1] == 0x6E && label[2] == 0x2D && label[3] == 0x2D
}

/// Whether `s` contains a code point greater than U+007F.
pub open spec fn contains_non_ascii(s: Seq<u32>) -> bool
    decreases s.len()
{
    if s.len() == 0 {
        false
    } else {
        s.last() > 0x7F || contains_non_ascii(s.drop_last())
    }
}

/// A label after step 4's conversion.
pub struct Converted {
    /// The label (decoded from Punycode, if that succeeded).
    pub label: Seq<u32>,
    /// Whether the conversion recorded an error.
    pub error: bool,
    /// Whether the label goes on to be checked against the validity
    /// criteria (false where UTS #46 says "continue with the next label").
    pub validate: bool,
}

/// Step 4, Convert/Validate, the conversion part, for one label.
pub open spec fn convert_label(label: Seq<u32>) -> Converted {
    if starts_with_xn(label) {
        // 4.1 "If the label starts with 'xn--':"
        if contains_non_ascii(label) {
            // 4.1.1 "If the label contains any non-ASCII code point (i.e., a
            // code point greater than U+007F), record that there was an
            // error, and continue with the next label."
            Converted { label, error: true, validate: false }
        } else {
            // 4.1.2 "Attempt to convert the rest of the label to Unicode
            // according to Punycode [RFC3492]. If that conversion fails and
            // if not IgnoreInvalidPunycode, record that there was an error,
            // and continue with the next label. Otherwise replace the
            // original label in the string by the results of the
            // conversion."
            match crate::punycode::spec::punycode_decode(label.subrange(4, label.len() as int)) {
                None => Converted { label, error: true, validate: false },
                Some(decoded) => {
                    // 4.1.3 "If the label is empty, or if the label contains
                    // only ASCII code points, record that there was an
                    // error."
                    // 4.1.4 "Verify that the label meets the validity
                    // criteria ... for Nontransitional Processing": in the
                    // second pass.
                    Converted { label: decoded, error: decoded.len() == 0 || !contains_non_ascii(decoded), validate: true }
                },
            }
        }
    } else {
        // 4.2 "If the label does not start with 'xn--': Verify that the
        // label meets the validity criteria": in the second pass.
        Converted { label, error: false, validate: true }
    }
}

/// Step 4's conversion for every label.
pub open spec fn convert_labels(labels: Seq<Seq<u32>>) -> Seq<Converted>
    decreases labels.len()
{
    if labels.len() == 0 {
        seq![]
    } else {
        convert_labels(labels.drop_last()).push(convert_label(labels.last()))
    }
}

// ---------------------------------------------------------------------------
// RFC 5893: the Bidi rule.
// ---------------------------------------------------------------------------

/// The Bidi class of `c` is one of R, AL or AN.
pub open spec fn is_r_al_an(c: u32) -> bool {
    match bidi_class(c) {
        Some(super::tables::BidiClass::RightToLeft) | Some(super::tables::BidiClass::ArabicLetter) | Some(super::tables::BidiClass::ArabicNumber) => true,
        _ => false,
    }
}

/// RFC 5893 §1.4: "An RTL label is a label that contains at least one
/// character of type R, AL, or AN."
pub open spec fn is_rtl_label(label: Seq<u32>) -> bool
    decreases label.len()
{
    if label.len() == 0 {
        false
    } else {
        is_r_al_an(label.last()) || is_rtl_label(label.drop_last())
    }
}

/// RFC 5893 §1.4: "A 'Bidi domain name' is a domain name containing at
/// least one character with the Bidi property R, AL, or AN", that is, at
/// least one RTL label; here over the converted labels.
pub open spec fn is_bidi_domain_name(labels: Seq<Converted>) -> bool
    decreases labels.len()
{
    if labels.len() == 0 {
        false
    } else {
        is_rtl_label(labels.last().label) || is_bidi_domain_name(labels.drop_last())
    }
}

/// Condition 2's list: "R, AL, AN, EN, ES, CS, ET, ON, BN, or NSM".
pub open spec fn rtl_allowed(class: Option<super::tables::BidiClass>) -> bool {
    match class {
        Some(super::tables::BidiClass::RightToLeft) | Some(super::tables::BidiClass::ArabicLetter) | Some(super::tables::BidiClass::ArabicNumber) | Some(
            super::tables::BidiClass::EuropeanNumber,
        ) | Some(super::tables::BidiClass::EuropeanSeparator) | Some(super::tables::BidiClass::CommonSeparator) | Some(
            super::tables::BidiClass::EuropeanTerminator,
        ) | Some(super::tables::BidiClass::OtherNeutral) | Some(super::tables::BidiClass::BoundaryNeutral) | Some(super::tables::BidiClass::NonspacingMark) => true,
        _ => false,
    }
}

/// Condition 5's list: "L, EN, ES, CS, ET, ON, BN, or NSM".
pub open spec fn ltr_allowed(class: Option<super::tables::BidiClass>) -> bool {
    match class {
        Some(super::tables::BidiClass::LeftToRight) | Some(super::tables::BidiClass::EuropeanNumber) | Some(super::tables::BidiClass::EuropeanSeparator) | Some(
            super::tables::BidiClass::CommonSeparator,
        ) | Some(super::tables::BidiClass::EuropeanTerminator) | Some(super::tables::BidiClass::OtherNeutral) | Some(super::tables::BidiClass::BoundaryNeutral)
        | Some(super::tables::BidiClass::NonspacingMark) => true,
        _ => false,
    }
}

/// Every code point of `label` has a class in `rtl_allowed` (if `rtl`) or
/// `ltr_allowed`.
pub open spec fn all_allowed(label: Seq<u32>, rtl: bool) -> bool
    decreases label.len()
{
    if label.len() == 0 {
        true
    } else {
        (if rtl {
            rtl_allowed(bidi_class(label.last()))
        } else {
            ltr_allowed(bidi_class(label.last()))
        }) && all_allowed(label.drop_last(), rtl)
    }
}

/// Conditions 3 and 6: after removing trailing NSM code points, the last
/// code point's class is one of R, AL, EN, AN (if `rtl`) or L, EN.
pub open spec fn ends_correctly(label: Seq<u32>, rtl: bool) -> bool
    decreases label.len()
{
    if label.len() == 0 {
        false
    } else {
        match bidi_class(label.last()) {
            Some(super::tables::BidiClass::NonspacingMark) => ends_correctly(label.drop_last(), rtl),
            Some(super::tables::BidiClass::RightToLeft) | Some(super::tables::BidiClass::ArabicLetter) | Some(super::tables::BidiClass::ArabicNumber) => rtl,
            Some(super::tables::BidiClass::EuropeanNumber) => true,
            Some(super::tables::BidiClass::LeftToRight) => !rtl,
            _ => false,
        }
    }
}

/// Whether some code point of `label` has Bidi class `class`.
pub open spec fn contains_class(label: Seq<u32>, class: super::tables::BidiClass) -> bool
    decreases label.len()
{
    if label.len() == 0 {
        false
    } else {
        bidi_class(label.last()) == Some(class) || contains_class(label.drop_last(), class)
    }
}

/// RFC 5893 §2, "the following six conditions", for a non-empty label.
pub open spec fn bidi_rule(label: Seq<u32>) -> bool {
    let first = bidi_class(label[0]);
    // 1. "The first character must be a character with Bidi property L, R,
    //    or AL. If it has the R or AL property, it is an RTL label; if it
    //    has the L property, it is an LTR label."
    if first == Some(super::tables::BidiClass::RightToLeft) || first == Some(super::tables::BidiClass::ArabicLetter) {
        // 2. "In an RTL label, only characters with the Bidi properties R,
        //    AL, AN, EN, ES, CS, ET, ON, BN, or NSM are allowed."
        all_allowed(label, true)
        // 3. "In an RTL label, the end of the label must be a character with
        //    Bidi property R, AL, EN, or AN, followed by zero or more
        //    characters with Bidi property NSM."
         && ends_correctly(label, true)
        // 4. "In an RTL label, if an EN is present, no AN may be present,
        //    and vice versa."
         && !(contains_class(label, super::tables::BidiClass::EuropeanNumber) && contains_class(label, super::tables::BidiClass::ArabicNumber))
    } else if first == Some(super::tables::BidiClass::LeftToRight) {
        // 5. "In an LTR label, only characters with the Bidi properties L,
        //    EN, ES, CS, ET, ON, BN, or NSM are allowed."
        all_allowed(label, false)
        // 6. "In an LTR label, the end of the label must be a character with
        //    Bidi property L or EN, followed by zero or more characters with
        //    Bidi property NSM."
         && ends_correctly(label, false)
    } else {
        false
    }
}

// ---------------------------------------------------------------------------
// RFC 5892 Appendix A.1 and A.2: the ContextJ rules.
// ---------------------------------------------------------------------------

/// "Canonical_Combining_Class(Before(cp)) .eq. Virama": the code point
/// before position `i` has class 9 (Virama).
pub open spec fn virama_before(label: Seq<u32>, i: int) -> bool {
    i > 0 && ccc(label[i - 1]) == 9
}

/// Left side of A.1's expression, from position `j` leftwards:
/// "(Joining_Type:{L,D})(Joining_Type:T)*".
pub open spec fn joins_left(label: Seq<u32>, j: int) -> bool
    decreases j + 1
{
    if j < 0 || j >= label.len() {
        false
    } else {
        match joining_type(label[j]) {
            Some(super::tables::JoiningType::Transparent) => joins_left(label, j - 1),
            Some(super::tables::JoiningType::LeftJoining) | Some(super::tables::JoiningType::DualJoining) => true,
            _ => false,
        }
    }
}

/// Right side of A.1's expression, from position `j` rightwards:
/// "(Joining_Type:T)*(Joining_Type:{R,D})".
pub open spec fn joins_right(label: Seq<u32>, j: int) -> bool
    decreases label.len() - j
{
    if j < 0 || j >= label.len() {
        false
    } else {
        match joining_type(label[j]) {
            Some(super::tables::JoiningType::Transparent) => joins_right(label, j + 1),
            Some(super::tables::JoiningType::RightJoining) | Some(super::tables::JoiningType::DualJoining) => true,
            _ => false,
        }
    }
}

/// The ContextJ rule for the code point at position `i`, true for code
/// points other than U+200C and U+200D.
pub open spec fn context_j_at(label: Seq<u32>, i: int) -> bool {
    if label[i] == 0x200C {
        // A.1 ZERO WIDTH NON-JOINER: "If Canonical_Combining_Class(Before(cp))
        // .eq. Virama Then True; If RegExpMatch((Joining_Type:{L,D})
        // (Joining_Type:T)*‌(Joining_Type:T)*(Joining_Type:{R,D})) Then
        // True;" and otherwise false.
        virama_before(label, i) || (joins_left(label, i - 1) && joins_right(label, i + 1))
    } else if label[i] == 0x200D {
        // A.2 ZERO WIDTH JOINER: "If Canonical_Combining_Class(Before(cp))
        // .eq. Virama Then True;" and otherwise false.
        virama_before(label, i)
    } else {
        true
    }
}

/// The ContextJ rules hold at every position from `i` on.
pub open spec fn context_j_from(label: Seq<u32>, i: nat) -> bool
    decreases label.len() - i
{
    if i >= label.len() {
        true
    } else {
        context_j_at(label, i as int) && context_j_from(label, i + 1)
    }
}

// ---------------------------------------------------------------------------
// §4.1 Validity Criteria.
// ---------------------------------------------------------------------------

/// Criterion 7 for one code point: "For Nontransitional Processing, each
/// value must be either valid or deviation. In addition, if
/// UseSTD3ASCIIRules=true and the code point is an ASCII code point
/// (U+0000..U+007F), then it must be a lowercase letter (a-z), a digit
/// (0-9), or a hyphen-minus (U+002D)."
pub open spec fn status_allowed(c: u32, flags: Flags) -> bool {
    (match status(c) {
        super::tables::Status::Valid | super::tables::Status::Deviation => true,
        _ => false,
    }) && (flags.use_std3_ascii_rules && c <= 0x7F ==> (0x61 <= c <= 0x7A || 0x30 <= c <= 0x39 || c
        == hyphen()))
}

/// Criteria 5 and 7 for every code point of `label`.
pub open spec fn code_points_allowed(label: Seq<u32>, flags: Flags) -> bool
    decreases label.len()
{
    if label.len() == 0 {
        true
    } else {
        // 5. "The label must not contain a U+002E ( . ) FULL STOP."
        label.last() != full_stop() && status_allowed(label.last(), flags) && code_points_allowed(
            label.drop_last(),
            flags,
        )
    }
}

/// §4.1: "Each of the following criteria must be satisfied for a non-empty
/// label", Nontransitional Processing, with `bidi_domain` saying whether the
/// domain name is a Bidi domain name.
pub open spec fn is_valid_label(label: Seq<u32>, flags: Flags, bidi_domain: bool) -> bool {
    label.len() == 0 || {
        // 1. "The label must be in Unicode Normalization Form NFC."
        &&& nfc(label) == label
        // 2. "If CheckHyphens, the label must not contain a U+002D
        //    HYPHEN-MINUS character in both the third and fourth positions."
        &&& flags.check_hyphens ==> !(label.len() >= 4 && label[2] == hyphen() && label[3] == hyphen())
        // 3. "If CheckHyphens, the label must neither begin nor end with a
        //    U+002D HYPHEN-MINUS character."
        &&& flags.check_hyphens ==> label[0] != hyphen() && label.last() != hyphen()
        // 4. "If not CheckHyphens, the label must not begin with 'xn--'."
        &&& !flags.check_hyphens ==> !starts_with_xn(label)
        // 5. (with 7) "The label must not contain a U+002E ( . ) FULL STOP."
        // 6. "The label must not begin with a combining mark, that is:
        //    General_Category=Mark."
        &&& !is_mark(label[0])
        // 7. "Each code point in the label must only have certain super::tables::Status
        //    values"
        &&& code_points_allowed(label, flags)
        // 8. "If CheckJoiners, the label must satisify the ContextJ rules
        //    from Appendix A, in The Unicode Code Points and
        //    Internationalized Domain Names for Applications (IDNA)."
        &&& flags.check_joiners ==> context_j_from(label, 0)
        // 9. "If CheckBidi, and if the domain name is a Bidi domain name,
        //    then the label must satisfy all six of the numbered conditions
        //    in [IDNA2008] RFC 5893, Section 2."
        &&& flags.check_bidi && bidi_domain ==> bidi_rule(label)
    }
}

/// Whether step 4 recorded an error for any of `labels`.
pub open spec fn any_error(labels: Seq<Converted>, flags: Flags, bidi_domain: bool) -> bool
    decreases labels.len()
{
    if labels.len() == 0 {
        false
    } else {
        let l = labels.last();
        l.error || (l.validate && !is_valid_label(l.label, flags, bidi_domain)) || any_error(
            labels.drop_last(),
            flags,
            bidi_domain,
        )
    }
}

/// The labels' strings.
pub open spec fn converted_labels(labels: Seq<Converted>) -> Seq<Seq<u32>>
    decreases labels.len()
{
    if labels.len() == 0 {
        seq![]
    } else {
        converted_labels(labels.drop_last()).push(labels.last().label)
    }
}

/// The result of processing: the labels and whether an error was recorded.
pub struct Processed {
    /// The labels, after step 4's conversion.
    pub labels: Seq<Seq<u32>>,
    /// Whether an error was recorded.
    pub error: bool,
}

/// UTS #46 §4 Processing (Nontransitional; IgnoreInvalidPunycode false).
pub open spec fn process(domain_name: Seq<u32>, flags: Flags) -> Processed {
    // 1. Map.
    let mapped = map(domain_name);
    // 2. Normalize: "Normalize the domain_name string to Unicode
    //    Normalization Form C."
    let normalized = nfc(mapped);
    // 3. Break.
    let labels = break_labels(normalized);
    // 4. Convert/Validate.
    let converted = convert_labels(labels);
    let bidi_domain = is_bidi_domain_name(converted);
    Processed { labels: converted_labels(converted), error: any_error(converted, flags, bidi_domain) }
}

// ---------------------------------------------------------------------------
// §4.2 ToASCII and §4.3 ToUnicode.
// ---------------------------------------------------------------------------

/// ToASCII step 3 for one label: "Convert each label with non-ASCII
/// characters into Punycode [RFC3492], and prefix by 'xn--'. This may
/// record an error." `None` records the error.
pub open spec fn to_ascii_label(label: Seq<u32>) -> Option<Seq<u32>> {
    if contains_non_ascii(label) {
        match crate::punycode::spec::punycode_encode(label) {
            Some(encoded) => Some(seq![0x78u32, 0x6E, 0x2D, 0x2D] + encoded),
            None => None,
        }
    } else {
        Some(label)
    }
}

/// ToASCII step 3 for every label; `None` if any records an error.
pub open spec fn to_ascii_labels(labels: Seq<Seq<u32>>) -> Option<Seq<Seq<u32>>>
    decreases labels.len()
{
    if labels.len() == 0 {
        Some(seq![])
    } else {
        match (to_ascii_labels(labels.drop_last()), to_ascii_label(labels.last())) {
            (Some(done), Some(label)) => Some(done.push(label)),
            _ => None,
        }
    }
}

/// Every label has length 1 to 63.
pub open spec fn label_lengths_ok(labels: Seq<Seq<u32>>) -> bool
    decreases labels.len()
{
    if labels.len() == 0 {
        true
    } else {
        1 <= labels.last().len() <= 63 && label_lengths_ok(labels.drop_last())
    }
}

/// ToASCII step 4, VerifyDnsLength (see the modelling choices).
pub open spec fn dns_length_ok(labels: Seq<Seq<u32>>) -> bool {
    let joined = join_labels(labels);
    let length = if joined.len() > 0 && joined.last() == full_stop() {
        joined.len() - 1
    } else {
        joined.len() as int
    };
    label_lengths_ok(labels) && 1 <= length <= 253
}

/// UTS #46 §4.2 ToASCII, with VerifyDnsLength `verify_dns_length`. `None`
/// is "a failure value".
pub open spec fn to_ascii(domain_name: Seq<u32>, flags: Flags, verify_dns_length: bool) -> Option<Seq<u32>> {
    // 1. "To the input domain_name, apply the Processing Steps in Section
    //    4, Processing ... This may record an error."
    let processed = process(domain_name, flags);
    // 2. "Break the result into labels at U+002E FULL STOP": the labels of
    //    step 1 (see the modelling choices).
    // 3. Convert to Punycode.
    match to_ascii_labels(processed.labels) {
        None => None,
        Some(labels) => {
            if processed.error {
                // 5. "If an error was recorded in steps 1-4, then the
                //    operation has failed and a failure value is returned."
                None
            } else if verify_dns_length && !dns_length_ok(labels) {
                // 4. "If the VerifyDnsLength flag is true, then verify DNS
                //    length restrictions. This may record an error."
                None
            } else {
                // 6. "Otherwise join the labels using U+002E FULL STOP as a
                //    separator, and return the result."
                Some(join_labels(labels))
            }
        },
    }
}

/// UTS #46 §4.3 ToUnicode: the converted string, and whether an error was
/// recorded ("this always signals whether or not there was an error").
pub open spec fn to_unicode(domain_name: Seq<u32>, flags: Flags) -> (Seq<u32>, bool) {
    // "To the input domain_name, apply the Processing Steps in Section 4"
    let processed = process(domain_name, flags);
    (join_labels(processed.labels), processed.error)
}

// ===========================================================================
// URL Standard §3.3 IDNA.
// ===========================================================================

/// URL §3.2: "A forbidden host code point is U+0000 NULL, U+0009 TAB,
/// U+000A LF, U+000D CR, U+0020 SPACE, U+0023 (#), U+002F (/), U+003A (:),
/// U+003C (<), U+003E (>), U+003F (?), U+0040 (@), U+005B ([), U+005C (\),
/// U+005D (]), U+005E (^), or U+007C (|)."
pub open spec fn is_forbidden_host_code_point(c: u32) -> bool {
    c == 0x00 || c == 0x09 || c == 0x0A || c == 0x0D || c == 0x20 || c == 0x23 || c == 0x2F || c == 0x3A
        || c == 0x3C || c == 0x3E || c == 0x3F || c == 0x40 || c == 0x5B || c == 0x5C || c == 0x5D || c
        == 0x5E || c == 0x7C
}

/// URL §3.2: "A forbidden domain code point is a forbidden host code point,
/// a C0 control, U+0025 (%), or U+007F DELETE." (Infra: "A C0 control is a
/// code point in the range U+0000 NULL to U+001F INFORMATION SEPARATOR ONE,
/// inclusive.")
pub open spec fn is_forbidden_domain_code_point(c: u32) -> bool {
    is_forbidden_host_code_point(c) || c <= 0x1F || c == 0x25 || c == 0x7F
}

/// Whether `s` contains a forbidden domain code point.
pub open spec fn contains_forbidden_domain_code_point(s: Seq<u32>) -> bool
    decreases s.len()
{
    if s.len() == 0 {
        false
    } else {
        is_forbidden_domain_code_point(s.last()) || contains_forbidden_domain_code_point(s.drop_last())
    }
}

/// Infra "ASCII lowercase": each ASCII upper alpha replaced by its ASCII
/// lower alpha.
pub open spec fn ascii_lowercase(s: Seq<u32>) -> Seq<u32>
    decreases s.len()
{
    if s.len() == 0 {
        seq![]
    } else {
        let c = s.last();
        ascii_lowercase(s.drop_last()).push(
            if 0x41 <= c <= 0x5A {
                (c + 0x20) as u32
            } else {
                c
            },
        )
    }
}

/// The flags "domain parser ToASCII" passes for `be_strict`.
pub open spec fn url_flags(be_strict: bool) -> Flags {
    Flags { use_std3_ascii_rules: be_strict, check_hyphens: be_strict, check_bidi: true, check_joiners: true }
}

/// URL §3.3 "domain parser ToASCII": "the result of running Unicode ToASCII
/// with domain_name set to domain, CheckHyphens set to beStrict, CheckBidi
/// set to true, CheckJoiners set to true, UseSTD3ASCIIRules set to
/// beStrict, Transitional_Processing set to false, VerifyDnsLength set to
/// beStrict, and IgnoreInvalidPunycode set to false."
pub open spec fn domain_parser_to_ascii(domain: Seq<u32>, be_strict: bool) -> Option<Seq<u32>> {
    to_ascii(domain, url_flags(be_strict), be_strict)
}

/// URL §3.3 "domain parser", given `domain` and `be_strict`. `None` is
/// failure.
pub open spec fn domain_parser(domain: Seq<u32>, be_strict: bool) -> Option<Seq<u32>> {
    // 1. "Let strictResult be the result of running domain parser ToASCII
    //    with domain and true."
    // 2. A validation error only (see the modelling choices).
    if be_strict {
        // 3. "If beStrict is true: If strictResult is a failure value, then
        //    return failure. Return strictResult."
        domain_parser_to_ascii(domain, true)
    } else {
        // 4. "Let result be null."
        // 5. "If domain is an ASCII string, then set result to domain,
        //    lowercased."
        // 6. "Otherwise: Set result to the result of running domain parser
        //    ToASCII with domain and false. If result is a failure value,
        //    then return failure."
        let result = if !contains_non_ascii(domain) {
            Some(ascii_lowercase(domain))
        } else {
            domain_parser_to_ascii(domain, false)
        };
        match result {
            None => None,
            Some(result) => {
                if result.len() == 0 {
                    // 7. "If result is the empty string, then return failure."
                    None
                } else if contains_forbidden_domain_code_point(result) {
                    // 8. "If result contains a forbidden domain code point,
                    //    then return failure."
                    None
                } else {
                    // 9. "Return result."
                    Some(result)
                }
            },
        }
    }
}

/// URL §3.3 "domain to Unicode", given a domain.
pub open spec fn domain_to_unicode(domain: Seq<u32>) -> Seq<u32> {
    // 1. "Let result be the result of running Unicode ToUnicode with
    //    domain_name set to domain, CheckHyphens set to false, CheckBidi set
    //    to true, CheckJoiners set to true, UseSTD3ASCIIRules set to false,
    //    Transitional_Processing set to false, and IgnoreInvalidPunycode set
    //    to false."
    let (result, error) = to_unicode(domain, url_flags(false));
    if error {
        // 2. "If an error was recorded, then return domain."
        domain
    } else {
        // 3. "Return result."
        result
    }
}

} // verus!
