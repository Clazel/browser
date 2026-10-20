//! Facts proven about the sniffing spec in [`super::spec`]. They are
//! evidence that the transcription behaves as the standard says, and the
//! theorems the mutation certificates in `mutations.json` contradict.
//!
//! Main results:
//! - [`lemma_pattern_matching_in_bounds`]: the pattern matching algorithm
//!   (§6) is true exactly when, after the ignored leading bytes, the input
//!   still holds the whole pattern and every byte of it matches under the
//!   mask. So it never looks past the end of the input, which the
//!   algorithm as written does (the §6 erratum in `docs/ERRATA.md`).
//! - [`lemma_pattern_matching_extends`]: a non-empty pattern that matches a
//!   resource header still matches when more bytes are appended, so
//!   reading more of a resource (§5.2) never undoes a table match.
//! - [`lemma_tables_well_formed`]: every row of every table meets §6's
//!   assertion (step 1), so the algorithm is always called as specified.
//! - [`lemma_no_scriptable_without_flag`]: with the sniff-scriptable flag
//!   unset, the rules for identifying an unknown MIME type (§7.1) never
//!   return a scriptable MIME type (§4.6); §7.1 step 1 is the only step
//!   that may. And [`lemma_no_sniff_never_scriptable_unless_supplied`]:
//!   with the no-sniff flag set, §7 returns either the supplied MIME type
//!   or a type that is not scriptable.
//! - [`lemma_apache_bug_text_or_binary`]: when the check-for-apache-bug
//!   flag decides (§7 step 4), the computed MIME type is "text/plain" or
//!   "application/octet-stream" (§7.2 has no other outcome), so a
//!   resource served as text/plain is never sniffed into a scriptable type.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ===========================================================================
// §6 pattern matching.
// ===========================================================================

/// What skipping the ignored bytes from `s` gives: the first byte at or
/// after `s` that is not ignored (or the end).
pub proof fn lemma_skip_ignored(input: Seq<u8>, s: nat, ignored: Ignored)
    requires
        s <= input.len(),
    ensures
        s <= skip_ignored(input, s, ignored) <= input.len(),
        forall|k: int| s <= k < skip_ignored(input, s, ignored) ==> ignored_contains(ignored, #[trigger] input[k]),
        skip_ignored(input, s, ignored) < input.len() ==> !ignored_contains(ignored, input[skip_ignored(input, s, ignored) as int]),
    decreases input.len() - s,
{
    if s < input.len() && ignored_contains(ignored, input[s as int]) {
        lemma_skip_ignored(input, s + 1, ignored);
    }
}

/// Step 6 of the pattern matching algorithm, in closed form.
pub proof fn lemma_compare_pattern(input: Seq<u8>, pattern: Seq<u8>, mask: Seq<u8>, s: nat, p: nat)
    requires
        pattern.len() == mask.len(),
        p <= pattern.len(),
        s <= input.len(),
    ensures
        compare_pattern(input, pattern, mask, s, p) == (s + (pattern.len() - p) <= input.len()
            && forall|k: int| p <= k < pattern.len() ==> (#[trigger] input[s + k - p] & mask[k]) == pattern[k]),
    decreases pattern.len() - p,
{
    if p < pattern.len() {
        let rhs = s + (pattern.len() - p) <= input.len()
            && forall|k: int| p <= k < pattern.len() ==> (#[trigger] input[s + k - p] & mask[k]) == pattern[k];
        if s >= input.len() {
            assert(!rhs);
        } else if (input[s as int] & mask[p as int]) != pattern[p as int] {
            assert(input[s + p - p] == input[s as int]);
            assert(!rhs);
        } else {
            lemma_compare_pattern(input, pattern, mask, s + 1, p + 1);
            let next = forall|k: int| p + 1 <= k < pattern.len() ==> (#[trigger] input[(s + 1) + k - (p + 1)] & mask[k]) == pattern[k];
            if next {
                assert forall|k: int| p <= k < pattern.len() implies (#[trigger] input[s + k - p] & mask[k]) == pattern[k] by {
                    if k > p {
                        assert(input[s + k - p] == input[(s + 1) + k - (p + 1)]);
                    }
                }
            }
            if rhs {
                assert forall|k: int| p + 1 <= k < pattern.len() implies (#[trigger] input[(s + 1) + k - (p + 1)] & mask[k]) == pattern[k] by {
                    assert(input[s + k - p] == input[(s + 1) + k - (p + 1)]);
                }
            }
        }
    }
}

/// The pattern matching algorithm (§6) is true exactly when, after the
/// ignored bytes, the input holds the whole pattern and each byte matches
/// under the mask. Every byte it depends on is inside the input.
pub proof fn lemma_pattern_matching_in_bounds(input: Seq<u8>, pattern: Seq<u8>, mask: Seq<u8>, ignored: Ignored)
    requires
        pattern.len() == mask.len(),
    ensures
        ({
            let s = skip_ignored(input, 0, ignored);
            pattern_matching(input, pattern, mask, ignored) == (s + pattern.len() <= input.len()
                && forall|k: int| 0 <= k < pattern.len() ==> (#[trigger] input[s + k] & mask[k]) == pattern[k])
        }),
{
    let s = skip_ignored(input, 0, ignored);
    lemma_skip_ignored(input, 0, ignored);
    lemma_compare_pattern(input, pattern, mask, s, 0);
    assert forall|k: int| 0 <= k < pattern.len() implies (#[trigger] input[s + k] & mask[k]) == (input[s + k - 0] & mask[k]) by {}
}

/// A non-empty pattern that matches `input` still matches `input + more`.
pub proof fn lemma_pattern_matching_extends(input: Seq<u8>, more: Seq<u8>, pattern: Seq<u8>, mask: Seq<u8>, ignored: Ignored)
    requires
        pattern.len() == mask.len(),
        pattern.len() > 0,
        pattern_matching(input, pattern, mask, ignored),
    ensures
        pattern_matching(input + more, pattern, mask, ignored),
{
    let longer = input + more;
    lemma_pattern_matching_in_bounds(input, pattern, mask, ignored);
    lemma_pattern_matching_in_bounds(longer, pattern, mask, ignored);
    let s = skip_ignored(input, 0, ignored);
    lemma_skip_ignored_prefix(input, more, 0, ignored);
    assert forall|k: int| 0 <= k < pattern.len() implies (#[trigger] longer[s + k] & mask[k]) == pattern[k] by {
        assert(longer[s + k] == input[s + k]);
        assert((input[s + k] & mask[k]) == pattern[k]);
    }
}

/// Skipping ignored bytes in `input + more` stops where it stops in
/// `input`, if that is before the end of `input`.
proof fn lemma_skip_ignored_prefix(input: Seq<u8>, more: Seq<u8>, s: nat, ignored: Ignored)
    requires
        s <= input.len(),
    ensures
        skip_ignored(input, s, ignored) < input.len() ==> skip_ignored(input + more, s, ignored) == skip_ignored(input, s, ignored),
    decreases input.len() - s,
{
    let longer = input + more;
    if s < input.len() {
        assert(longer[s as int] == input[s as int]);
        if ignored_contains(ignored, input[s as int]) {
            lemma_skip_ignored_prefix(input, more, s + 1, ignored);
        }
    }
}

// ===========================================================================
// The tables meet §6 step 1.
// ===========================================================================

/// Every row of `table` from `i` on has a pattern as long as its mask.
pub open spec fn rows_well_formed(table: Seq<Row>, i: nat) -> bool
    decreases table.len() - i
{
    i >= table.len() || (table[i as int].pattern.len() == table[i as int].mask.len() && rows_well_formed(table, i + 1))
}

/// [`rows_well_formed`] as a quantifier.
pub proof fn lemma_rows_well_formed(table: Seq<Row>, i: nat)
    requires
        rows_well_formed(table, i),
    ensures
        forall|j: int| i <= j < table.len() ==> (#[trigger] table[j]).pattern.len() == table[j].mask.len(),
    decreases table.len() - i,
{
    if i < table.len() {
        lemma_rows_well_formed(table, i + 1);
    }
}

/// "Assert: pattern's length is equal to mask's length." (§6 step 1) holds
/// for every row of every table.
pub proof fn lemma_tables_well_formed()
    ensures
        forall|j: int| 0 <= j < image_type_table().len() ==> (#[trigger] image_type_table()[j]).pattern.len() == image_type_table()[j].mask.len(),
        forall|j: int| 0 <= j < audio_or_video_type_table().len() ==> (#[trigger] audio_or_video_type_table()[j]).pattern.len() == audio_or_video_type_table()[j].mask.len(),
        forall|j: int| 0 <= j < font_type_table().len() ==> (#[trigger] font_type_table()[j]).pattern.len() == font_type_table()[j].mask.len(),
        forall|j: int| 0 <= j < archive_type_table().len() ==> (#[trigger] archive_type_table()[j]).pattern.len() == archive_type_table()[j].mask.len(),
        forall|j: int| 0 <= j < unknown_scriptable_table().len() ==> (#[trigger] unknown_scriptable_table()[j]).pattern.len() == unknown_scriptable_table()[j].mask.len(),
        forall|j: int| 0 <= j < unknown_non_scriptable_table().len() ==> (#[trigger] unknown_non_scriptable_table()[j]).pattern.len() == unknown_non_scriptable_table()[j].mask.len(),
{
    assert(rows_well_formed(image_type_table(), 0)) by (compute_only);
    assert(rows_well_formed(audio_or_video_type_table(), 0)) by (compute_only);
    assert(rows_well_formed(font_type_table(), 0)) by (compute_only);
    assert(rows_well_formed(archive_type_table(), 0)) by (compute_only);
    assert(rows_well_formed(unknown_scriptable_table(), 0)) by (compute_only);
    assert(rows_well_formed(unknown_non_scriptable_table(), 0)) by (compute_only);
    lemma_rows_well_formed(image_type_table(), 0);
    lemma_rows_well_formed(audio_or_video_type_table(), 0);
    lemma_rows_well_formed(font_type_table(), 0);
    lemma_rows_well_formed(archive_type_table(), 0);
    lemma_rows_well_formed(unknown_scriptable_table(), 0);
    lemma_rows_well_formed(unknown_non_scriptable_table(), 0);
}

// ===========================================================================
// What §7.1 and §7 may return.
// ===========================================================================

/// No row of `table` from `i` on gives a scriptable MIME type.
pub open spec fn outputs_not_scriptable(table: Seq<Row>, i: nat) -> bool
    decreases table.len() - i
{
    i >= table.len() || (!crate::mime_type::spec::is_scriptable_mime_type(table[i as int].computed) && outputs_not_scriptable(table, i + 1))
}

/// A table whose rows give no scriptable MIME type returns none.
pub proof fn lemma_match_table_not_scriptable(input: Seq<u8>, table: Seq<Row>, i: nat)
    requires
        outputs_not_scriptable(table, i),
    ensures
        match_table(input, table, i) matches Some(t) ==> !crate::mime_type::spec::is_scriptable_mime_type(t),
    decreases table.len() - i,
{
    if i < table.len() && !pattern_matching(input, table[i as int].pattern, table[i as int].mask, table[i as int].ignored) {
        lemma_match_table_not_scriptable(input, table, i + 1);
    }
}

/// "text/plain".
pub open spec fn text_plain() -> crate::mime_type::spec::MimeTypeRecord {
    mime_type(seq![0x74u32, 0x65, 0x78, 0x74], seq![0x70u32, 0x6C, 0x61, 0x69, 0x6E])
}

/// "application/octet-stream".
pub open spec fn application_octet_stream() -> crate::mime_type::spec::MimeTypeRecord {
    mime_type(seq![0x61u32, 0x70, 0x70, 0x6C, 0x69, 0x63, 0x61, 0x74, 0x69, 0x6F, 0x6E],
        seq![0x6Fu32, 0x63, 0x74, 0x65, 0x74, 0x2D, 0x73, 0x74, 0x72, 0x65, 0x61, 0x6D])
}

/// Neither "text/plain" nor "application/octet-stream" is scriptable, and
/// they differ.
pub proof fn lemma_text_or_binary_not_scriptable()
    ensures
        !crate::mime_type::spec::is_scriptable_mime_type(text_plain()),
        !crate::mime_type::spec::is_scriptable_mime_type(application_octet_stream()),
{
    assert(!crate::mime_type::spec::is_scriptable_mime_type(text_plain())) by (compute_only);
    assert(!crate::mime_type::spec::is_scriptable_mime_type(application_octet_stream())) by (compute_only);
}

/// The audio or video type pattern matching algorithm (§6.2) never returns
/// a scriptable MIME type.
pub proof fn lemma_audio_or_video_not_scriptable(input: Seq<u8>)
    ensures
        audio_or_video_type_pattern_matching(input) matches Some(t) ==> !crate::mime_type::spec::is_scriptable_mime_type(t),
{
    assert(outputs_not_scriptable(audio_or_video_type_table(), 0)) by (compute_only);
    lemma_match_table_not_scriptable(input, audio_or_video_type_table(), 0);
    assert(!crate::mime_type::spec::is_scriptable_mime_type(mime_type(seq![0x76u32, 0x69, 0x64, 0x65, 0x6F], seq![0x6Du32, 0x70, 0x34]))) by (compute_only);
    assert(!crate::mime_type::spec::is_scriptable_mime_type(mime_type(seq![0x76u32, 0x69, 0x64, 0x65, 0x6F], seq![0x77u32, 0x65, 0x62, 0x6D]))) by (compute_only);
    assert(!crate::mime_type::spec::is_scriptable_mime_type(mime_type(seq![0x61u32, 0x75, 0x64, 0x69, 0x6F], seq![0x6Du32, 0x70, 0x65, 0x67]))) by (compute_only);
}

/// With the sniff-scriptable flag unset, the rules for identifying an
/// unknown MIME type (§7.1) never return a scriptable MIME type.
pub proof fn lemma_no_scriptable_without_flag(header: Seq<u8>)
    ensures
        !crate::mime_type::spec::is_scriptable_mime_type(identify_unknown_mime_type(header, false)),
{
    assert(outputs_not_scriptable(unknown_non_scriptable_table(), 0)) by (compute_only);
    assert(outputs_not_scriptable(image_type_table(), 0)) by (compute_only);
    assert(outputs_not_scriptable(archive_type_table(), 0)) by (compute_only);
    lemma_match_table_not_scriptable(header, unknown_non_scriptable_table(), 0);
    lemma_match_table_not_scriptable(header, image_type_table(), 0);
    lemma_match_table_not_scriptable(header, archive_type_table(), 0);
    lemma_audio_or_video_not_scriptable(header);
    lemma_text_or_binary_not_scriptable();
}

/// The rules for distinguishing if a resource is text or binary (§7.2)
/// give "text/plain" or "application/octet-stream".
pub proof fn lemma_distinguish_text_or_binary(header: Seq<u8>)
    ensures
        distinguish_text_or_binary(header) == text_plain() || distinguish_text_or_binary(header) == application_octet_stream(),
        !crate::mime_type::spec::is_scriptable_mime_type(distinguish_text_or_binary(header)),
{
    lemma_text_or_binary_not_scriptable();
}

/// When the check-for-apache-bug flag is set for a supplied MIME type that
/// is not scriptable and not unknown, and the no-sniff flag is not set,
/// the computed MIME type (§7) is "text/plain" or
/// "application/octet-stream": never a scriptable MIME type.
pub proof fn lemma_apache_bug_text_or_binary(resource: Resource, supported: bool)
    ensures
        resource.check_for_apache_bug && !resource.no_sniff && resource.supplied is Some
            && !crate::mime_type::spec::is_scriptable_mime_type(resource.supplied->Some_0)
            && !is_unknown_essence(resource.supplied->Some_0) ==> {
            let t = computed_mime_type(resource, supported);
            (t == text_plain() || t == application_octet_stream()) && !crate::mime_type::spec::is_scriptable_mime_type(t)
        },
{
    lemma_distinguish_text_or_binary(resource.header);
}

/// With the no-sniff flag set, the computed MIME type (§7) is the supplied
/// MIME type or not scriptable.
pub proof fn lemma_no_sniff_never_scriptable_unless_supplied(resource: Resource, supported: bool)
    ensures
        resource.no_sniff ==> (resource.supplied == Some(computed_mime_type(resource, supported))
            || !crate::mime_type::spec::is_scriptable_mime_type(computed_mime_type(resource, supported))),
{
    lemma_no_scriptable_without_flag(resource.header);
}

} // verus!
