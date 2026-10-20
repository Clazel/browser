//! Facts about the concrete tables, established by evaluating them
//! (`compute_only`): each table meets §6 step 1, gives no scriptable MIME
//! type where §7.1 needs that, and equals the rows `independent.rs` derives
//! from the notes.
//!
//! Kept out of `lemmas.rs` and `independent.rs`, which hold the mutation
//! certificates: a certificate is checked with its module's other
//! evaluations, and a mutant table would fail these.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The evaluated facts.
pub proof fn lemma_tables_evaluated()
    ensures
        super::lemmas::rows_well_formed(image_type_table(), 0),
        super::lemmas::rows_well_formed(audio_or_video_type_table(), 0),
        super::lemmas::rows_well_formed(font_type_table(), 0),
        super::lemmas::rows_well_formed(archive_type_table(), 0),
        super::lemmas::rows_well_formed(unknown_scriptable_table(), 0),
        super::lemmas::rows_well_formed(unknown_non_scriptable_table(), 0),
        !crate::mime_type::spec::is_scriptable_mime_type(super::lemmas::text_plain()),
        !crate::mime_type::spec::is_scriptable_mime_type(super::lemmas::application_octet_stream()),
        super::lemmas::outputs_not_scriptable(audio_or_video_type_table(), 0),
        !crate::mime_type::spec::is_scriptable_mime_type(mime_type(seq![0x76u32, 0x69, 0x64, 0x65, 0x6F], seq![0x6Du32, 0x70, 0x34])),
        !crate::mime_type::spec::is_scriptable_mime_type(mime_type(seq![0x76u32, 0x69, 0x64, 0x65, 0x6F], seq![0x77u32, 0x65, 0x62, 0x6D])),
        !crate::mime_type::spec::is_scriptable_mime_type(mime_type(seq![0x61u32, 0x75, 0x64, 0x69, 0x6F], seq![0x6Du32, 0x70, 0x65, 0x67])),
        super::lemmas::outputs_not_scriptable(unknown_non_scriptable_table(), 0),
        super::lemmas::outputs_not_scriptable(image_type_table(), 0),
        super::lemmas::outputs_not_scriptable(archive_type_table(), 0),
        super::independent::rows_equal(image_type_table(), super::independent::expand(super::independent::image_entries(), 0), 0),
        super::independent::rows_equal(font_type_table(), super::independent::expand(super::independent::font_entries(), 0), 0),
        super::independent::rows_equal(archive_type_table(), super::independent::expand(super::independent::archive_entries(), 0), 0),
        super::independent::rows_equal(unknown_scriptable_table(), super::independent::expand(super::independent::scriptable_entries(), 0), 0),
        super::independent::rows_equal(unknown_non_scriptable_table(), super::independent::expand(super::independent::non_scriptable_entries(), 0), 0),
        super::independent::rows_equal(audio_or_video_type_table(), super::independent::expand(super::independent::audio_or_video_entries(), 0), 0),
{
    assert(super::lemmas::rows_well_formed(image_type_table(), 0)) by (compute_only);
    assert(super::lemmas::rows_well_formed(audio_or_video_type_table(), 0)) by (compute_only);
    assert(super::lemmas::rows_well_formed(font_type_table(), 0)) by (compute_only);
    assert(super::lemmas::rows_well_formed(archive_type_table(), 0)) by (compute_only);
    assert(super::lemmas::rows_well_formed(unknown_scriptable_table(), 0)) by (compute_only);
    assert(super::lemmas::rows_well_formed(unknown_non_scriptable_table(), 0)) by (compute_only);
    assert(!crate::mime_type::spec::is_scriptable_mime_type(super::lemmas::text_plain())) by (compute_only);
    assert(!crate::mime_type::spec::is_scriptable_mime_type(super::lemmas::application_octet_stream())) by (compute_only);
    assert(super::lemmas::outputs_not_scriptable(audio_or_video_type_table(), 0)) by (compute_only);
    assert(!crate::mime_type::spec::is_scriptable_mime_type(mime_type(seq![0x76u32, 0x69, 0x64, 0x65, 0x6F], seq![0x6Du32, 0x70, 0x34]))) by (compute_only);
    assert(!crate::mime_type::spec::is_scriptable_mime_type(mime_type(seq![0x76u32, 0x69, 0x64, 0x65, 0x6F], seq![0x77u32, 0x65, 0x62, 0x6D]))) by (compute_only);
    assert(!crate::mime_type::spec::is_scriptable_mime_type(mime_type(seq![0x61u32, 0x75, 0x64, 0x69, 0x6F], seq![0x6Du32, 0x70, 0x65, 0x67]))) by (compute_only);
    assert(super::lemmas::outputs_not_scriptable(unknown_non_scriptable_table(), 0)) by (compute_only);
    assert(super::lemmas::outputs_not_scriptable(image_type_table(), 0)) by (compute_only);
    assert(super::lemmas::outputs_not_scriptable(archive_type_table(), 0)) by (compute_only);
    assert(super::independent::rows_equal(image_type_table(), super::independent::expand(super::independent::image_entries(), 0), 0)) by (compute_only);
    assert(super::independent::rows_equal(font_type_table(), super::independent::expand(super::independent::font_entries(), 0), 0)) by (compute_only);
    assert(super::independent::rows_equal(archive_type_table(), super::independent::expand(super::independent::archive_entries(), 0), 0)) by (compute_only);
    assert(super::independent::rows_equal(unknown_scriptable_table(), super::independent::expand(super::independent::scriptable_entries(), 0), 0)) by (compute_only);
    assert(super::independent::rows_equal(unknown_non_scriptable_table(), super::independent::expand(super::independent::non_scriptable_entries(), 0), 0)) by (compute_only);
    assert(super::independent::rows_equal(audio_or_video_type_table(), super::independent::expand(super::independent::audio_or_video_entries(), 0), 0)) by (compute_only);
}

} // verus!
