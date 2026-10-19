//! The executable §4.6 MIME type group predicates, proven to meet
//! [`super::contract`]. Each compares the type, subtype or essence with the
//! standard's literal strings (`eq_*` below, one per `lit_*` in
//! [`super::spec`]).

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

use super::record::{MimeType, ascii_lowercase_exec, slice_eq};

verus! {

/// Does `s` end with `suffix` (Infra §4.7)?
fn ends_with_exec(s: &[u32], suffix: &[u32]) -> (r: bool)
    ensures
        r == ends_with(s@, suffix@),
{
    if suffix.len() > s.len() {
        return false;
    }
    // Never saturates: suffix.len() <= s.len().
    let tail = vstd::slice::slice_subrange(s, s.len().saturating_sub(suffix.len()), s.len());
    slice_eq(tail, suffix)
}

/// Is `mime_type` an image MIME type (§4.6)?
pub fn is_image_mime_type(mime_type: &MimeType) -> (r: bool)
    ensures
        super::contract::group_ensures(super::contract::Group::Image, mime_type@, r),
{
    eq_image(mime_type.type_.as_slice())
}

/// Is `mime_type` an audio or video MIME type (§4.6)?
pub fn is_audio_or_video_mime_type(mime_type: &MimeType) -> (r: bool)
    ensures
        super::contract::group_ensures(super::contract::Group::AudioOrVideo, mime_type@, r),
{
    let essence = mime_type.essence();
    eq_audio(mime_type.type_.as_slice()) || eq_video(mime_type.type_.as_slice())
        || eq_application_ogg(essence.as_slice())
}

/// Is `mime_type` a font MIME type (§4.6)?
pub fn is_font_mime_type(mime_type: &MimeType) -> (r: bool)
    ensures
        super::contract::group_ensures(super::contract::Group::Font, mime_type@, r),
{
    let e = mime_type.essence();
    let e = e.as_slice();
    proof {
        reveal_with_fuel(is_one_of, 8);
    }
    eq_font(mime_type.type_.as_slice()) || eq_application_font_cff(e) || eq_application_font_otf(e)
        || eq_application_font_sfnt(e) || eq_application_font_ttf(e) || eq_application_font_woff(e)
        || eq_application_vnd_ms_fontobject(e) || eq_application_vnd_ms_opentype(e)
}

/// Is `mime_type` a ZIP-based MIME type (§4.6)?
pub fn is_zip_based_mime_type(mime_type: &MimeType) -> (r: bool)
    ensures
        super::contract::group_ensures(super::contract::Group::ZipBased, mime_type@, r),
{
    let e = mime_type.essence();
    let suffix: [u32; 4] = [0x2B, 0x7A, 0x69, 0x70];
    assert(suffix@ =~= lit_plus_zip());
    proof {
        reveal_with_fuel(is_one_of, 2);
    }
    ends_with_exec(mime_type.subtype.as_slice(), suffix.as_slice()) || eq_application_zip(e.as_slice())
}

/// Is `mime_type` an archive MIME type (§4.6)?
pub fn is_archive_mime_type(mime_type: &MimeType) -> (r: bool)
    ensures
        super::contract::group_ensures(super::contract::Group::Archive, mime_type@, r),
{
    let e = mime_type.essence();
    let e = e.as_slice();
    proof {
        reveal_with_fuel(is_one_of, 4);
    }
    eq_application_x_rar_compressed(e) || eq_application_zip(e) || eq_application_x_gzip(e)
}

/// Is `mime_type` an XML MIME type (§4.6)?
pub fn is_xml_mime_type(mime_type: &MimeType) -> (r: bool)
    ensures
        super::contract::group_ensures(super::contract::Group::Xml, mime_type@, r),
{
    let e = mime_type.essence();
    let suffix: [u32; 4] = [0x2B, 0x78, 0x6D, 0x6C];
    assert(suffix@ =~= lit_plus_xml());
    ends_with_exec(mime_type.subtype.as_slice(), suffix.as_slice()) || eq_text_xml(e.as_slice())
        || eq_application_xml(e.as_slice())
}

/// Is `mime_type` an HTML MIME type (§4.6)?
pub fn is_html_mime_type(mime_type: &MimeType) -> (r: bool)
    ensures
        super::contract::group_ensures(super::contract::Group::Html, mime_type@, r),
{
    let e = mime_type.essence();
    eq_text_html(e.as_slice())
}

/// Is `mime_type` a scriptable MIME type (§4.6)?
pub fn is_scriptable_mime_type(mime_type: &MimeType) -> (r: bool)
    ensures
        super::contract::group_ensures(super::contract::Group::Scriptable, mime_type@, r),
{
    let e = mime_type.essence();
    is_xml_mime_type(mime_type) || is_html_mime_type(mime_type) || eq_application_pdf(e.as_slice())
}

/// Is `s` one of the JavaScript MIME type essence strings?
fn is_javascript_essence(s: &[u32]) -> (r: bool)
    ensures
        r == is_one_of(s@, javascript_mime_type_essences()),
{
    proof {
        reveal_with_fuel(is_one_of, 17);
    }
    eq_application_ecmascript(s) || eq_application_javascript(s) || eq_application_x_ecmascript(s)
        || eq_application_x_javascript(s) || eq_text_ecmascript(s) || eq_text_javascript(s)
        || eq_text_javascript1_0(s) || eq_text_javascript1_1(s) || eq_text_javascript1_2(s)
        || eq_text_javascript1_3(s) || eq_text_javascript1_4(s) || eq_text_javascript1_5(s)
        || eq_text_jscript(s) || eq_text_livescript(s) || eq_text_x_ecmascript(s) || eq_text_x_javascript(s)
}

/// Is `mime_type` a JavaScript MIME type (§4.6)?
pub fn is_javascript_mime_type(mime_type: &MimeType) -> (r: bool)
    ensures
        super::contract::group_ensures(super::contract::Group::JavaScript, mime_type@, r),
{
    let e = mime_type.essence();
    is_javascript_essence(e.as_slice())
}

/// Is `s` a JavaScript MIME type essence match (§4.6)?
pub fn is_javascript_mime_type_essence_match(s: &[u32]) -> (r: bool)
    ensures
        super::contract::javascript_essence_match_ensures(s@, r),
{
    let lower = ascii_lowercase_exec(s);
    proof {
        super::lemmas::lemma_javascript_essences_lowercase();
        reveal_with_fuel(javascript_essence_match_from, 17);
        reveal_with_fuel(is_one_of, 17);
    }
    is_javascript_essence(lower.as_slice())
}

/// Is `mime_type` a JSON MIME type (§4.6)?
pub fn is_json_mime_type(mime_type: &MimeType) -> (r: bool)
    ensures
        super::contract::group_ensures(super::contract::Group::Json, mime_type@, r),
{
    let e = mime_type.essence();
    let suffix: [u32; 5] = [0x2B, 0x6A, 0x73, 0x6F, 0x6E];
    assert(suffix@ =~= lit_plus_json());
    ends_with_exec(mime_type.subtype.as_slice(), suffix.as_slice()) || eq_application_json(e.as_slice())
        || eq_text_json(e.as_slice())
}

// The standard's literal strings, as exec comparisons.

/// Is `s` "`image`"?
fn eq_image(s: &[u32]) -> (r: bool)
    ensures
        r == (s@ == lit_image()),
{
    let lit: [u32; 5] = [0x69, 0x6D, 0x61, 0x67, 0x65];
    assert(lit@ =~= lit_image());
    slice_eq(s, lit.as_slice())
}

/// Is `s` "`audio`"?
fn eq_audio(s: &[u32]) -> (r: bool)
    ensures
        r == (s@ == lit_audio()),
{
    let lit: [u32; 5] = [0x61, 0x75, 0x64, 0x69, 0x6F];
    assert(lit@ =~= lit_audio());
    slice_eq(s, lit.as_slice())
}

/// Is `s` "`video`"?
fn eq_video(s: &[u32]) -> (r: bool)
    ensures
        r == (s@ == lit_video()),
{
    let lit: [u32; 5] = [0x76, 0x69, 0x64, 0x65, 0x6F];
    assert(lit@ =~= lit_video());
    slice_eq(s, lit.as_slice())
}

/// Is `s` "`font`"?
fn eq_font(s: &[u32]) -> (r: bool)
    ensures
        r == (s@ == lit_font()),
{
    let lit: [u32; 4] = [0x66, 0x6F, 0x6E, 0x74];
    assert(lit@ =~= lit_font());
    slice_eq(s, lit.as_slice())
}

/// Is `s` "`application/ogg`"?
fn eq_application_ogg(s: &[u32]) -> (r: bool)
    ensures
        r == (s@ == lit_application_ogg()),
{
    let lit: [u32; 15] = [0x61, 0x70, 0x70, 0x6C, 0x69, 0x63, 0x61, 0x74, 0x69, 0x6F, 0x6E, 0x2F, 0x6F, 0x67, 0x67];
    assert(lit@ =~= lit_application_ogg());
    slice_eq(s, lit.as_slice())
}

/// Is `s` "`application/font-cff`"?
fn eq_application_font_cff(s: &[u32]) -> (r: bool)
    ensures
        r == (s@ == lit_application_font_cff()),
{
    let lit: [u32; 20] = [0x61, 0x70, 0x70, 0x6C, 0x69, 0x63, 0x61, 0x74, 0x69, 0x6F, 0x6E, 0x2F, 0x66, 0x6F, 0x6E, 0x74, 0x2D, 0x63, 0x66, 0x66];
    assert(lit@ =~= lit_application_font_cff());
    slice_eq(s, lit.as_slice())
}

/// Is `s` "`application/font-otf`"?
fn eq_application_font_otf(s: &[u32]) -> (r: bool)
    ensures
        r == (s@ == lit_application_font_otf()),
{
    let lit: [u32; 20] = [0x61, 0x70, 0x70, 0x6C, 0x69, 0x63, 0x61, 0x74, 0x69, 0x6F, 0x6E, 0x2F, 0x66, 0x6F, 0x6E, 0x74, 0x2D, 0x6F, 0x74, 0x66];
    assert(lit@ =~= lit_application_font_otf());
    slice_eq(s, lit.as_slice())
}

/// Is `s` "`application/font-sfnt`"?
fn eq_application_font_sfnt(s: &[u32]) -> (r: bool)
    ensures
        r == (s@ == lit_application_font_sfnt()),
{
    let lit: [u32; 21] = [0x61, 0x70, 0x70, 0x6C, 0x69, 0x63, 0x61, 0x74, 0x69, 0x6F, 0x6E, 0x2F, 0x66, 0x6F, 0x6E, 0x74, 0x2D, 0x73, 0x66, 0x6E, 0x74];
    assert(lit@ =~= lit_application_font_sfnt());
    slice_eq(s, lit.as_slice())
}

/// Is `s` "`application/font-ttf`"?
fn eq_application_font_ttf(s: &[u32]) -> (r: bool)
    ensures
        r == (s@ == lit_application_font_ttf()),
{
    let lit: [u32; 20] = [0x61, 0x70, 0x70, 0x6C, 0x69, 0x63, 0x61, 0x74, 0x69, 0x6F, 0x6E, 0x2F, 0x66, 0x6F, 0x6E, 0x74, 0x2D, 0x74, 0x74, 0x66];
    assert(lit@ =~= lit_application_font_ttf());
    slice_eq(s, lit.as_slice())
}

/// Is `s` "`application/font-woff`"?
fn eq_application_font_woff(s: &[u32]) -> (r: bool)
    ensures
        r == (s@ == lit_application_font_woff()),
{
    let lit: [u32; 21] = [0x61, 0x70, 0x70, 0x6C, 0x69, 0x63, 0x61, 0x74, 0x69, 0x6F, 0x6E, 0x2F, 0x66, 0x6F, 0x6E, 0x74, 0x2D, 0x77, 0x6F, 0x66, 0x66];
    assert(lit@ =~= lit_application_font_woff());
    slice_eq(s, lit.as_slice())
}

/// Is `s` "`application/vnd.ms-fontobject`"?
fn eq_application_vnd_ms_fontobject(s: &[u32]) -> (r: bool)
    ensures
        r == (s@ == lit_application_vnd_ms_fontobject()),
{
    let lit: [u32; 29] = [0x61, 0x70, 0x70, 0x6C, 0x69, 0x63, 0x61, 0x74, 0x69, 0x6F, 0x6E, 0x2F, 0x76, 0x6E, 0x64, 0x2E, 0x6D, 0x73, 0x2D, 0x66, 0x6F, 0x6E, 0x74, 0x6F, 0x62, 0x6A, 0x65, 0x63, 0x74];
    assert(lit@ =~= lit_application_vnd_ms_fontobject());
    slice_eq(s, lit.as_slice())
}

/// Is `s` "`application/vnd.ms-opentype`"?
fn eq_application_vnd_ms_opentype(s: &[u32]) -> (r: bool)
    ensures
        r == (s@ == lit_application_vnd_ms_opentype()),
{
    let lit: [u32; 27] = [0x61, 0x70, 0x70, 0x6C, 0x69, 0x63, 0x61, 0x74, 0x69, 0x6F, 0x6E, 0x2F, 0x76, 0x6E, 0x64, 0x2E, 0x6D, 0x73, 0x2D, 0x6F, 0x70, 0x65, 0x6E, 0x74, 0x79, 0x70, 0x65];
    assert(lit@ =~= lit_application_vnd_ms_opentype());
    slice_eq(s, lit.as_slice())
}

/// Is `s` "`application/zip`"?
fn eq_application_zip(s: &[u32]) -> (r: bool)
    ensures
        r == (s@ == lit_application_zip()),
{
    let lit: [u32; 15] = [0x61, 0x70, 0x70, 0x6C, 0x69, 0x63, 0x61, 0x74, 0x69, 0x6F, 0x6E, 0x2F, 0x7A, 0x69, 0x70];
    assert(lit@ =~= lit_application_zip());
    slice_eq(s, lit.as_slice())
}

/// Is `s` "`application/x-rar-compressed`"?
fn eq_application_x_rar_compressed(s: &[u32]) -> (r: bool)
    ensures
        r == (s@ == lit_application_x_rar_compressed()),
{
    let lit: [u32; 28] = [0x61, 0x70, 0x70, 0x6C, 0x69, 0x63, 0x61, 0x74, 0x69, 0x6F, 0x6E, 0x2F, 0x78, 0x2D, 0x72, 0x61, 0x72, 0x2D, 0x63, 0x6F, 0x6D, 0x70, 0x72, 0x65, 0x73, 0x73, 0x65, 0x64];
    assert(lit@ =~= lit_application_x_rar_compressed());
    slice_eq(s, lit.as_slice())
}

/// Is `s` "`application/x-gzip`"?
fn eq_application_x_gzip(s: &[u32]) -> (r: bool)
    ensures
        r == (s@ == lit_application_x_gzip()),
{
    let lit: [u32; 18] = [0x61, 0x70, 0x70, 0x6C, 0x69, 0x63, 0x61, 0x74, 0x69, 0x6F, 0x6E, 0x2F, 0x78, 0x2D, 0x67, 0x7A, 0x69, 0x70];
    assert(lit@ =~= lit_application_x_gzip());
    slice_eq(s, lit.as_slice())
}

/// Is `s` "`text/xml`"?
fn eq_text_xml(s: &[u32]) -> (r: bool)
    ensures
        r == (s@ == lit_text_xml()),
{
    let lit: [u32; 8] = [0x74, 0x65, 0x78, 0x74, 0x2F, 0x78, 0x6D, 0x6C];
    assert(lit@ =~= lit_text_xml());
    slice_eq(s, lit.as_slice())
}

/// Is `s` "`application/xml`"?
fn eq_application_xml(s: &[u32]) -> (r: bool)
    ensures
        r == (s@ == lit_application_xml()),
{
    let lit: [u32; 15] = [0x61, 0x70, 0x70, 0x6C, 0x69, 0x63, 0x61, 0x74, 0x69, 0x6F, 0x6E, 0x2F, 0x78, 0x6D, 0x6C];
    assert(lit@ =~= lit_application_xml());
    slice_eq(s, lit.as_slice())
}

/// Is `s` "`text/html`"?
fn eq_text_html(s: &[u32]) -> (r: bool)
    ensures
        r == (s@ == lit_text_html()),
{
    let lit: [u32; 9] = [0x74, 0x65, 0x78, 0x74, 0x2F, 0x68, 0x74, 0x6D, 0x6C];
    assert(lit@ =~= lit_text_html());
    slice_eq(s, lit.as_slice())
}

/// Is `s` "`application/pdf`"?
fn eq_application_pdf(s: &[u32]) -> (r: bool)
    ensures
        r == (s@ == lit_application_pdf()),
{
    let lit: [u32; 15] = [0x61, 0x70, 0x70, 0x6C, 0x69, 0x63, 0x61, 0x74, 0x69, 0x6F, 0x6E, 0x2F, 0x70, 0x64, 0x66];
    assert(lit@ =~= lit_application_pdf());
    slice_eq(s, lit.as_slice())
}

/// Is `s` "`application/ecmascript`"?
fn eq_application_ecmascript(s: &[u32]) -> (r: bool)
    ensures
        r == (s@ == lit_application_ecmascript()),
{
    let lit: [u32; 22] = [0x61, 0x70, 0x70, 0x6C, 0x69, 0x63, 0x61, 0x74, 0x69, 0x6F, 0x6E, 0x2F, 0x65, 0x63, 0x6D, 0x61, 0x73, 0x63, 0x72, 0x69, 0x70, 0x74];
    assert(lit@ =~= lit_application_ecmascript());
    slice_eq(s, lit.as_slice())
}

/// Is `s` "`application/javascript`"?
fn eq_application_javascript(s: &[u32]) -> (r: bool)
    ensures
        r == (s@ == lit_application_javascript()),
{
    let lit: [u32; 22] = [0x61, 0x70, 0x70, 0x6C, 0x69, 0x63, 0x61, 0x74, 0x69, 0x6F, 0x6E, 0x2F, 0x6A, 0x61, 0x76, 0x61, 0x73, 0x63, 0x72, 0x69, 0x70, 0x74];
    assert(lit@ =~= lit_application_javascript());
    slice_eq(s, lit.as_slice())
}

/// Is `s` "`application/x-ecmascript`"?
fn eq_application_x_ecmascript(s: &[u32]) -> (r: bool)
    ensures
        r == (s@ == lit_application_x_ecmascript()),
{
    let lit: [u32; 24] = [0x61, 0x70, 0x70, 0x6C, 0x69, 0x63, 0x61, 0x74, 0x69, 0x6F, 0x6E, 0x2F, 0x78, 0x2D, 0x65, 0x63, 0x6D, 0x61, 0x73, 0x63, 0x72, 0x69, 0x70, 0x74];
    assert(lit@ =~= lit_application_x_ecmascript());
    slice_eq(s, lit.as_slice())
}

/// Is `s` "`application/x-javascript`"?
fn eq_application_x_javascript(s: &[u32]) -> (r: bool)
    ensures
        r == (s@ == lit_application_x_javascript()),
{
    let lit: [u32; 24] = [0x61, 0x70, 0x70, 0x6C, 0x69, 0x63, 0x61, 0x74, 0x69, 0x6F, 0x6E, 0x2F, 0x78, 0x2D, 0x6A, 0x61, 0x76, 0x61, 0x73, 0x63, 0x72, 0x69, 0x70, 0x74];
    assert(lit@ =~= lit_application_x_javascript());
    slice_eq(s, lit.as_slice())
}

/// Is `s` "`text/ecmascript`"?
fn eq_text_ecmascript(s: &[u32]) -> (r: bool)
    ensures
        r == (s@ == lit_text_ecmascript()),
{
    let lit: [u32; 15] = [0x74, 0x65, 0x78, 0x74, 0x2F, 0x65, 0x63, 0x6D, 0x61, 0x73, 0x63, 0x72, 0x69, 0x70, 0x74];
    assert(lit@ =~= lit_text_ecmascript());
    slice_eq(s, lit.as_slice())
}

/// Is `s` "`text/javascript`"?
fn eq_text_javascript(s: &[u32]) -> (r: bool)
    ensures
        r == (s@ == lit_text_javascript()),
{
    let lit: [u32; 15] = [0x74, 0x65, 0x78, 0x74, 0x2F, 0x6A, 0x61, 0x76, 0x61, 0x73, 0x63, 0x72, 0x69, 0x70, 0x74];
    assert(lit@ =~= lit_text_javascript());
    slice_eq(s, lit.as_slice())
}

/// Is `s` "`text/javascript1.0`"?
fn eq_text_javascript1_0(s: &[u32]) -> (r: bool)
    ensures
        r == (s@ == lit_text_javascript1_0()),
{
    let lit: [u32; 18] = [0x74, 0x65, 0x78, 0x74, 0x2F, 0x6A, 0x61, 0x76, 0x61, 0x73, 0x63, 0x72, 0x69, 0x70, 0x74, 0x31, 0x2E, 0x30];
    assert(lit@ =~= lit_text_javascript1_0());
    slice_eq(s, lit.as_slice())
}

/// Is `s` "`text/javascript1.1`"?
fn eq_text_javascript1_1(s: &[u32]) -> (r: bool)
    ensures
        r == (s@ == lit_text_javascript1_1()),
{
    let lit: [u32; 18] = [0x74, 0x65, 0x78, 0x74, 0x2F, 0x6A, 0x61, 0x76, 0x61, 0x73, 0x63, 0x72, 0x69, 0x70, 0x74, 0x31, 0x2E, 0x31];
    assert(lit@ =~= lit_text_javascript1_1());
    slice_eq(s, lit.as_slice())
}

/// Is `s` "`text/javascript1.2`"?
fn eq_text_javascript1_2(s: &[u32]) -> (r: bool)
    ensures
        r == (s@ == lit_text_javascript1_2()),
{
    let lit: [u32; 18] = [0x74, 0x65, 0x78, 0x74, 0x2F, 0x6A, 0x61, 0x76, 0x61, 0x73, 0x63, 0x72, 0x69, 0x70, 0x74, 0x31, 0x2E, 0x32];
    assert(lit@ =~= lit_text_javascript1_2());
    slice_eq(s, lit.as_slice())
}

/// Is `s` "`text/javascript1.3`"?
fn eq_text_javascript1_3(s: &[u32]) -> (r: bool)
    ensures
        r == (s@ == lit_text_javascript1_3()),
{
    let lit: [u32; 18] = [0x74, 0x65, 0x78, 0x74, 0x2F, 0x6A, 0x61, 0x76, 0x61, 0x73, 0x63, 0x72, 0x69, 0x70, 0x74, 0x31, 0x2E, 0x33];
    assert(lit@ =~= lit_text_javascript1_3());
    slice_eq(s, lit.as_slice())
}

/// Is `s` "`text/javascript1.4`"?
fn eq_text_javascript1_4(s: &[u32]) -> (r: bool)
    ensures
        r == (s@ == lit_text_javascript1_4()),
{
    let lit: [u32; 18] = [0x74, 0x65, 0x78, 0x74, 0x2F, 0x6A, 0x61, 0x76, 0x61, 0x73, 0x63, 0x72, 0x69, 0x70, 0x74, 0x31, 0x2E, 0x34];
    assert(lit@ =~= lit_text_javascript1_4());
    slice_eq(s, lit.as_slice())
}

/// Is `s` "`text/javascript1.5`"?
fn eq_text_javascript1_5(s: &[u32]) -> (r: bool)
    ensures
        r == (s@ == lit_text_javascript1_5()),
{
    let lit: [u32; 18] = [0x74, 0x65, 0x78, 0x74, 0x2F, 0x6A, 0x61, 0x76, 0x61, 0x73, 0x63, 0x72, 0x69, 0x70, 0x74, 0x31, 0x2E, 0x35];
    assert(lit@ =~= lit_text_javascript1_5());
    slice_eq(s, lit.as_slice())
}

/// Is `s` "`text/jscript`"?
fn eq_text_jscript(s: &[u32]) -> (r: bool)
    ensures
        r == (s@ == lit_text_jscript()),
{
    let lit: [u32; 12] = [0x74, 0x65, 0x78, 0x74, 0x2F, 0x6A, 0x73, 0x63, 0x72, 0x69, 0x70, 0x74];
    assert(lit@ =~= lit_text_jscript());
    slice_eq(s, lit.as_slice())
}

/// Is `s` "`text/livescript`"?
fn eq_text_livescript(s: &[u32]) -> (r: bool)
    ensures
        r == (s@ == lit_text_livescript()),
{
    let lit: [u32; 15] = [0x74, 0x65, 0x78, 0x74, 0x2F, 0x6C, 0x69, 0x76, 0x65, 0x73, 0x63, 0x72, 0x69, 0x70, 0x74];
    assert(lit@ =~= lit_text_livescript());
    slice_eq(s, lit.as_slice())
}

/// Is `s` "`text/x-ecmascript`"?
fn eq_text_x_ecmascript(s: &[u32]) -> (r: bool)
    ensures
        r == (s@ == lit_text_x_ecmascript()),
{
    let lit: [u32; 17] = [0x74, 0x65, 0x78, 0x74, 0x2F, 0x78, 0x2D, 0x65, 0x63, 0x6D, 0x61, 0x73, 0x63, 0x72, 0x69, 0x70, 0x74];
    assert(lit@ =~= lit_text_x_ecmascript());
    slice_eq(s, lit.as_slice())
}

/// Is `s` "`text/x-javascript`"?
fn eq_text_x_javascript(s: &[u32]) -> (r: bool)
    ensures
        r == (s@ == lit_text_x_javascript()),
{
    let lit: [u32; 17] = [0x74, 0x65, 0x78, 0x74, 0x2F, 0x78, 0x2D, 0x6A, 0x61, 0x76, 0x61, 0x73, 0x63, 0x72, 0x69, 0x70, 0x74];
    assert(lit@ =~= lit_text_x_javascript());
    slice_eq(s, lit.as_slice())
}

/// Is `s` "`application/json`"?
fn eq_application_json(s: &[u32]) -> (r: bool)
    ensures
        r == (s@ == lit_application_json()),
{
    let lit: [u32; 16] = [0x61, 0x70, 0x70, 0x6C, 0x69, 0x63, 0x61, 0x74, 0x69, 0x6F, 0x6E, 0x2F, 0x6A, 0x73, 0x6F, 0x6E];
    assert(lit@ =~= lit_application_json());
    slice_eq(s, lit.as_slice())
}

/// Is `s` "`text/json`"?
fn eq_text_json(s: &[u32]) -> (r: bool)
    ensures
        r == (s@ == lit_text_json()),
{
    let lit: [u32; 9] = [0x74, 0x65, 0x78, 0x74, 0x2F, 0x6A, 0x73, 0x6F, 0x6E];
    assert(lit@ =~= lit_text_json());
    slice_eq(s, lit.as_slice())
}

} // verus!

#[cfg(test)]
mod tests {
    use super::*;

    fn u(s: &str) -> Vec<u32> {
        s.chars().map(u32::from).collect()
    }

    /// Each hex literal in `spec.rs` is the text its doc comment says: the
    /// `eq_*` functions are proven to compare against exactly the `lit_*`
    /// spec strings, and here each accepts its text and rejects a change.
    #[test]
    fn literals_are_their_text() {
        assert!(eq_image(&u("image")));
        assert!(eq_audio(&u("audio")));
        assert!(eq_video(&u("video")));
        assert!(eq_font(&u("font")));
        assert!(eq_application_ogg(&u("application/ogg")));
        assert!(eq_application_font_cff(&u("application/font-cff")));
        assert!(eq_application_font_otf(&u("application/font-otf")));
        assert!(eq_application_font_sfnt(&u("application/font-sfnt")));
        assert!(eq_application_font_ttf(&u("application/font-ttf")));
        assert!(eq_application_font_woff(&u("application/font-woff")));
        assert!(eq_application_vnd_ms_fontobject(&u(
            "application/vnd.ms-fontobject"
        )));
        assert!(eq_application_vnd_ms_opentype(&u(
            "application/vnd.ms-opentype"
        )));
        assert!(eq_application_zip(&u("application/zip")));
        assert!(eq_application_x_rar_compressed(&u(
            "application/x-rar-compressed"
        )));
        assert!(eq_application_x_gzip(&u("application/x-gzip")));
        assert!(eq_text_xml(&u("text/xml")));
        assert!(eq_application_xml(&u("application/xml")));
        assert!(eq_text_html(&u("text/html")));
        assert!(eq_application_pdf(&u("application/pdf")));
        assert!(eq_application_ecmascript(&u("application/ecmascript")));
        assert!(eq_application_javascript(&u("application/javascript")));
        assert!(eq_application_x_ecmascript(&u("application/x-ecmascript")));
        assert!(eq_application_x_javascript(&u("application/x-javascript")));
        assert!(eq_text_ecmascript(&u("text/ecmascript")));
        assert!(eq_text_javascript(&u("text/javascript")));
        assert!(eq_text_javascript1_0(&u("text/javascript1.0")));
        assert!(eq_text_javascript1_1(&u("text/javascript1.1")));
        assert!(eq_text_javascript1_2(&u("text/javascript1.2")));
        assert!(eq_text_javascript1_3(&u("text/javascript1.3")));
        assert!(eq_text_javascript1_4(&u("text/javascript1.4")));
        assert!(eq_text_javascript1_5(&u("text/javascript1.5")));
        assert!(eq_text_jscript(&u("text/jscript")));
        assert!(eq_text_livescript(&u("text/livescript")));
        assert!(eq_text_x_ecmascript(&u("text/x-ecmascript")));
        assert!(eq_text_x_javascript(&u("text/x-javascript")));
        assert!(eq_application_json(&u("application/json")));
        assert!(eq_text_json(&u("text/json")));
        assert!(!eq_text_html(&u("text/htm")));
        assert!(!eq_text_html(&u("text/htmlx")));
        assert!(!eq_text_html(&u("text/HTML")));
    }
}
