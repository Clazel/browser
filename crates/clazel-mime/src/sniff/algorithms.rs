//! The sniffing algorithms built on the pattern tables: the image, font and
//! archive type pattern matching algorithms (§6.1, §6.3, §6.4),
//! check-for-apache-bug (§5.1), the rules for distinguishing if a resource
//! is text or binary (§7.2), the rules for identifying an unknown MIME type
//! (§7.1) and the MIME type sniffing algorithm (§7). Each is proven against
//! [`super::contract`].

use super::pattern::{contains_binary_data_byte_exec, mime_literal};
#[allow(unused_imports)]
use super::spec::*;
use crate::mime_type::groups;
use crate::mime_type::record::{MimeType, copy, slice_eq};
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The image type pattern matching algorithm (§6.1).
pub fn match_image_type_pattern(input: &[u8]) -> (r: Option<MimeType>)
    ensures
        super::contract::type_pattern_ensures(super::contract::TypePattern::Image, input@, crate::mime_type::record::option_view(r)),
{
    super::tables::match_image_table(input)
}

/// The audio or video type pattern matching algorithm (§6.2).
pub fn match_audio_or_video_type_pattern(input: &[u8]) -> (r: Option<MimeType>)
    ensures
        super::contract::type_pattern_ensures(super::contract::TypePattern::AudioOrVideo, input@, crate::mime_type::record::option_view(r)),
{
    super::signatures::match_audio_or_video_type_pattern(input)
}

/// The font type pattern matching algorithm (§6.3).
pub fn match_font_type_pattern(input: &[u8]) -> (r: Option<MimeType>)
    ensures
        super::contract::type_pattern_ensures(super::contract::TypePattern::Font, input@, crate::mime_type::record::option_view(r)),
{
    super::tables::match_font_table(input)
}

/// The archive type pattern matching algorithm (§6.4).
pub fn match_archive_type_pattern(input: &[u8]) -> (r: Option<MimeType>)
    ensures
        super::contract::type_pattern_ensures(super::contract::TypePattern::Archive, input@, crate::mime_type::record::option_view(r)),
{
    super::tables::match_archive_table(input)
}

/// Are `a` and `b` the same byte sequence?
fn bytes_eq(a: &[u8], b: &[u8]) -> (r: bool)
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
            forall|k: int| 0 <= k < i ==> a@[k] == b@[k],
        decreases a.len() - i,
    {
        if a.get(i) != b.get(i) {
            return false;
        }
        // Never saturates: i < a.len().
        i = i.saturating_add(1);
    }
    assert(a@ =~= b@);
    true
}

/// check-for-apache-bug (§5.1 step 2.1.2): is `supplied_type` exactly
/// equal to one of the values in the table?
pub fn check_for_apache_bug_exec(supplied_type: &[u8]) -> (r: bool)
    ensures
        super::contract::check_for_apache_bug_ensures(supplied_type@, r),
{
    let ghost values = apache_bug_values();
    proof {
        reveal_with_fuel(is_one_of_bytes, 5);
    }
    // text/plain
    let v0: &[u8] = &[0x74u8, 0x65, 0x78, 0x74, 0x2F, 0x70, 0x6C, 0x61, 0x69, 0x6E];
    // text/plain; charset=ISO-8859-1
    let v1: &[u8] = &[0x74u8, 0x65, 0x78, 0x74, 0x2F, 0x70, 0x6C, 0x61, 0x69, 0x6E, 0x3B, 0x20, 0x63, 0x68, 0x61, 0x72, 0x73, 0x65, 0x74, 0x3D, 0x49, 0x53, 0x4F, 0x2D, 0x38, 0x38, 0x35, 0x39, 0x2D, 0x31];
    // text/plain; charset=iso-8859-1
    let v2: &[u8] = &[0x74u8, 0x65, 0x78, 0x74, 0x2F, 0x70, 0x6C, 0x61, 0x69, 0x6E, 0x3B, 0x20, 0x63, 0x68, 0x61, 0x72, 0x73, 0x65, 0x74, 0x3D, 0x69, 0x73, 0x6F, 0x2D, 0x38, 0x38, 0x35, 0x39, 0x2D, 0x31];
    // text/plain; charset=UTF-8
    let v3: &[u8] = &[0x74u8, 0x65, 0x78, 0x74, 0x2F, 0x70, 0x6C, 0x61, 0x69, 0x6E, 0x3B, 0x20, 0x63, 0x68, 0x61, 0x72, 0x73, 0x65, 0x74, 0x3D, 0x55, 0x54, 0x46, 0x2D, 0x38];
    assert(v0@ =~= values[0] && v1@ =~= values[1] && v2@ =~= values[2] && v3@ =~= values[3]);
    assert(values.drop_first().drop_first().drop_first().drop_first().len() == 0);
    bytes_eq(supplied_type, v0) || bytes_eq(supplied_type, v1) || bytes_eq(supplied_type, v2) || bytes_eq(supplied_type, v3)
}

/// "text/plain".
fn text_plain() -> (m: MimeType)
    ensures
        m@ == mime_type(seq![0x74u32, 0x65, 0x78, 0x74], seq![0x70u32, 0x6C, 0x61, 0x69, 0x6E]),
{
    let m = mime_literal(&[0x74u32, 0x65, 0x78, 0x74], &[0x70u32, 0x6C, 0x61, 0x69, 0x6E]);
    assert(m@ =~= mime_type(seq![0x74u32, 0x65, 0x78, 0x74], seq![0x70u32, 0x6C, 0x61, 0x69, 0x6E]));
    m
}

/// "application/octet-stream".
fn application_octet_stream() -> (m: MimeType)
    ensures
        m@ == mime_type(seq![0x61u32, 0x70, 0x70, 0x6C, 0x69, 0x63, 0x61, 0x74, 0x69, 0x6F, 0x6E],
            seq![0x6Fu32, 0x63, 0x74, 0x65, 0x74, 0x2D, 0x73, 0x74, 0x72, 0x65, 0x61, 0x6D]),
{
    let m = mime_literal(&[0x61u32, 0x70, 0x70, 0x6C, 0x69, 0x63, 0x61, 0x74, 0x69, 0x6F, 0x6E],
        &[0x6Fu32, 0x63, 0x74, 0x65, 0x74, 0x2D, 0x73, 0x74, 0x72, 0x65, 0x61, 0x6D]);
    assert(m@ =~= mime_type(seq![0x61u32, 0x70, 0x70, 0x6C, 0x69, 0x63, 0x61, 0x74, 0x69, 0x6F, 0x6E],
        seq![0x6Fu32, 0x63, 0x74, 0x65, 0x74, 0x2D, 0x73, 0x74, 0x72, 0x65, 0x61, 0x6D]));
    m
}

/// The rules for distinguishing if a resource is text or binary (§7.2).
pub fn distinguish_text_or_binary_exec(header: &[u8]) -> (r: MimeType)
    ensures
        super::contract::distinguish_text_or_binary_ensures(header@, r@),
{
    // 1. "Let length be the number of bytes in the resource header."
    let length = header.len();
    // 2. UTF-16BE or UTF-16LE BOM: "text/plain".
    if length >= 2 {
        let (b0, b1) = match (header.first(), header.get(1)) {
            (Some(b0), Some(b1)) => (*b0, *b1),
            _ => (0, 0),
        };
        if (b0 == 0xFE && b1 == 0xFF) || (b0 == 0xFF && b1 == 0xFE) {
            return text_plain();
        }
    }
    // 3. UTF-8 BOM: "text/plain".
    if length >= 3 {
        let (b0, b1, b2) = match (header.first(), header.get(1), header.get(2)) {
            (Some(b0), Some(b1), Some(b2)) => (*b0, *b1, *b2),
            _ => (0, 0, 0),
        };
        if b0 == 0xEF && b1 == 0xBB && b2 == 0xBF {
            return text_plain();
        }
    }
    // 4. "If the resource header contains no binary data bytes, the
    //    computed MIME type is "text/plain"."
    if !contains_binary_data_byte_exec(header) {
        return text_plain();
    }
    // 5. "The computed MIME type is "application/octet-stream"."
    application_octet_stream()
}

/// The rules for identifying an unknown MIME type (§7.1).
pub fn identify_unknown_mime_type_exec(header: &[u8], sniff_scriptable: bool) -> (r: MimeType)
    ensures
        super::contract::identify_unknown_mime_type_ensures(header@, sniff_scriptable, r@),
{
    // 1. "If the sniff-scriptable flag is set, execute the following steps
    //    for each row row in the following table:"
    let scriptable = if sniff_scriptable {
        super::tables::match_unknown_scriptable_table(header)
    } else {
        None
    };
    if let Some(t) = scriptable {
        return t;
    }
    // 2. The second table.
    if let Some(t) = super::tables::match_unknown_non_scriptable_table(header) {
        return t;
    }
    // 3–4. The image type pattern matching algorithm.
    if let Some(t) = match_image_type_pattern(header) {
        return t;
    }
    // 5–6. The audio or video type pattern matching algorithm.
    if let Some(t) = match_audio_or_video_type_pattern(header) {
        return t;
    }
    // 7–8. The archive type pattern matching algorithm.
    if let Some(t) = match_archive_type_pattern(header) {
        return t;
    }
    // 9. "If resource's resource header contains no binary data bytes,
    //    return "text/plain"."
    if !contains_binary_data_byte_exec(header) {
        return text_plain();
    }
    // 10. "Return "application/octet-stream"."
    application_octet_stream()
}

/// A copy of `m`.
fn copy_mime_type(m: &MimeType) -> (r: MimeType)
    ensures
        r@ == m@,
{
    let mut parameters: Vec<(Vec<u32>, Vec<u32>)> = Vec::new();
    let mut i: usize = 0;
    while i < m.parameters.len()
        invariant
            i <= m.parameters.len(),
            crate::mime_type::record::parameters_view(parameters@) =~= crate::mime_type::record::parameters_view(m.parameters@).subrange(0, i as int),
        decreases m.parameters.len() - i,
    {
        let ghost before = parameters@;
        if let Some(e) = m.parameters.get(i) {
            parameters.push((copy(e.0.as_slice()), copy(e.1.as_slice())));
        }
        assert(parameters@ == before.push(parameters@.last()));
        assert(crate::mime_type::record::parameters_view(parameters@) =~= crate::mime_type::record::parameters_view(before).push((m.parameters@[i as int].0@, m.parameters@[i as int].1@)));
        // Never saturates: i < m.parameters.len().
        i = i.saturating_add(1);
    }
    assert(crate::mime_type::record::parameters_view(m.parameters@).subrange(0, m.parameters.len() as int) =~= crate::mime_type::record::parameters_view(m.parameters@));
    MimeType { type_: copy(m.type_.as_slice()), subtype: copy(m.subtype.as_slice()), parameters }
}

/// The supplied MIME type's essence is "unknown/unknown",
/// "application/unknown", or "*/*" (§7 step 2).
fn is_unknown_essence_exec(m: &MimeType) -> (r: bool)
    ensures
        r == is_unknown_essence(m@),
{
    let e = m.essence();
    let e = e.as_slice();
    let unknown_unknown: &[u32] = &[0x75u32, 0x6E, 0x6B, 0x6E, 0x6F, 0x77, 0x6E, 0x2F, 0x75, 0x6E, 0x6B, 0x6E, 0x6F, 0x77, 0x6E];
    let application_unknown: &[u32] = &[0x61u32, 0x70, 0x70, 0x6C, 0x69, 0x63, 0x61, 0x74, 0x69, 0x6F, 0x6E, 0x2F, 0x75, 0x6E, 0x6B, 0x6E, 0x6F, 0x77, 0x6E];
    let any: &[u32] = &[0x2Au32, 0x2F, 0x2A];
    assert(unknown_unknown@ =~= seq![0x75u32, 0x6E, 0x6B, 0x6E, 0x6F, 0x77, 0x6E, 0x2F, 0x75, 0x6E, 0x6B, 0x6E, 0x6F, 0x77, 0x6E]);
    assert(application_unknown@ =~= seq![0x61u32, 0x70, 0x70, 0x6C, 0x69, 0x63, 0x61, 0x74, 0x69, 0x6F, 0x6E, 0x2F, 0x75, 0x6E, 0x6B, 0x6E, 0x6F, 0x77, 0x6E]);
    assert(any@ =~= seq![0x2Au32, 0x2F, 0x2A]);
    slice_eq(e, unknown_unknown) || slice_eq(e, application_unknown) || slice_eq(e, any)
}

/// A resource and the metadata §5 says a user agent tracks for it,
/// viewed as [`super::spec::Resource`].
pub struct Resource {
    /// The supplied MIME type; `None` is undefined.
    pub supplied: Option<MimeType>,
    /// The check-for-apache-bug flag.
    pub check_for_apache_bug: bool,
    /// The no-sniff flag.
    pub no_sniff: bool,
    /// The resource header.
    pub header: Vec<u8>,
}

impl View for Resource {
    type V = super::spec::Resource;

    open spec fn view(&self) -> super::spec::Resource {
        super::spec::Resource {
            supplied: crate::mime_type::record::option_view(self.supplied),
            check_for_apache_bug: self.check_for_apache_bug,
            no_sniff: self.no_sniff,
            header: self.header@,
        }
    }
}

/// The MIME type sniffing algorithm (§7,
/// #determining-the-computed-mime-type-of-a-resource). `supported`: the
/// supplied MIME type is supported by the user agent.
pub fn computed_mime_type_exec(resource: &Resource, supported: bool) -> (r: MimeType)
    ensures
        super::contract::computed_mime_type_ensures(resource@, supported, r@),
{
    let header = resource.header.as_slice();
    let supplied = match &resource.supplied {
        // 2. "If the supplied MIME type is undefined ..., execute the rules
        //    for identifying an unknown MIME type with the sniff-scriptable
        //    flag equal to the inverse of the no-sniff flag and abort these
        //    steps."
        None => return identify_unknown_mime_type_exec(header, !resource.no_sniff),
        Some(s) => s,
    };
    // 1. "If the supplied MIME type is an XML MIME type or HTML MIME type,
    //    the computed MIME type is the supplied MIME type. Abort these
    //    steps."
    if groups::is_xml_mime_type(supplied) || groups::is_html_mime_type(supplied) {
        return copy_mime_type(supplied);
    }
    // 2. "... or if the supplied MIME type's essence is "unknown/unknown",
    //    "application/unknown", or "*/*", ..."
    if is_unknown_essence_exec(supplied) {
        return identify_unknown_mime_type_exec(header, !resource.no_sniff);
    }
    // 3. "If the no-sniff flag is set, the computed MIME type is the
    //    supplied MIME type. Abort these steps."
    if resource.no_sniff {
        return copy_mime_type(supplied);
    }
    // 4. "If the check-for-apache-bug flag is set, execute the rules for
    //    distinguishing if a resource is text or binary and abort these
    //    steps."
    if resource.check_for_apache_bug {
        return distinguish_text_or_binary_exec(header);
    }
    // 5–6. "If the supplied MIME type is an image MIME type supported by
    //    the user agent, let matched-type be the result of executing the
    //    image type pattern matching algorithm with the resource header";
    //    if it is not undefined, it is the computed MIME type.
    let image = if supported && groups::is_image_mime_type(supplied) {
        match_image_type_pattern(header)
    } else {
        None
    };
    if let Some(t) = image {
        return t;
    }
    // 7–8. The same with the audio or video type pattern matching
    //    algorithm.
    let av = if supported && groups::is_audio_or_video_mime_type(supplied) {
        match_audio_or_video_type_pattern(header)
    } else {
        None
    };
    if let Some(t) = av {
        return t;
    }
    // 9. "The computed MIME type is the supplied MIME type."
    copy_mime_type(supplied)
}

} // verus!
