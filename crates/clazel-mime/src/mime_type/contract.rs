//! Contracts the executable MIME type functions must be proven to meet.
//! Each exec function's `ensures` clause is exactly one of these
//! predicates, so reviewing these (and [`super::spec`]) is enough to know
//! what the implementation guarantees.
//!
//! Strings are sequences of scalar values as `u32` (`&[u32]`, `Vec<u32>`),
//! as in `clazel-encoding`, whose UTF-8 decoder outputs exactly that. An
//! exec MIME type is viewed as a [`MimeTypeRecord`]; `None` is failure.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Contract for `parse(&[u32]) -> Option<MimeType>`: equals "parse a MIME
/// type".
pub open spec fn parse_ensures(input: Seq<u32>, output: Option<MimeTypeRecord>) -> bool {
    output == parse_a_mime_type(input)
}

/// Contract for `parse_from_bytes(&[u8]) -> Option<MimeType>`: equals
/// "parse a MIME type from bytes".
pub open spec fn parse_from_bytes_ensures(input: Seq<u8>, output: Option<MimeTypeRecord>) -> bool {
    output == parse_a_mime_type_from_bytes(input)
}

/// Contract for `serialize(&MimeType) -> Vec<u32>`: equals "serialize a
/// MIME type". Defined for every record.
pub open spec fn serialize_ensures(mime_type: MimeTypeRecord, output: Seq<u32>) -> bool {
    output == serialize_a_mime_type(mime_type)
}

/// Every code point of `s` is at most U+00FF.
pub open spec fn all_at_most_ff(s: Seq<u32>) -> bool {
    forall|k: int| 0 <= k < s.len() ==> #[trigger] s[k] <= 0xFF
}

/// Precondition of `serialize_to_bytes(&MimeType) -> Vec<u8>`: the
/// assertion in isomorphic encode (Infra §4.7, step 1), "input contains no
/// code points greater than U+00FF", for the serialization. Every record
/// that parsing returns meets it (`lemmas::lemma_parse_serializable`).
pub open spec fn serialize_to_bytes_requires(mime_type: MimeTypeRecord) -> bool {
    all_at_most_ff(serialize_a_mime_type(mime_type))
}

/// Contract for `serialize_to_bytes(&MimeType) -> Vec<u8>`: equals
/// "serialize a MIME type to bytes".
pub open spec fn serialize_to_bytes_ensures(mime_type: MimeTypeRecord, output: Seq<u8>) -> bool {
    output == serialize_a_mime_type_to_bytes(mime_type)
}

/// Contract for `MimeType::essence(&self) -> Vec<u32>`.
pub open spec fn essence_ensures(mime_type: MimeTypeRecord, output: Seq<u32>) -> bool {
    output == essence(mime_type)
}

/// Contract for each §4.6 group predicate, `is_*_mime_type(&MimeType) ->
/// bool`: the result is the spec predicate of the same name.
pub open spec fn group_ensures(group: Group, mime_type: MimeTypeRecord, output: bool) -> bool {
    output == match group {
        Group::Image => is_image_mime_type(mime_type),
        Group::AudioOrVideo => is_audio_or_video_mime_type(mime_type),
        Group::Font => is_font_mime_type(mime_type),
        Group::ZipBased => is_zip_based_mime_type(mime_type),
        Group::Archive => is_archive_mime_type(mime_type),
        Group::Xml => is_xml_mime_type(mime_type),
        Group::Html => is_html_mime_type(mime_type),
        Group::Scriptable => is_scriptable_mime_type(mime_type),
        Group::JavaScript => is_javascript_mime_type(mime_type),
        Group::Json => is_json_mime_type(mime_type),
    }
}

/// The §4.6 MIME type groups, one per exec predicate.
pub enum Group {
    /// image MIME type
    Image,
    /// audio or video MIME type
    AudioOrVideo,
    /// font MIME type
    Font,
    /// ZIP-based MIME type
    ZipBased,
    /// archive MIME type
    Archive,
    /// XML MIME type
    Xml,
    /// HTML MIME type
    Html,
    /// scriptable MIME type
    Scriptable,
    /// JavaScript MIME type
    JavaScript,
    /// JSON MIME type
    Json,
}

/// Contract for `is_javascript_mime_type_essence_match(&[u32]) -> bool`.
pub open spec fn javascript_essence_match_ensures(s: Seq<u32>, output: bool) -> bool {
    output == is_javascript_mime_type_essence_match(s)
}

} // verus!
