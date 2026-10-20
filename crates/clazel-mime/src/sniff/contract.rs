//! Contracts the executable sniffing functions must be proven to meet.
//! Each exec function's `ensures` clause will be exactly one of these
//! predicates, so reviewing these (and [`super::spec`]) is enough to know
//! what the implementation guarantees. Byte sequences are `&[u8]`; MIME
//! types are viewed as [`MimeTypeRecord`](crate::mime_type::spec::MimeTypeRecord); `None` is undefined.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Contract for `pattern_matching(input, pattern, mask, ignored) -> bool`.
/// The precondition is the algorithm's assertion (§6 step 1).
pub open spec fn pattern_matching_requires(pattern: Seq<u8>, mask: Seq<u8>) -> bool {
    pattern.len() == mask.len()
}

/// Contract for `pattern_matching(input, pattern, mask, ignored) -> bool`.
pub open spec fn pattern_matching_ensures(input: Seq<u8>, pattern: Seq<u8>, mask: Seq<u8>, ignored: Ignored, output: bool) -> bool {
    output == pattern_matching(input, pattern, mask, ignored)
}

/// The four pattern matching algorithms of §6.1 to §6.4.
pub enum TypePattern {
    /// image type pattern matching algorithm (§6.1)
    Image,
    /// audio or video type pattern matching algorithm (§6.2)
    AudioOrVideo,
    /// font type pattern matching algorithm (§6.3)
    Font,
    /// archive type pattern matching algorithm (§6.4)
    Archive,
}

/// Contract for each `match_*_type_pattern(&[u8]) -> Option<MimeType>`.
pub open spec fn type_pattern_ensures(which: TypePattern, input: Seq<u8>, output: Option<crate::mime_type::spec::MimeTypeRecord>) -> bool {
    output == match which {
        TypePattern::Image => image_type_pattern_matching(input),
        TypePattern::AudioOrVideo => audio_or_video_type_pattern_matching(input),
        TypePattern::Font => font_type_pattern_matching(input),
        TypePattern::Archive => archive_type_pattern_matching(input),
    }
}

/// Contract for `check_for_apache_bug(&[u8]) -> bool`.
pub open spec fn check_for_apache_bug_ensures(supplied_type: Seq<u8>, output: bool) -> bool {
    output == check_for_apache_bug(supplied_type)
}

/// Contract for `distinguish_text_or_binary(&[u8]) -> MimeType` (§7.2).
pub open spec fn distinguish_text_or_binary_ensures(header: Seq<u8>, output: crate::mime_type::spec::MimeTypeRecord) -> bool {
    output == distinguish_text_or_binary(header)
}

/// Contract for `identify_unknown_mime_type(&[u8], bool) -> MimeType` (§7.1).
pub open spec fn identify_unknown_mime_type_ensures(header: Seq<u8>, sniff_scriptable: bool, output: crate::mime_type::spec::MimeTypeRecord) -> bool {
    output == identify_unknown_mime_type(header, sniff_scriptable)
}

/// Contract for `computed_mime_type(&Resource, bool) -> MimeType` (§7).
pub open spec fn computed_mime_type_ensures(resource: Resource, supported: bool, output: crate::mime_type::spec::MimeTypeRecord) -> bool {
    output == computed_mime_type(resource, supported)
}

} // verus!
