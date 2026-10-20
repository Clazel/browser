//! The pattern tables of MIME Sniffing §6.1–§6.4 and §7.1, as executable
//! code: one `row_matches` call per row of the spec's tables, in order,
//! each proven to be that row ("Execute the following steps for each row
//! row in the following table: 1. Let patternMatched be the result of the
//! pattern matching algorithm given input, [the row's first three
//! columns]. 2. If patternMatched is true, return the value in the fourth
//! column of row."). Generated from `spec.rs`'s rows; each function is
//! proven equal to `match_table` on its spec table, so a row that differs
//! from the spec fails verification.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;
use super::pattern::{mime_literal, row_matches};
use crate::mime_type::record::MimeType;

verus! {
/// The table in §6.1 (image type pattern matching algorithm).
pub fn match_image_table(input: &[u8]) -> (r: Option<MimeType>)
    ensures
        crate::mime_type::record::option_view(r) == match_table(input@, image_type_table(), 0),
{
    let ghost table = image_type_table();
    assert(table.len() == 8);
    // A Windows Icon signature.
    // 00 00 01 00 / FF FF FF FF / None. / image/x-icon
    let pattern: &[u8] = &[0x00u8, 0x00, 0x01, 0x00];
    let mask: &[u8] = &[0xFFu8, 0xFF, 0xFF, 0xFF];
    assert(pattern@ =~= table[0].pattern && mask@ =~= table[0].mask);
    if row_matches(input, pattern, mask, Ignored::None, Ghost(table), Ghost(0nat)) {
        let type_: &[u32] = &[0x69u32, 0x6D, 0x61, 0x67, 0x65];
        let subtype: &[u32] = &[0x78u32, 0x2D, 0x69, 0x63, 0x6F, 0x6E];
        assert(type_@ =~= table[0].computed.type_ && subtype@ =~= table[0].computed.subtype);
        return Some(mime_literal(type_, subtype));
    }
    // A Windows Cursor signature.
    // 00 00 02 00 / FF FF FF FF / None. / image/x-icon
    let pattern: &[u8] = &[0x00u8, 0x00, 0x02, 0x00];
    let mask: &[u8] = &[0xFFu8, 0xFF, 0xFF, 0xFF];
    assert(pattern@ =~= table[1].pattern && mask@ =~= table[1].mask);
    if row_matches(input, pattern, mask, Ignored::None, Ghost(table), Ghost(1nat)) {
        let type_: &[u32] = &[0x69u32, 0x6D, 0x61, 0x67, 0x65];
        let subtype: &[u32] = &[0x78u32, 0x2D, 0x69, 0x63, 0x6F, 0x6E];
        assert(type_@ =~= table[1].computed.type_ && subtype@ =~= table[1].computed.subtype);
        return Some(mime_literal(type_, subtype));
    }
    // The string "BM", a BMP signature.
    // 42 4D / FF FF / None. / image/bmp
    let pattern: &[u8] = &[0x42u8, 0x4D];
    let mask: &[u8] = &[0xFFu8, 0xFF];
    assert(pattern@ =~= table[2].pattern && mask@ =~= table[2].mask);
    if row_matches(input, pattern, mask, Ignored::None, Ghost(table), Ghost(2nat)) {
        let type_: &[u32] = &[0x69u32, 0x6D, 0x61, 0x67, 0x65];
        let subtype: &[u32] = &[0x62u32, 0x6D, 0x70];
        assert(type_@ =~= table[2].computed.type_ && subtype@ =~= table[2].computed.subtype);
        return Some(mime_literal(type_, subtype));
    }
    // The string "GIF87a", a GIF signature.
    // 47 49 46 38 37 61 / FF FF FF FF FF FF / None. / image/gif
    let pattern: &[u8] = &[0x47u8, 0x49, 0x46, 0x38, 0x37, 0x61];
    let mask: &[u8] = &[0xFFu8, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF];
    assert(pattern@ =~= table[3].pattern && mask@ =~= table[3].mask);
    if row_matches(input, pattern, mask, Ignored::None, Ghost(table), Ghost(3nat)) {
        let type_: &[u32] = &[0x69u32, 0x6D, 0x61, 0x67, 0x65];
        let subtype: &[u32] = &[0x67u32, 0x69, 0x66];
        assert(type_@ =~= table[3].computed.type_ && subtype@ =~= table[3].computed.subtype);
        return Some(mime_literal(type_, subtype));
    }
    // The string "GIF89a", a GIF signature.
    // 47 49 46 38 39 61 / FF FF FF FF FF FF / None. / image/gif
    let pattern: &[u8] = &[0x47u8, 0x49, 0x46, 0x38, 0x39, 0x61];
    let mask: &[u8] = &[0xFFu8, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF];
    assert(pattern@ =~= table[4].pattern && mask@ =~= table[4].mask);
    if row_matches(input, pattern, mask, Ignored::None, Ghost(table), Ghost(4nat)) {
        let type_: &[u32] = &[0x69u32, 0x6D, 0x61, 0x67, 0x65];
        let subtype: &[u32] = &[0x67u32, 0x69, 0x66];
        assert(type_@ =~= table[4].computed.type_ && subtype@ =~= table[4].computed.subtype);
        return Some(mime_literal(type_, subtype));
    }
    // The string "RIFF" followed by four bytes followed by the string "WEBPVP".
    // 52 49 46 46 00 00 00 00 57 45 42 50 56 50 / FF FF FF FF 00 00 00 00 FF FF FF FF FF FF / None. / image/webp
    let pattern: &[u8] = &[0x52u8, 0x49, 0x46, 0x46, 0x00, 0x00, 0x00, 0x00, 0x57, 0x45, 0x42, 0x50, 0x56, 0x50];
    let mask: &[u8] = &[0xFFu8, 0xFF, 0xFF, 0xFF, 0x00, 0x00, 0x00, 0x00, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF];
    assert(pattern@ =~= table[5].pattern && mask@ =~= table[5].mask);
    if row_matches(input, pattern, mask, Ignored::None, Ghost(table), Ghost(5nat)) {
        let type_: &[u32] = &[0x69u32, 0x6D, 0x61, 0x67, 0x65];
        let subtype: &[u32] = &[0x77u32, 0x65, 0x62, 0x70];
        assert(type_@ =~= table[5].computed.type_ && subtype@ =~= table[5].computed.subtype);
        return Some(mime_literal(type_, subtype));
    }
    // An error-checking byte followed by the string "PNG" followed by CR LF SUB LF, the PNG signature.
    // 89 50 4E 47 0D 0A 1A 0A / FF FF FF FF FF FF FF FF / None. / image/png
    let pattern: &[u8] = &[0x89u8, 0x50, 0x4E, 0x47, 0x0D, 0x0A, 0x1A, 0x0A];
    let mask: &[u8] = &[0xFFu8, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF];
    assert(pattern@ =~= table[6].pattern && mask@ =~= table[6].mask);
    if row_matches(input, pattern, mask, Ignored::None, Ghost(table), Ghost(6nat)) {
        let type_: &[u32] = &[0x69u32, 0x6D, 0x61, 0x67, 0x65];
        let subtype: &[u32] = &[0x70u32, 0x6E, 0x67];
        assert(type_@ =~= table[6].computed.type_ && subtype@ =~= table[6].computed.subtype);
        return Some(mime_literal(type_, subtype));
    }
    // The JPEG Start of Image marker followed by the indicator byte of another marker.
    // FF D8 FF / FF FF FF / None. / image/jpeg
    let pattern: &[u8] = &[0xFFu8, 0xD8, 0xFF];
    let mask: &[u8] = &[0xFFu8, 0xFF, 0xFF];
    assert(pattern@ =~= table[7].pattern && mask@ =~= table[7].mask);
    if row_matches(input, pattern, mask, Ignored::None, Ghost(table), Ghost(7nat)) {
        let type_: &[u32] = &[0x69u32, 0x6D, 0x61, 0x67, 0x65];
        let subtype: &[u32] = &[0x6Au32, 0x70, 0x65, 0x67];
        assert(type_@ =~= table[7].computed.type_ && subtype@ =~= table[7].computed.subtype);
        return Some(mime_literal(type_, subtype));
    }
    // No row matched.
    None
}

/// The table in §6.2 (audio or video type pattern matching algorithm), step 1.
pub fn match_audio_or_video_table(input: &[u8]) -> (r: Option<MimeType>)
    ensures
        crate::mime_type::record::option_view(r) == match_table(input@, audio_or_video_type_table(), 0),
{
    let ghost table = audio_or_video_type_table();
    assert(table.len() == 6);
    // The string "FORM" followed by four bytes followed by the string "AIFF", the AIFF signature.
    // 46 4F 52 4D 00 00 00 00 41 49 46 46 / FF FF FF FF 00 00 00 00 FF FF FF FF / None. / audio/aiff
    let pattern: &[u8] = &[0x46u8, 0x4F, 0x52, 0x4D, 0x00, 0x00, 0x00, 0x00, 0x41, 0x49, 0x46, 0x46];
    let mask: &[u8] = &[0xFFu8, 0xFF, 0xFF, 0xFF, 0x00, 0x00, 0x00, 0x00, 0xFF, 0xFF, 0xFF, 0xFF];
    assert(pattern@ =~= table[0].pattern && mask@ =~= table[0].mask);
    if row_matches(input, pattern, mask, Ignored::None, Ghost(table), Ghost(0nat)) {
        let type_: &[u32] = &[0x61u32, 0x75, 0x64, 0x69, 0x6F];
        let subtype: &[u32] = &[0x61u32, 0x69, 0x66, 0x66];
        assert(type_@ =~= table[0].computed.type_ && subtype@ =~= table[0].computed.subtype);
        return Some(mime_literal(type_, subtype));
    }
    // The string "ID3", the ID3v2-tagged MP3 signature.
    // 49 44 33 / FF FF FF / None. / audio/mpeg
    let pattern: &[u8] = &[0x49u8, 0x44, 0x33];
    let mask: &[u8] = &[0xFFu8, 0xFF, 0xFF];
    assert(pattern@ =~= table[1].pattern && mask@ =~= table[1].mask);
    if row_matches(input, pattern, mask, Ignored::None, Ghost(table), Ghost(1nat)) {
        let type_: &[u32] = &[0x61u32, 0x75, 0x64, 0x69, 0x6F];
        let subtype: &[u32] = &[0x6Du32, 0x70, 0x65, 0x67];
        assert(type_@ =~= table[1].computed.type_ && subtype@ =~= table[1].computed.subtype);
        return Some(mime_literal(type_, subtype));
    }
    // The string "OggS" followed by NUL, the Ogg container signature.
    // 4F 67 67 53 00 / FF FF FF FF FF / None. / application/ogg
    let pattern: &[u8] = &[0x4Fu8, 0x67, 0x67, 0x53, 0x00];
    let mask: &[u8] = &[0xFFu8, 0xFF, 0xFF, 0xFF, 0xFF];
    assert(pattern@ =~= table[2].pattern && mask@ =~= table[2].mask);
    if row_matches(input, pattern, mask, Ignored::None, Ghost(table), Ghost(2nat)) {
        let type_: &[u32] = &[0x61u32, 0x70, 0x70, 0x6C, 0x69, 0x63, 0x61, 0x74, 0x69, 0x6F, 0x6E];
        let subtype: &[u32] = &[0x6Fu32, 0x67, 0x67];
        assert(type_@ =~= table[2].computed.type_ && subtype@ =~= table[2].computed.subtype);
        return Some(mime_literal(type_, subtype));
    }
    // The string "MThd" followed by four bytes representing the number 6 in 32 bits (big-endian), the MIDI signature.
    // 4D 54 68 64 00 00 00 06 / FF FF FF FF FF FF FF FF / None. / audio/midi
    let pattern: &[u8] = &[0x4Du8, 0x54, 0x68, 0x64, 0x00, 0x00, 0x00, 0x06];
    let mask: &[u8] = &[0xFFu8, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF];
    assert(pattern@ =~= table[3].pattern && mask@ =~= table[3].mask);
    if row_matches(input, pattern, mask, Ignored::None, Ghost(table), Ghost(3nat)) {
        let type_: &[u32] = &[0x61u32, 0x75, 0x64, 0x69, 0x6F];
        let subtype: &[u32] = &[0x6Du32, 0x69, 0x64, 0x69];
        assert(type_@ =~= table[3].computed.type_ && subtype@ =~= table[3].computed.subtype);
        return Some(mime_literal(type_, subtype));
    }
    // The string "RIFF" followed by four bytes followed by the string "AVI ", the AVI signature.
    // 52 49 46 46 00 00 00 00 41 56 49 20 / FF FF FF FF 00 00 00 00 FF FF FF FF / None. / video/avi
    let pattern: &[u8] = &[0x52u8, 0x49, 0x46, 0x46, 0x00, 0x00, 0x00, 0x00, 0x41, 0x56, 0x49, 0x20];
    let mask: &[u8] = &[0xFFu8, 0xFF, 0xFF, 0xFF, 0x00, 0x00, 0x00, 0x00, 0xFF, 0xFF, 0xFF, 0xFF];
    assert(pattern@ =~= table[4].pattern && mask@ =~= table[4].mask);
    if row_matches(input, pattern, mask, Ignored::None, Ghost(table), Ghost(4nat)) {
        let type_: &[u32] = &[0x76u32, 0x69, 0x64, 0x65, 0x6F];
        let subtype: &[u32] = &[0x61u32, 0x76, 0x69];
        assert(type_@ =~= table[4].computed.type_ && subtype@ =~= table[4].computed.subtype);
        return Some(mime_literal(type_, subtype));
    }
    // The string "RIFF" followed by four bytes followed by the string "WAVE", the WAVE signature.
    // 52 49 46 46 00 00 00 00 57 41 56 45 / FF FF FF FF 00 00 00 00 FF FF FF FF / None. / audio/wave
    let pattern: &[u8] = &[0x52u8, 0x49, 0x46, 0x46, 0x00, 0x00, 0x00, 0x00, 0x57, 0x41, 0x56, 0x45];
    let mask: &[u8] = &[0xFFu8, 0xFF, 0xFF, 0xFF, 0x00, 0x00, 0x00, 0x00, 0xFF, 0xFF, 0xFF, 0xFF];
    assert(pattern@ =~= table[5].pattern && mask@ =~= table[5].mask);
    if row_matches(input, pattern, mask, Ignored::None, Ghost(table), Ghost(5nat)) {
        let type_: &[u32] = &[0x61u32, 0x75, 0x64, 0x69, 0x6F];
        let subtype: &[u32] = &[0x77u32, 0x61, 0x76, 0x65];
        assert(type_@ =~= table[5].computed.type_ && subtype@ =~= table[5].computed.subtype);
        return Some(mime_literal(type_, subtype));
    }
    // No row matched.
    None
}

/// The table in §6.3 (font type pattern matching algorithm).
pub fn match_font_table(input: &[u8]) -> (r: Option<MimeType>)
    ensures
        crate::mime_type::record::option_view(r) == match_table(input@, font_type_table(), 0),
{
    let ghost table = font_type_table();
    assert(table.len() == 6);
    // 34 bytes followed by the string "LP", the Embedded OpenType signature.
    // 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 4C 50 / 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 FF FF / None. / application/vnd.ms-fontobject
    let pattern: &[u8] = &[0x00u8, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x4C, 0x50];
    let mask: &[u8] = &[0x00u8, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xFF, 0xFF];
    assert(pattern@ =~= table[0].pattern && mask@ =~= table[0].mask);
    if row_matches(input, pattern, mask, Ignored::None, Ghost(table), Ghost(0nat)) {
        let type_: &[u32] = &[0x61u32, 0x70, 0x70, 0x6C, 0x69, 0x63, 0x61, 0x74, 0x69, 0x6F, 0x6E];
        let subtype: &[u32] = &[0x76u32, 0x6E, 0x64, 0x2E, 0x6D, 0x73, 0x2D, 0x66, 0x6F, 0x6E, 0x74, 0x6F, 0x62, 0x6A, 0x65, 0x63, 0x74];
        assert(type_@ =~= table[0].computed.type_ && subtype@ =~= table[0].computed.subtype);
        return Some(mime_literal(type_, subtype));
    }
    // 4 bytes representing the version number 1.0, a TrueType signature.
    // 00 01 00 00 / FF FF FF FF / None. / font/ttf
    let pattern: &[u8] = &[0x00u8, 0x01, 0x00, 0x00];
    let mask: &[u8] = &[0xFFu8, 0xFF, 0xFF, 0xFF];
    assert(pattern@ =~= table[1].pattern && mask@ =~= table[1].mask);
    if row_matches(input, pattern, mask, Ignored::None, Ghost(table), Ghost(1nat)) {
        let type_: &[u32] = &[0x66u32, 0x6F, 0x6E, 0x74];
        let subtype: &[u32] = &[0x74u32, 0x74, 0x66];
        assert(type_@ =~= table[1].computed.type_ && subtype@ =~= table[1].computed.subtype);
        return Some(mime_literal(type_, subtype));
    }
    // The string "OTTO", the OpenType signature.
    // 4F 54 54 4F / FF FF FF FF / None. / font/otf
    let pattern: &[u8] = &[0x4Fu8, 0x54, 0x54, 0x4F];
    let mask: &[u8] = &[0xFFu8, 0xFF, 0xFF, 0xFF];
    assert(pattern@ =~= table[2].pattern && mask@ =~= table[2].mask);
    if row_matches(input, pattern, mask, Ignored::None, Ghost(table), Ghost(2nat)) {
        let type_: &[u32] = &[0x66u32, 0x6F, 0x6E, 0x74];
        let subtype: &[u32] = &[0x6Fu32, 0x74, 0x66];
        assert(type_@ =~= table[2].computed.type_ && subtype@ =~= table[2].computed.subtype);
        return Some(mime_literal(type_, subtype));
    }
    // The string "ttcf", the TrueType Collection signature.
    // 74 74 63 66 / FF FF FF FF / None. / font/collection
    let pattern: &[u8] = &[0x74u8, 0x74, 0x63, 0x66];
    let mask: &[u8] = &[0xFFu8, 0xFF, 0xFF, 0xFF];
    assert(pattern@ =~= table[3].pattern && mask@ =~= table[3].mask);
    if row_matches(input, pattern, mask, Ignored::None, Ghost(table), Ghost(3nat)) {
        let type_: &[u32] = &[0x66u32, 0x6F, 0x6E, 0x74];
        let subtype: &[u32] = &[0x63u32, 0x6F, 0x6C, 0x6C, 0x65, 0x63, 0x74, 0x69, 0x6F, 0x6E];
        assert(type_@ =~= table[3].computed.type_ && subtype@ =~= table[3].computed.subtype);
        return Some(mime_literal(type_, subtype));
    }
    // The string "wOFF", the Web Open Font Format 1.0 signature.
    // 77 4F 46 46 / FF FF FF FF / None. / font/woff
    let pattern: &[u8] = &[0x77u8, 0x4F, 0x46, 0x46];
    let mask: &[u8] = &[0xFFu8, 0xFF, 0xFF, 0xFF];
    assert(pattern@ =~= table[4].pattern && mask@ =~= table[4].mask);
    if row_matches(input, pattern, mask, Ignored::None, Ghost(table), Ghost(4nat)) {
        let type_: &[u32] = &[0x66u32, 0x6F, 0x6E, 0x74];
        let subtype: &[u32] = &[0x77u32, 0x6F, 0x66, 0x66];
        assert(type_@ =~= table[4].computed.type_ && subtype@ =~= table[4].computed.subtype);
        return Some(mime_literal(type_, subtype));
    }
    // The string "wOF2", the Web Open Font Format 2.0 signature.
    // 77 4F 46 32 / FF FF FF FF / None. / font/woff2
    let pattern: &[u8] = &[0x77u8, 0x4F, 0x46, 0x32];
    let mask: &[u8] = &[0xFFu8, 0xFF, 0xFF, 0xFF];
    assert(pattern@ =~= table[5].pattern && mask@ =~= table[5].mask);
    if row_matches(input, pattern, mask, Ignored::None, Ghost(table), Ghost(5nat)) {
        let type_: &[u32] = &[0x66u32, 0x6F, 0x6E, 0x74];
        let subtype: &[u32] = &[0x77u32, 0x6F, 0x66, 0x66, 0x32];
        assert(type_@ =~= table[5].computed.type_ && subtype@ =~= table[5].computed.subtype);
        return Some(mime_literal(type_, subtype));
    }
    // No row matched.
    None
}

/// The table in §6.4 (archive type pattern matching algorithm).
pub fn match_archive_table(input: &[u8]) -> (r: Option<MimeType>)
    ensures
        crate::mime_type::record::option_view(r) == match_table(input@, archive_type_table(), 0),
{
    let ghost table = archive_type_table();
    assert(table.len() == 3);
    // The GZIP archive signature.
    // 1F 8B 08 / FF FF FF / None. / application/x-gzip
    let pattern: &[u8] = &[0x1Fu8, 0x8B, 0x08];
    let mask: &[u8] = &[0xFFu8, 0xFF, 0xFF];
    assert(pattern@ =~= table[0].pattern && mask@ =~= table[0].mask);
    if row_matches(input, pattern, mask, Ignored::None, Ghost(table), Ghost(0nat)) {
        let type_: &[u32] = &[0x61u32, 0x70, 0x70, 0x6C, 0x69, 0x63, 0x61, 0x74, 0x69, 0x6F, 0x6E];
        let subtype: &[u32] = &[0x78u32, 0x2D, 0x67, 0x7A, 0x69, 0x70];
        assert(type_@ =~= table[0].computed.type_ && subtype@ =~= table[0].computed.subtype);
        return Some(mime_literal(type_, subtype));
    }
    // The string "PK" followed by ETX EOT, the ZIP archive signature.
    // 50 4B 03 04 / FF FF FF FF / None. / application/zip
    let pattern: &[u8] = &[0x50u8, 0x4B, 0x03, 0x04];
    let mask: &[u8] = &[0xFFu8, 0xFF, 0xFF, 0xFF];
    assert(pattern@ =~= table[1].pattern && mask@ =~= table[1].mask);
    if row_matches(input, pattern, mask, Ignored::None, Ghost(table), Ghost(1nat)) {
        let type_: &[u32] = &[0x61u32, 0x70, 0x70, 0x6C, 0x69, 0x63, 0x61, 0x74, 0x69, 0x6F, 0x6E];
        let subtype: &[u32] = &[0x7Au32, 0x69, 0x70];
        assert(type_@ =~= table[1].computed.type_ && subtype@ =~= table[1].computed.subtype);
        return Some(mime_literal(type_, subtype));
    }
    // The string "Rar!" followed by SUB BEL NUL, the RAR 4.x archive signature.
    // 52 61 72 21 1A 07 00 / FF FF FF FF FF FF FF / None. / application/x-rar-compressed
    let pattern: &[u8] = &[0x52u8, 0x61, 0x72, 0x21, 0x1A, 0x07, 0x00];
    let mask: &[u8] = &[0xFFu8, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF];
    assert(pattern@ =~= table[2].pattern && mask@ =~= table[2].mask);
    if row_matches(input, pattern, mask, Ignored::None, Ghost(table), Ghost(2nat)) {
        let type_: &[u32] = &[0x61u32, 0x70, 0x70, 0x6C, 0x69, 0x63, 0x61, 0x74, 0x69, 0x6F, 0x6E];
        let subtype: &[u32] = &[0x78u32, 0x2D, 0x72, 0x61, 0x72, 0x2D, 0x63, 0x6F, 0x6D, 0x70, 0x72, 0x65, 0x73, 0x73, 0x65, 0x64];
        assert(type_@ =~= table[2].computed.type_ && subtype@ =~= table[2].computed.subtype);
        return Some(mime_literal(type_, subtype));
    }
    // No row matched.
    None
}

/// The table in §7.1 step 1 (rules for identifying an unknown MIME type).
pub fn match_unknown_scriptable_table(input: &[u8]) -> (r: Option<MimeType>)
    ensures
        crate::mime_type::record::option_view(r) == match_table(input@, unknown_scriptable_table(), 0),
{
    let ghost table = unknown_scriptable_table();
    assert(table.len() == 36);
    // The case-insensitive string "<!DOCTYPE HTML" followed by a tag-terminating byte. (TT = 0x20)
    // 3C 21 44 4F 43 54 59 50 45 20 48 54 4D 4C TT / FF FF DF DF DF DF DF DF DF FF DF DF DF DF FF / Whitespace bytes. / text/html
    let pattern: &[u8] = &[0x3Cu8, 0x21, 0x44, 0x4F, 0x43, 0x54, 0x59, 0x50, 0x45, 0x20, 0x48, 0x54, 0x4D, 0x4C, 0x20];
    let mask: &[u8] = &[0xFFu8, 0xFF, 0xDF, 0xDF, 0xDF, 0xDF, 0xDF, 0xDF, 0xDF, 0xFF, 0xDF, 0xDF, 0xDF, 0xDF, 0xFF];
    assert(pattern@ =~= table[0].pattern && mask@ =~= table[0].mask);
    if row_matches(input, pattern, mask, Ignored::WhitespaceBytes, Ghost(table), Ghost(0nat)) {
        let type_: &[u32] = &[0x74u32, 0x65, 0x78, 0x74];
        let subtype: &[u32] = &[0x68u32, 0x74, 0x6D, 0x6C];
        assert(type_@ =~= table[0].computed.type_ && subtype@ =~= table[0].computed.subtype);
        return Some(mime_literal(type_, subtype));
    }
    // The case-insensitive string "<!DOCTYPE HTML" followed by a tag-terminating byte. (TT = 0x3E)
    // 3C 21 44 4F 43 54 59 50 45 20 48 54 4D 4C TT / FF FF DF DF DF DF DF DF DF FF DF DF DF DF FF / Whitespace bytes. / text/html
    let pattern: &[u8] = &[0x3Cu8, 0x21, 0x44, 0x4F, 0x43, 0x54, 0x59, 0x50, 0x45, 0x20, 0x48, 0x54, 0x4D, 0x4C, 0x3E];
    let mask: &[u8] = &[0xFFu8, 0xFF, 0xDF, 0xDF, 0xDF, 0xDF, 0xDF, 0xDF, 0xDF, 0xFF, 0xDF, 0xDF, 0xDF, 0xDF, 0xFF];
    assert(pattern@ =~= table[1].pattern && mask@ =~= table[1].mask);
    if row_matches(input, pattern, mask, Ignored::WhitespaceBytes, Ghost(table), Ghost(1nat)) {
        let type_: &[u32] = &[0x74u32, 0x65, 0x78, 0x74];
        let subtype: &[u32] = &[0x68u32, 0x74, 0x6D, 0x6C];
        assert(type_@ =~= table[1].computed.type_ && subtype@ =~= table[1].computed.subtype);
        return Some(mime_literal(type_, subtype));
    }
    // The case-insensitive string "<HTML" followed by a tag-terminating byte. (TT = 0x20)
    // 3C 48 54 4D 4C TT / FF DF DF DF DF FF / Whitespace bytes. / text/html
    let pattern: &[u8] = &[0x3Cu8, 0x48, 0x54, 0x4D, 0x4C, 0x20];
    let mask: &[u8] = &[0xFFu8, 0xDF, 0xDF, 0xDF, 0xDF, 0xFF];
    assert(pattern@ =~= table[2].pattern && mask@ =~= table[2].mask);
    if row_matches(input, pattern, mask, Ignored::WhitespaceBytes, Ghost(table), Ghost(2nat)) {
        let type_: &[u32] = &[0x74u32, 0x65, 0x78, 0x74];
        let subtype: &[u32] = &[0x68u32, 0x74, 0x6D, 0x6C];
        assert(type_@ =~= table[2].computed.type_ && subtype@ =~= table[2].computed.subtype);
        return Some(mime_literal(type_, subtype));
    }
    // The case-insensitive string "<HTML" followed by a tag-terminating byte. (TT = 0x3E)
    // 3C 48 54 4D 4C TT / FF DF DF DF DF FF / Whitespace bytes. / text/html
    let pattern: &[u8] = &[0x3Cu8, 0x48, 0x54, 0x4D, 0x4C, 0x3E];
    let mask: &[u8] = &[0xFFu8, 0xDF, 0xDF, 0xDF, 0xDF, 0xFF];
    assert(pattern@ =~= table[3].pattern && mask@ =~= table[3].mask);
    if row_matches(input, pattern, mask, Ignored::WhitespaceBytes, Ghost(table), Ghost(3nat)) {
        let type_: &[u32] = &[0x74u32, 0x65, 0x78, 0x74];
        let subtype: &[u32] = &[0x68u32, 0x74, 0x6D, 0x6C];
        assert(type_@ =~= table[3].computed.type_ && subtype@ =~= table[3].computed.subtype);
        return Some(mime_literal(type_, subtype));
    }
    // The case-insensitive string "<HEAD" followed by a tag-terminating byte. (TT = 0x20)
    // 3C 48 45 41 44 TT / FF DF DF DF DF FF / Whitespace bytes. / text/html
    let pattern: &[u8] = &[0x3Cu8, 0x48, 0x45, 0x41, 0x44, 0x20];
    let mask: &[u8] = &[0xFFu8, 0xDF, 0xDF, 0xDF, 0xDF, 0xFF];
    assert(pattern@ =~= table[4].pattern && mask@ =~= table[4].mask);
    if row_matches(input, pattern, mask, Ignored::WhitespaceBytes, Ghost(table), Ghost(4nat)) {
        let type_: &[u32] = &[0x74u32, 0x65, 0x78, 0x74];
        let subtype: &[u32] = &[0x68u32, 0x74, 0x6D, 0x6C];
        assert(type_@ =~= table[4].computed.type_ && subtype@ =~= table[4].computed.subtype);
        return Some(mime_literal(type_, subtype));
    }
    // The case-insensitive string "<HEAD" followed by a tag-terminating byte. (TT = 0x3E)
    // 3C 48 45 41 44 TT / FF DF DF DF DF FF / Whitespace bytes. / text/html
    let pattern: &[u8] = &[0x3Cu8, 0x48, 0x45, 0x41, 0x44, 0x3E];
    let mask: &[u8] = &[0xFFu8, 0xDF, 0xDF, 0xDF, 0xDF, 0xFF];
    assert(pattern@ =~= table[5].pattern && mask@ =~= table[5].mask);
    if row_matches(input, pattern, mask, Ignored::WhitespaceBytes, Ghost(table), Ghost(5nat)) {
        let type_: &[u32] = &[0x74u32, 0x65, 0x78, 0x74];
        let subtype: &[u32] = &[0x68u32, 0x74, 0x6D, 0x6C];
        assert(type_@ =~= table[5].computed.type_ && subtype@ =~= table[5].computed.subtype);
        return Some(mime_literal(type_, subtype));
    }
    // The case-insensitive string "<SCRIPT" followed by a tag-terminating byte. (TT = 0x20)
    // 3C 53 43 52 49 50 54 TT / FF DF DF DF DF DF DF FF / Whitespace bytes. / text/html
    let pattern: &[u8] = &[0x3Cu8, 0x53, 0x43, 0x52, 0x49, 0x50, 0x54, 0x20];
    let mask: &[u8] = &[0xFFu8, 0xDF, 0xDF, 0xDF, 0xDF, 0xDF, 0xDF, 0xFF];
    assert(pattern@ =~= table[6].pattern && mask@ =~= table[6].mask);
    if row_matches(input, pattern, mask, Ignored::WhitespaceBytes, Ghost(table), Ghost(6nat)) {
        let type_: &[u32] = &[0x74u32, 0x65, 0x78, 0x74];
        let subtype: &[u32] = &[0x68u32, 0x74, 0x6D, 0x6C];
        assert(type_@ =~= table[6].computed.type_ && subtype@ =~= table[6].computed.subtype);
        return Some(mime_literal(type_, subtype));
    }
    // The case-insensitive string "<SCRIPT" followed by a tag-terminating byte. (TT = 0x3E)
    // 3C 53 43 52 49 50 54 TT / FF DF DF DF DF DF DF FF / Whitespace bytes. / text/html
    let pattern: &[u8] = &[0x3Cu8, 0x53, 0x43, 0x52, 0x49, 0x50, 0x54, 0x3E];
    let mask: &[u8] = &[0xFFu8, 0xDF, 0xDF, 0xDF, 0xDF, 0xDF, 0xDF, 0xFF];
    assert(pattern@ =~= table[7].pattern && mask@ =~= table[7].mask);
    if row_matches(input, pattern, mask, Ignored::WhitespaceBytes, Ghost(table), Ghost(7nat)) {
        let type_: &[u32] = &[0x74u32, 0x65, 0x78, 0x74];
        let subtype: &[u32] = &[0x68u32, 0x74, 0x6D, 0x6C];
        assert(type_@ =~= table[7].computed.type_ && subtype@ =~= table[7].computed.subtype);
        return Some(mime_literal(type_, subtype));
    }
    // The case-insensitive string "<IFRAME" followed by a tag-terminating byte. (TT = 0x20)
    // 3C 49 46 52 41 4D 45 TT / FF DF DF DF DF DF DF FF / Whitespace bytes. / text/html
    let pattern: &[u8] = &[0x3Cu8, 0x49, 0x46, 0x52, 0x41, 0x4D, 0x45, 0x20];
    let mask: &[u8] = &[0xFFu8, 0xDF, 0xDF, 0xDF, 0xDF, 0xDF, 0xDF, 0xFF];
    assert(pattern@ =~= table[8].pattern && mask@ =~= table[8].mask);
    if row_matches(input, pattern, mask, Ignored::WhitespaceBytes, Ghost(table), Ghost(8nat)) {
        let type_: &[u32] = &[0x74u32, 0x65, 0x78, 0x74];
        let subtype: &[u32] = &[0x68u32, 0x74, 0x6D, 0x6C];
        assert(type_@ =~= table[8].computed.type_ && subtype@ =~= table[8].computed.subtype);
        return Some(mime_literal(type_, subtype));
    }
    // The case-insensitive string "<IFRAME" followed by a tag-terminating byte. (TT = 0x3E)
    // 3C 49 46 52 41 4D 45 TT / FF DF DF DF DF DF DF FF / Whitespace bytes. / text/html
    let pattern: &[u8] = &[0x3Cu8, 0x49, 0x46, 0x52, 0x41, 0x4D, 0x45, 0x3E];
    let mask: &[u8] = &[0xFFu8, 0xDF, 0xDF, 0xDF, 0xDF, 0xDF, 0xDF, 0xFF];
    assert(pattern@ =~= table[9].pattern && mask@ =~= table[9].mask);
    if row_matches(input, pattern, mask, Ignored::WhitespaceBytes, Ghost(table), Ghost(9nat)) {
        let type_: &[u32] = &[0x74u32, 0x65, 0x78, 0x74];
        let subtype: &[u32] = &[0x68u32, 0x74, 0x6D, 0x6C];
        assert(type_@ =~= table[9].computed.type_ && subtype@ =~= table[9].computed.subtype);
        return Some(mime_literal(type_, subtype));
    }
    // The case-insensitive string "<H1" followed by a tag-terminating byte. (TT = 0x20)
    // 3C 48 31 TT / FF DF FF FF / Whitespace bytes. / text/html
    let pattern: &[u8] = &[0x3Cu8, 0x48, 0x31, 0x20];
    let mask: &[u8] = &[0xFFu8, 0xDF, 0xFF, 0xFF];
    assert(pattern@ =~= table[10].pattern && mask@ =~= table[10].mask);
    if row_matches(input, pattern, mask, Ignored::WhitespaceBytes, Ghost(table), Ghost(10nat)) {
        let type_: &[u32] = &[0x74u32, 0x65, 0x78, 0x74];
        let subtype: &[u32] = &[0x68u32, 0x74, 0x6D, 0x6C];
        assert(type_@ =~= table[10].computed.type_ && subtype@ =~= table[10].computed.subtype);
        return Some(mime_literal(type_, subtype));
    }
    // The case-insensitive string "<H1" followed by a tag-terminating byte. (TT = 0x3E)
    // 3C 48 31 TT / FF DF FF FF / Whitespace bytes. / text/html
    let pattern: &[u8] = &[0x3Cu8, 0x48, 0x31, 0x3E];
    let mask: &[u8] = &[0xFFu8, 0xDF, 0xFF, 0xFF];
    assert(pattern@ =~= table[11].pattern && mask@ =~= table[11].mask);
    if row_matches(input, pattern, mask, Ignored::WhitespaceBytes, Ghost(table), Ghost(11nat)) {
        let type_: &[u32] = &[0x74u32, 0x65, 0x78, 0x74];
        let subtype: &[u32] = &[0x68u32, 0x74, 0x6D, 0x6C];
        assert(type_@ =~= table[11].computed.type_ && subtype@ =~= table[11].computed.subtype);
        return Some(mime_literal(type_, subtype));
    }
    // The case-insensitive string "<DIV" followed by a tag-terminating byte. (TT = 0x20)
    // 3C 44 49 56 TT / FF DF DF DF FF / Whitespace bytes. / text/html
    let pattern: &[u8] = &[0x3Cu8, 0x44, 0x49, 0x56, 0x20];
    let mask: &[u8] = &[0xFFu8, 0xDF, 0xDF, 0xDF, 0xFF];
    assert(pattern@ =~= table[12].pattern && mask@ =~= table[12].mask);
    if row_matches(input, pattern, mask, Ignored::WhitespaceBytes, Ghost(table), Ghost(12nat)) {
        let type_: &[u32] = &[0x74u32, 0x65, 0x78, 0x74];
        let subtype: &[u32] = &[0x68u32, 0x74, 0x6D, 0x6C];
        assert(type_@ =~= table[12].computed.type_ && subtype@ =~= table[12].computed.subtype);
        return Some(mime_literal(type_, subtype));
    }
    // The case-insensitive string "<DIV" followed by a tag-terminating byte. (TT = 0x3E)
    // 3C 44 49 56 TT / FF DF DF DF FF / Whitespace bytes. / text/html
    let pattern: &[u8] = &[0x3Cu8, 0x44, 0x49, 0x56, 0x3E];
    let mask: &[u8] = &[0xFFu8, 0xDF, 0xDF, 0xDF, 0xFF];
    assert(pattern@ =~= table[13].pattern && mask@ =~= table[13].mask);
    if row_matches(input, pattern, mask, Ignored::WhitespaceBytes, Ghost(table), Ghost(13nat)) {
        let type_: &[u32] = &[0x74u32, 0x65, 0x78, 0x74];
        let subtype: &[u32] = &[0x68u32, 0x74, 0x6D, 0x6C];
        assert(type_@ =~= table[13].computed.type_ && subtype@ =~= table[13].computed.subtype);
        return Some(mime_literal(type_, subtype));
    }
    // The case-insensitive string "<FONT" followed by a tag-terminating byte. (TT = 0x20)
    // 3C 46 4F 4E 54 TT / FF DF DF DF DF FF / Whitespace bytes. / text/html
    let pattern: &[u8] = &[0x3Cu8, 0x46, 0x4F, 0x4E, 0x54, 0x20];
    let mask: &[u8] = &[0xFFu8, 0xDF, 0xDF, 0xDF, 0xDF, 0xFF];
    assert(pattern@ =~= table[14].pattern && mask@ =~= table[14].mask);
    if row_matches(input, pattern, mask, Ignored::WhitespaceBytes, Ghost(table), Ghost(14nat)) {
        let type_: &[u32] = &[0x74u32, 0x65, 0x78, 0x74];
        let subtype: &[u32] = &[0x68u32, 0x74, 0x6D, 0x6C];
        assert(type_@ =~= table[14].computed.type_ && subtype@ =~= table[14].computed.subtype);
        return Some(mime_literal(type_, subtype));
    }
    // The case-insensitive string "<FONT" followed by a tag-terminating byte. (TT = 0x3E)
    // 3C 46 4F 4E 54 TT / FF DF DF DF DF FF / Whitespace bytes. / text/html
    let pattern: &[u8] = &[0x3Cu8, 0x46, 0x4F, 0x4E, 0x54, 0x3E];
    let mask: &[u8] = &[0xFFu8, 0xDF, 0xDF, 0xDF, 0xDF, 0xFF];
    assert(pattern@ =~= table[15].pattern && mask@ =~= table[15].mask);
    if row_matches(input, pattern, mask, Ignored::WhitespaceBytes, Ghost(table), Ghost(15nat)) {
        let type_: &[u32] = &[0x74u32, 0x65, 0x78, 0x74];
        let subtype: &[u32] = &[0x68u32, 0x74, 0x6D, 0x6C];
        assert(type_@ =~= table[15].computed.type_ && subtype@ =~= table[15].computed.subtype);
        return Some(mime_literal(type_, subtype));
    }
    // The case-insensitive string "<TABLE" followed by a tag-terminating byte. (TT = 0x20)
    // 3C 54 41 42 4C 45 TT / FF DF DF DF DF DF FF / Whitespace bytes. / text/html
    let pattern: &[u8] = &[0x3Cu8, 0x54, 0x41, 0x42, 0x4C, 0x45, 0x20];
    let mask: &[u8] = &[0xFFu8, 0xDF, 0xDF, 0xDF, 0xDF, 0xDF, 0xFF];
    assert(pattern@ =~= table[16].pattern && mask@ =~= table[16].mask);
    if row_matches(input, pattern, mask, Ignored::WhitespaceBytes, Ghost(table), Ghost(16nat)) {
        let type_: &[u32] = &[0x74u32, 0x65, 0x78, 0x74];
        let subtype: &[u32] = &[0x68u32, 0x74, 0x6D, 0x6C];
        assert(type_@ =~= table[16].computed.type_ && subtype@ =~= table[16].computed.subtype);
        return Some(mime_literal(type_, subtype));
    }
    // The case-insensitive string "<TABLE" followed by a tag-terminating byte. (TT = 0x3E)
    // 3C 54 41 42 4C 45 TT / FF DF DF DF DF DF FF / Whitespace bytes. / text/html
    let pattern: &[u8] = &[0x3Cu8, 0x54, 0x41, 0x42, 0x4C, 0x45, 0x3E];
    let mask: &[u8] = &[0xFFu8, 0xDF, 0xDF, 0xDF, 0xDF, 0xDF, 0xFF];
    assert(pattern@ =~= table[17].pattern && mask@ =~= table[17].mask);
    if row_matches(input, pattern, mask, Ignored::WhitespaceBytes, Ghost(table), Ghost(17nat)) {
        let type_: &[u32] = &[0x74u32, 0x65, 0x78, 0x74];
        let subtype: &[u32] = &[0x68u32, 0x74, 0x6D, 0x6C];
        assert(type_@ =~= table[17].computed.type_ && subtype@ =~= table[17].computed.subtype);
        return Some(mime_literal(type_, subtype));
    }
    // The case-insensitive string "<A" followed by a tag-terminating byte. (TT = 0x20)
    // 3C 41 TT / FF DF FF / Whitespace bytes. / text/html
    let pattern: &[u8] = &[0x3Cu8, 0x41, 0x20];
    let mask: &[u8] = &[0xFFu8, 0xDF, 0xFF];
    assert(pattern@ =~= table[18].pattern && mask@ =~= table[18].mask);
    if row_matches(input, pattern, mask, Ignored::WhitespaceBytes, Ghost(table), Ghost(18nat)) {
        let type_: &[u32] = &[0x74u32, 0x65, 0x78, 0x74];
        let subtype: &[u32] = &[0x68u32, 0x74, 0x6D, 0x6C];
        assert(type_@ =~= table[18].computed.type_ && subtype@ =~= table[18].computed.subtype);
        return Some(mime_literal(type_, subtype));
    }
    // The case-insensitive string "<A" followed by a tag-terminating byte. (TT = 0x3E)
    // 3C 41 TT / FF DF FF / Whitespace bytes. / text/html
    let pattern: &[u8] = &[0x3Cu8, 0x41, 0x3E];
    let mask: &[u8] = &[0xFFu8, 0xDF, 0xFF];
    assert(pattern@ =~= table[19].pattern && mask@ =~= table[19].mask);
    if row_matches(input, pattern, mask, Ignored::WhitespaceBytes, Ghost(table), Ghost(19nat)) {
        let type_: &[u32] = &[0x74u32, 0x65, 0x78, 0x74];
        let subtype: &[u32] = &[0x68u32, 0x74, 0x6D, 0x6C];
        assert(type_@ =~= table[19].computed.type_ && subtype@ =~= table[19].computed.subtype);
        return Some(mime_literal(type_, subtype));
    }
    // The case-insensitive string "<STYLE" followed by a tag-terminating byte. (TT = 0x20)
    // 3C 53 54 59 4C 45 TT / FF DF DF DF DF DF FF / Whitespace bytes. / text/html
    let pattern: &[u8] = &[0x3Cu8, 0x53, 0x54, 0x59, 0x4C, 0x45, 0x20];
    let mask: &[u8] = &[0xFFu8, 0xDF, 0xDF, 0xDF, 0xDF, 0xDF, 0xFF];
    assert(pattern@ =~= table[20].pattern && mask@ =~= table[20].mask);
    if row_matches(input, pattern, mask, Ignored::WhitespaceBytes, Ghost(table), Ghost(20nat)) {
        let type_: &[u32] = &[0x74u32, 0x65, 0x78, 0x74];
        let subtype: &[u32] = &[0x68u32, 0x74, 0x6D, 0x6C];
        assert(type_@ =~= table[20].computed.type_ && subtype@ =~= table[20].computed.subtype);
        return Some(mime_literal(type_, subtype));
    }
    // The case-insensitive string "<STYLE" followed by a tag-terminating byte. (TT = 0x3E)
    // 3C 53 54 59 4C 45 TT / FF DF DF DF DF DF FF / Whitespace bytes. / text/html
    let pattern: &[u8] = &[0x3Cu8, 0x53, 0x54, 0x59, 0x4C, 0x45, 0x3E];
    let mask: &[u8] = &[0xFFu8, 0xDF, 0xDF, 0xDF, 0xDF, 0xDF, 0xFF];
    assert(pattern@ =~= table[21].pattern && mask@ =~= table[21].mask);
    if row_matches(input, pattern, mask, Ignored::WhitespaceBytes, Ghost(table), Ghost(21nat)) {
        let type_: &[u32] = &[0x74u32, 0x65, 0x78, 0x74];
        let subtype: &[u32] = &[0x68u32, 0x74, 0x6D, 0x6C];
        assert(type_@ =~= table[21].computed.type_ && subtype@ =~= table[21].computed.subtype);
        return Some(mime_literal(type_, subtype));
    }
    // The case-insensitive string "<TITLE" followed by a tag-terminating byte. (TT = 0x20)
    // 3C 54 49 54 4C 45 TT / FF DF DF DF DF DF FF / Whitespace bytes. / text/html
    let pattern: &[u8] = &[0x3Cu8, 0x54, 0x49, 0x54, 0x4C, 0x45, 0x20];
    let mask: &[u8] = &[0xFFu8, 0xDF, 0xDF, 0xDF, 0xDF, 0xDF, 0xFF];
    assert(pattern@ =~= table[22].pattern && mask@ =~= table[22].mask);
    if row_matches(input, pattern, mask, Ignored::WhitespaceBytes, Ghost(table), Ghost(22nat)) {
        let type_: &[u32] = &[0x74u32, 0x65, 0x78, 0x74];
        let subtype: &[u32] = &[0x68u32, 0x74, 0x6D, 0x6C];
        assert(type_@ =~= table[22].computed.type_ && subtype@ =~= table[22].computed.subtype);
        return Some(mime_literal(type_, subtype));
    }
    // The case-insensitive string "<TITLE" followed by a tag-terminating byte. (TT = 0x3E)
    // 3C 54 49 54 4C 45 TT / FF DF DF DF DF DF FF / Whitespace bytes. / text/html
    let pattern: &[u8] = &[0x3Cu8, 0x54, 0x49, 0x54, 0x4C, 0x45, 0x3E];
    let mask: &[u8] = &[0xFFu8, 0xDF, 0xDF, 0xDF, 0xDF, 0xDF, 0xFF];
    assert(pattern@ =~= table[23].pattern && mask@ =~= table[23].mask);
    if row_matches(input, pattern, mask, Ignored::WhitespaceBytes, Ghost(table), Ghost(23nat)) {
        let type_: &[u32] = &[0x74u32, 0x65, 0x78, 0x74];
        let subtype: &[u32] = &[0x68u32, 0x74, 0x6D, 0x6C];
        assert(type_@ =~= table[23].computed.type_ && subtype@ =~= table[23].computed.subtype);
        return Some(mime_literal(type_, subtype));
    }
    // The case-insensitive string "<B" followed by a tag-terminating byte. (TT = 0x20)
    // 3C 42 TT / FF DF FF / Whitespace bytes. / text/html
    let pattern: &[u8] = &[0x3Cu8, 0x42, 0x20];
    let mask: &[u8] = &[0xFFu8, 0xDF, 0xFF];
    assert(pattern@ =~= table[24].pattern && mask@ =~= table[24].mask);
    if row_matches(input, pattern, mask, Ignored::WhitespaceBytes, Ghost(table), Ghost(24nat)) {
        let type_: &[u32] = &[0x74u32, 0x65, 0x78, 0x74];
        let subtype: &[u32] = &[0x68u32, 0x74, 0x6D, 0x6C];
        assert(type_@ =~= table[24].computed.type_ && subtype@ =~= table[24].computed.subtype);
        return Some(mime_literal(type_, subtype));
    }
    // The case-insensitive string "<B" followed by a tag-terminating byte. (TT = 0x3E)
    // 3C 42 TT / FF DF FF / Whitespace bytes. / text/html
    let pattern: &[u8] = &[0x3Cu8, 0x42, 0x3E];
    let mask: &[u8] = &[0xFFu8, 0xDF, 0xFF];
    assert(pattern@ =~= table[25].pattern && mask@ =~= table[25].mask);
    if row_matches(input, pattern, mask, Ignored::WhitespaceBytes, Ghost(table), Ghost(25nat)) {
        let type_: &[u32] = &[0x74u32, 0x65, 0x78, 0x74];
        let subtype: &[u32] = &[0x68u32, 0x74, 0x6D, 0x6C];
        assert(type_@ =~= table[25].computed.type_ && subtype@ =~= table[25].computed.subtype);
        return Some(mime_literal(type_, subtype));
    }
    // The case-insensitive string "<BODY" followed by a tag-terminating byte. (TT = 0x20)
    // 3C 42 4F 44 59 TT / FF DF DF DF DF FF / Whitespace bytes. / text/html
    let pattern: &[u8] = &[0x3Cu8, 0x42, 0x4F, 0x44, 0x59, 0x20];
    let mask: &[u8] = &[0xFFu8, 0xDF, 0xDF, 0xDF, 0xDF, 0xFF];
    assert(pattern@ =~= table[26].pattern && mask@ =~= table[26].mask);
    if row_matches(input, pattern, mask, Ignored::WhitespaceBytes, Ghost(table), Ghost(26nat)) {
        let type_: &[u32] = &[0x74u32, 0x65, 0x78, 0x74];
        let subtype: &[u32] = &[0x68u32, 0x74, 0x6D, 0x6C];
        assert(type_@ =~= table[26].computed.type_ && subtype@ =~= table[26].computed.subtype);
        return Some(mime_literal(type_, subtype));
    }
    // The case-insensitive string "<BODY" followed by a tag-terminating byte. (TT = 0x3E)
    // 3C 42 4F 44 59 TT / FF DF DF DF DF FF / Whitespace bytes. / text/html
    let pattern: &[u8] = &[0x3Cu8, 0x42, 0x4F, 0x44, 0x59, 0x3E];
    let mask: &[u8] = &[0xFFu8, 0xDF, 0xDF, 0xDF, 0xDF, 0xFF];
    assert(pattern@ =~= table[27].pattern && mask@ =~= table[27].mask);
    if row_matches(input, pattern, mask, Ignored::WhitespaceBytes, Ghost(table), Ghost(27nat)) {
        let type_: &[u32] = &[0x74u32, 0x65, 0x78, 0x74];
        let subtype: &[u32] = &[0x68u32, 0x74, 0x6D, 0x6C];
        assert(type_@ =~= table[27].computed.type_ && subtype@ =~= table[27].computed.subtype);
        return Some(mime_literal(type_, subtype));
    }
    // The case-insensitive string "<BR" followed by a tag-terminating byte. (TT = 0x20)
    // 3C 42 52 TT / FF DF DF FF / Whitespace bytes. / text/html
    let pattern: &[u8] = &[0x3Cu8, 0x42, 0x52, 0x20];
    let mask: &[u8] = &[0xFFu8, 0xDF, 0xDF, 0xFF];
    assert(pattern@ =~= table[28].pattern && mask@ =~= table[28].mask);
    if row_matches(input, pattern, mask, Ignored::WhitespaceBytes, Ghost(table), Ghost(28nat)) {
        let type_: &[u32] = &[0x74u32, 0x65, 0x78, 0x74];
        let subtype: &[u32] = &[0x68u32, 0x74, 0x6D, 0x6C];
        assert(type_@ =~= table[28].computed.type_ && subtype@ =~= table[28].computed.subtype);
        return Some(mime_literal(type_, subtype));
    }
    // The case-insensitive string "<BR" followed by a tag-terminating byte. (TT = 0x3E)
    // 3C 42 52 TT / FF DF DF FF / Whitespace bytes. / text/html
    let pattern: &[u8] = &[0x3Cu8, 0x42, 0x52, 0x3E];
    let mask: &[u8] = &[0xFFu8, 0xDF, 0xDF, 0xFF];
    assert(pattern@ =~= table[29].pattern && mask@ =~= table[29].mask);
    if row_matches(input, pattern, mask, Ignored::WhitespaceBytes, Ghost(table), Ghost(29nat)) {
        let type_: &[u32] = &[0x74u32, 0x65, 0x78, 0x74];
        let subtype: &[u32] = &[0x68u32, 0x74, 0x6D, 0x6C];
        assert(type_@ =~= table[29].computed.type_ && subtype@ =~= table[29].computed.subtype);
        return Some(mime_literal(type_, subtype));
    }
    // The case-insensitive string "<P" followed by a tag-terminating byte. (TT = 0x20)
    // 3C 50 TT / FF DF FF / Whitespace bytes. / text/html
    let pattern: &[u8] = &[0x3Cu8, 0x50, 0x20];
    let mask: &[u8] = &[0xFFu8, 0xDF, 0xFF];
    assert(pattern@ =~= table[30].pattern && mask@ =~= table[30].mask);
    if row_matches(input, pattern, mask, Ignored::WhitespaceBytes, Ghost(table), Ghost(30nat)) {
        let type_: &[u32] = &[0x74u32, 0x65, 0x78, 0x74];
        let subtype: &[u32] = &[0x68u32, 0x74, 0x6D, 0x6C];
        assert(type_@ =~= table[30].computed.type_ && subtype@ =~= table[30].computed.subtype);
        return Some(mime_literal(type_, subtype));
    }
    // The case-insensitive string "<P" followed by a tag-terminating byte. (TT = 0x3E)
    // 3C 50 TT / FF DF FF / Whitespace bytes. / text/html
    let pattern: &[u8] = &[0x3Cu8, 0x50, 0x3E];
    let mask: &[u8] = &[0xFFu8, 0xDF, 0xFF];
    assert(pattern@ =~= table[31].pattern && mask@ =~= table[31].mask);
    if row_matches(input, pattern, mask, Ignored::WhitespaceBytes, Ghost(table), Ghost(31nat)) {
        let type_: &[u32] = &[0x74u32, 0x65, 0x78, 0x74];
        let subtype: &[u32] = &[0x68u32, 0x74, 0x6D, 0x6C];
        assert(type_@ =~= table[31].computed.type_ && subtype@ =~= table[31].computed.subtype);
        return Some(mime_literal(type_, subtype));
    }
    // The string "<!--" followed by a tag-terminating byte. (TT = 0x20)
    // 3C 21 2D 2D TT / FF FF FF FF FF / Whitespace bytes. / text/html
    let pattern: &[u8] = &[0x3Cu8, 0x21, 0x2D, 0x2D, 0x20];
    let mask: &[u8] = &[0xFFu8, 0xFF, 0xFF, 0xFF, 0xFF];
    assert(pattern@ =~= table[32].pattern && mask@ =~= table[32].mask);
    if row_matches(input, pattern, mask, Ignored::WhitespaceBytes, Ghost(table), Ghost(32nat)) {
        let type_: &[u32] = &[0x74u32, 0x65, 0x78, 0x74];
        let subtype: &[u32] = &[0x68u32, 0x74, 0x6D, 0x6C];
        assert(type_@ =~= table[32].computed.type_ && subtype@ =~= table[32].computed.subtype);
        return Some(mime_literal(type_, subtype));
    }
    // The string "<!--" followed by a tag-terminating byte. (TT = 0x3E)
    // 3C 21 2D 2D TT / FF FF FF FF FF / Whitespace bytes. / text/html
    let pattern: &[u8] = &[0x3Cu8, 0x21, 0x2D, 0x2D, 0x3E];
    let mask: &[u8] = &[0xFFu8, 0xFF, 0xFF, 0xFF, 0xFF];
    assert(pattern@ =~= table[33].pattern && mask@ =~= table[33].mask);
    if row_matches(input, pattern, mask, Ignored::WhitespaceBytes, Ghost(table), Ghost(33nat)) {
        let type_: &[u32] = &[0x74u32, 0x65, 0x78, 0x74];
        let subtype: &[u32] = &[0x68u32, 0x74, 0x6D, 0x6C];
        assert(type_@ =~= table[33].computed.type_ && subtype@ =~= table[33].computed.subtype);
        return Some(mime_literal(type_, subtype));
    }
    // The string "<?xml".
    // 3C 3F 78 6D 6C / FF FF FF FF FF / Whitespace bytes. / text/xml
    let pattern: &[u8] = &[0x3Cu8, 0x3F, 0x78, 0x6D, 0x6C];
    let mask: &[u8] = &[0xFFu8, 0xFF, 0xFF, 0xFF, 0xFF];
    assert(pattern@ =~= table[34].pattern && mask@ =~= table[34].mask);
    if row_matches(input, pattern, mask, Ignored::WhitespaceBytes, Ghost(table), Ghost(34nat)) {
        let type_: &[u32] = &[0x74u32, 0x65, 0x78, 0x74];
        let subtype: &[u32] = &[0x78u32, 0x6D, 0x6C];
        assert(type_@ =~= table[34].computed.type_ && subtype@ =~= table[34].computed.subtype);
        return Some(mime_literal(type_, subtype));
    }
    // The string "%PDF-", the PDF signature.
    // 25 50 44 46 2D / FF FF FF FF FF / None. / application/pdf
    let pattern: &[u8] = &[0x25u8, 0x50, 0x44, 0x46, 0x2D];
    let mask: &[u8] = &[0xFFu8, 0xFF, 0xFF, 0xFF, 0xFF];
    assert(pattern@ =~= table[35].pattern && mask@ =~= table[35].mask);
    if row_matches(input, pattern, mask, Ignored::None, Ghost(table), Ghost(35nat)) {
        let type_: &[u32] = &[0x61u32, 0x70, 0x70, 0x6C, 0x69, 0x63, 0x61, 0x74, 0x69, 0x6F, 0x6E];
        let subtype: &[u32] = &[0x70u32, 0x64, 0x66];
        assert(type_@ =~= table[35].computed.type_ && subtype@ =~= table[35].computed.subtype);
        return Some(mime_literal(type_, subtype));
    }
    // No row matched.
    None
}

/// The table in §7.1 step 2 (rules for identifying an unknown MIME type).
pub fn match_unknown_non_scriptable_table(input: &[u8]) -> (r: Option<MimeType>)
    ensures
        crate::mime_type::record::option_view(r) == match_table(input@, unknown_non_scriptable_table(), 0),
{
    let ghost table = unknown_non_scriptable_table();
    assert(table.len() == 4);
    // The string "%!PS-Adobe-", the PostScript signature.
    // 25 21 50 53 2D 41 64 6F 62 65 2D / FF FF FF FF FF FF FF FF FF FF FF / None. / application/postscript
    let pattern: &[u8] = &[0x25u8, 0x21, 0x50, 0x53, 0x2D, 0x41, 0x64, 0x6F, 0x62, 0x65, 0x2D];
    let mask: &[u8] = &[0xFFu8, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF];
    assert(pattern@ =~= table[0].pattern && mask@ =~= table[0].mask);
    if row_matches(input, pattern, mask, Ignored::None, Ghost(table), Ghost(0nat)) {
        let type_: &[u32] = &[0x61u32, 0x70, 0x70, 0x6C, 0x69, 0x63, 0x61, 0x74, 0x69, 0x6F, 0x6E];
        let subtype: &[u32] = &[0x70u32, 0x6F, 0x73, 0x74, 0x73, 0x63, 0x72, 0x69, 0x70, 0x74];
        assert(type_@ =~= table[0].computed.type_ && subtype@ =~= table[0].computed.subtype);
        return Some(mime_literal(type_, subtype));
    }
    // UTF-16BE BOM
    // FE FF 00 00 / FF FF 00 00 / None. / text/plain
    let pattern: &[u8] = &[0xFEu8, 0xFF, 0x00, 0x00];
    let mask: &[u8] = &[0xFFu8, 0xFF, 0x00, 0x00];
    assert(pattern@ =~= table[1].pattern && mask@ =~= table[1].mask);
    if row_matches(input, pattern, mask, Ignored::None, Ghost(table), Ghost(1nat)) {
        let type_: &[u32] = &[0x74u32, 0x65, 0x78, 0x74];
        let subtype: &[u32] = &[0x70u32, 0x6C, 0x61, 0x69, 0x6E];
        assert(type_@ =~= table[1].computed.type_ && subtype@ =~= table[1].computed.subtype);
        return Some(mime_literal(type_, subtype));
    }
    // UTF-16LE BOM
    // FF FE 00 00 / FF FF 00 00 / None. / text/plain
    let pattern: &[u8] = &[0xFFu8, 0xFE, 0x00, 0x00];
    let mask: &[u8] = &[0xFFu8, 0xFF, 0x00, 0x00];
    assert(pattern@ =~= table[2].pattern && mask@ =~= table[2].mask);
    if row_matches(input, pattern, mask, Ignored::None, Ghost(table), Ghost(2nat)) {
        let type_: &[u32] = &[0x74u32, 0x65, 0x78, 0x74];
        let subtype: &[u32] = &[0x70u32, 0x6C, 0x61, 0x69, 0x6E];
        assert(type_@ =~= table[2].computed.type_ && subtype@ =~= table[2].computed.subtype);
        return Some(mime_literal(type_, subtype));
    }
    // UTF-8 BOM
    // EF BB BF 00 / FF FF FF 00 / None. / text/plain
    let pattern: &[u8] = &[0xEFu8, 0xBB, 0xBF, 0x00];
    let mask: &[u8] = &[0xFFu8, 0xFF, 0xFF, 0x00];
    assert(pattern@ =~= table[3].pattern && mask@ =~= table[3].mask);
    if row_matches(input, pattern, mask, Ignored::None, Ghost(table), Ghost(3nat)) {
        let type_: &[u32] = &[0x74u32, 0x65, 0x78, 0x74];
        let subtype: &[u32] = &[0x70u32, 0x6C, 0x61, 0x69, 0x6E];
        assert(type_@ =~= table[3].computed.type_ && subtype@ =~= table[3].computed.subtype);
        return Some(mime_literal(type_, subtype));
    }
    // No row matched.
    None
}

} // verus!
