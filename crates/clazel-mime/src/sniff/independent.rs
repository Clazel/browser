//! An independent transcription of MIME sniffing's signature tables and
//! the algorithms built on them, and the proof that it agrees with
//! [`super::spec`]. The transcription section uses nothing from `spec.rs`;
//! only the proof section below it does.
//!
//! What is independent, and from what:
//! - Each table row is read from its *note* (the prose column: "The string
//!   "GIF89a"", "The case-insensitive string "<HTML" followed by a
//!   tag-terminating byte", "The string "RIFF" followed by four bytes
//!   followed by the string "AVI "", ...), not from its byte pattern and
//!   pattern mask, and checked against the file-format specification the
//!   note names, where there is one:
//!   - ICO and CUR: Microsoft's ICONDIR header (`idReserved` 0, `idType` 1
//!     for icons and 2 for cursors, little-endian WORDs);
//!   - BMP: `BITMAPFILEHEADER.bfType`, "BM";
//!   - GIF: GIF89a specification §17 (Signature "GIF", Version "87a" or
//!     "89a");
//!   - WebP: the WebP container specification (a RIFF file whose form type
//!     is "WEBP"; its first chunk is "VP8 ", "VP8L" or "VP8X", all of which
//!     start with "VP", which is what the row checks);
//!   - PNG: PNG (Third Edition) §5.2, the signature 137 80 78 71 13 10 26 10
//!     (written here in decimal, as there);
//!   - JPEG: ITU-T T.81 B.1.1.3 (markers are 0xFF then a code; SOI is
//!     0xFFD8);
//!   - AIFF ("FORM" .... "AIFF"), WAVE and AVI (RIFF form types "WAVE" and
//!     "AVI "), Standard MIDI Files ("MThd" and a header length of 6 as a
//!     32-bit big-endian number), Ogg (RFC 3533 §6: capture pattern "OggS"
//!     then stream structure version 0), ID3v2 ("ID3");
//!   - TrueType/OpenType (`sfntVersion` 0x00010000 or "OTTO"), TrueType
//!     Collections ("ttcf"), WOFF ("wOFF") and WOFF2 ("wOF2"), Embedded
//!     OpenType (the magic number 0x504C, "LP", at offset 34);
//!   - GZIP: RFC 1952 §2.3.1 (ID1 31, ID2 139, CM 8 = deflate); ZIP: APPNOTE
//!     4.3.7 (local file header signature 0x04034b50, little-endian); RAR
//!     4.x: the marker block "Rar!" 0x1A 0x07 0x00;
//!   - the UTF-16 and UTF-8 byte order marks: Unicode §23.8 (U+FEFF
//!     encoded);
//!   - PDF ("%PDF-", ISO 32000-1 §7.5.2) and PostScript ("%!PS-Adobe-",
//!     the DSC header).
//! - MP4 (§6.2.1) is read with ISO/IEC 14496-12's `FileTypeBox` layout
//!   (size, "ftyp", `major_brand`, `minor_version`, then
//!   `compatible_brands` to the end of the box): it matches when the box
//!   checks of steps 3–6 pass and some brand starts with "mp4". The loop
//!   of steps 8–10 becomes "some compatible brand", a quantifier.
//! - §7.2 (text or binary) is read with the BOMs from the Unicode Standard
//!   and §3's binary data bytes as a set.
//! - The order of the rows, and how §6.2 and §7.1 combine the tables, come
//!   from the same standard; they are not independent.
//!
//! Not independently transcribed: the WebM and MP3-without-ID3 signatures
//! (§6.2.2, §6.2.3) and §7's dispatch on the supplied MIME type. The
//! format specs (Matroska/EBML, MPEG audio) do not define these sniffing
//! heuristics, and the standard's text needed four errata to read at all.
//! [`indep_audio_or_video`] and [`indep_identify_unknown`] therefore take
//! the WebM and MP3 results as inputs; the agreement lemmas pass the
//! spec's. Those parts are covered by `examples.rs` (real files from WPT)
//! and the conformance tests.
//!
//! Modelling choices:
//! - A row is a [`Signature`] and the MIME type it gives (type and subtype;
//!   no parameters). A tag-terminating byte is 0x20 or 0x3E (§3), and is
//!   one alternative of one row, where the spec splits the row in two.
//! - "Case-insensitive" compares ASCII lowercase (Infra): A–Z map to a–z.
//! - "Whitespace bytes" are skipped at the start (§3 whitespace byte), as
//!   the third column says for the rows that have them.
//! - The byte order mark rows ("UTF-16BE BOM", ...) are four bytes long in
//!   the standard's patterns, the last ones masked out, and the pattern
//!   matching algorithm requires the input to be as long as the pattern
//!   (§6 step 2). The notes do not say so; we read them as "the BOM
//!   followed by two bytes" (one byte for UTF-8), which is what the table
//!   does. So a three-byte resource FE FF 00 is not "UTF-16BE BOM" here.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;
use super::lemmas::lemma_pattern_matching_in_bounds;

verus! {

// ===========================================================================
// Transcription. Uses nothing from `spec.rs`.
// ===========================================================================

/// A whitespace byte (§3): HT, LF, FF, CR, SP.
pub open spec fn ws(b: u8) -> bool {
    b == 9 || b == 10 || b == 12 || b == 13 || b == 32
}

/// A tag-terminating byte (§3): SP or ">".
pub open spec fn tag_terminating(b: u8) -> bool {
    b == 0x20 || b == 0x3E
}

/// A binary data byte (§3), as the set it is: every byte below 0x20 except
/// HT, LF, FF, CR and ESC (0x1B).
pub open spec fn binary_data(b: u8) -> bool {
    b < 0x20 && b != 0x09 && b != 0x0A && b != 0x0C && b != 0x0D && b != 0x1B
}

/// ASCII lowercase of a byte (Infra): A–Z to a–z.
pub open spec fn lower(b: u8) -> u8 {
    if 0x41 <= b <= 0x5A { (b + 0x20) as u8 } else { b }
}

/// How many whitespace bytes `bytes` starts with.
pub open spec fn leading_whitespace(bytes: Seq<u8>) -> nat
    decreases bytes.len()
{
    if bytes.len() > 0 && ws(bytes[0]) { 1 + leading_whitespace(bytes.drop_first()) } else { 0 }
}

/// `input`, from `offset`, begins with `s`; case-insensitively if `ci`.
pub open spec fn begins_with_at(input: Seq<u8>, offset: nat, s: Seq<u8>, ci: bool) -> bool
    decreases s.len()
{
    if s.len() == 0 {
        true
    } else {
        offset < input.len() && (if ci { lower(input[offset as int]) == lower(s[0]) } else { input[offset as int] == s[0] })
            && begins_with_at(input, offset + 1, s.drop_first(), ci)
    }
}

/// `input` has no binary data byte.
pub open spec fn no_binary_data(input: Seq<u8>) -> bool
    decreases input.len()
{
    input.len() == 0 || (!binary_data(input[0]) && no_binary_data(input.drop_first()))
}

/// What a row's note says the resource header starts with.
pub enum Signature {
    /// "The string X" (or bytes X) at the start.
    Starts(Seq<u8>),
    /// X, then `n` bytes of any value, then Y.
    Gap(Seq<u8>, nat, Seq<u8>),
    /// After whitespace bytes: "The case-insensitive string X followed by a
    /// tag-terminating byte."
    CaseInsensitiveTag(Seq<u8>),
    /// After whitespace bytes: "The string X followed by a tag-terminating
    /// byte."
    Tag(Seq<u8>),
    /// After whitespace bytes: "The string X."
    StartsAfterWhitespace(Seq<u8>),
}

/// Does `input` have `sig`?
pub open spec fn has(input: Seq<u8>, sig: Signature) -> bool {
    let w = leading_whitespace(input);
    match sig {
        Signature::Starts(x) => begins_with_at(input, 0, x, false),
        Signature::Gap(x, n, y) => x.len() + n + y.len() <= input.len() && begins_with_at(input, 0, x, false)
            && begins_with_at(input, x.len() + n, y, false),
        Signature::CaseInsensitiveTag(x) => begins_with_at(input, w, x, true) && w + x.len() < input.len()
            && tag_terminating(input[(w + x.len()) as int]),
        Signature::Tag(x) => begins_with_at(input, w, x, false) && w + x.len() < input.len()
            && tag_terminating(input[(w + x.len()) as int]),
        Signature::StartsAfterWhitespace(x) => begins_with_at(input, w, x, false),
    }
}

/// A table row: the signature and the MIME type (type, subtype) it gives.
pub struct Entry {
    /// The signature.
    pub sig: Signature,
    /// The type.
    pub type_: Seq<u32>,
    /// The subtype.
    pub subtype: Seq<u32>,
}

/// The MIME type with this type and subtype and no parameters.
pub open spec fn literal(type_: Seq<u32>, subtype: Seq<u32>) -> crate::mime_type::spec::MimeTypeRecord {
    crate::mime_type::spec::MimeTypeRecord { type_, subtype, parameters: seq![] }
}

/// The MIME type of the first entry from `i` on that `input` has.
pub open spec fn first_match(input: Seq<u8>, entries: Seq<Entry>, i: nat) -> Option<crate::mime_type::spec::MimeTypeRecord>
    decreases entries.len() - i
{
    if i < entries.len() {
        if has(input, entries[i as int].sig) {
            Some(literal(entries[i as int].type_, entries[i as int].subtype))
        } else {
            first_match(input, entries, i + 1)
        }
    } else {
        None
    }
}

// Type and subtype strings, as code points.
/// "image"
pub open spec fn s_image() -> Seq<u32> { seq![0x69u32, 0x6D, 0x61, 0x67, 0x65] }
/// "audio"
pub open spec fn s_audio() -> Seq<u32> { seq![0x61u32, 0x75, 0x64, 0x69, 0x6F] }
/// "video"
pub open spec fn s_video() -> Seq<u32> { seq![0x76u32, 0x69, 0x64, 0x65, 0x6F] }
/// "application"
pub open spec fn s_application() -> Seq<u32> { seq![0x61u32, 0x70, 0x70, 0x6C, 0x69, 0x63, 0x61, 0x74, 0x69, 0x6F, 0x6E] }
/// "font"
pub open spec fn s_font() -> Seq<u32> { seq![0x66u32, 0x6F, 0x6E, 0x74] }
/// "text"
pub open spec fn s_text() -> Seq<u32> { seq![0x74u32, 0x65, 0x78, 0x74] }
/// "html"
pub open spec fn s_html() -> Seq<u32> { seq![0x68u32, 0x74, 0x6D, 0x6C] }
/// "plain"
pub open spec fn s_plain() -> Seq<u32> { seq![0x70u32, 0x6C, 0x61, 0x69, 0x6E] }
/// "mpeg"
pub open spec fn s_mpeg() -> Seq<u32> { seq![0x6Du32, 0x70, 0x65, 0x67] }
/// "octet-stream"
pub open spec fn s_octet_stream() -> Seq<u32> { seq![0x6Fu32, 0x63, 0x74, 0x65, 0x74, 0x2D, 0x73, 0x74, 0x72, 0x65, 0x61, 0x6D] }

/// §6.1's rows, in order.
pub open spec fn image_entries() -> Seq<Entry> {
    seq![
        // ICONDIR: idReserved 0, idType 1 (icon), little-endian WORDs.
        Entry { sig: Signature::Starts(seq![0u8, 0, 1, 0]), type_: s_image(), subtype: seq![0x78u32, 0x2D, 0x69, 0x63, 0x6F, 0x6E] },
        // ICONDIR: idReserved 0, idType 2 (cursor).
        Entry { sig: Signature::Starts(seq![0u8, 0, 2, 0]), type_: s_image(), subtype: seq![0x78u32, 0x2D, 0x69, 0x63, 0x6F, 0x6E] },
        // "BM"
        Entry { sig: Signature::Starts(seq![0x42u8, 0x4D]), type_: s_image(), subtype: seq![0x62u32, 0x6D, 0x70] },
        // "GIF" "87a"
        Entry { sig: Signature::Starts(seq![0x47u8, 0x49, 0x46, 0x38, 0x37, 0x61]), type_: s_image(), subtype: seq![0x67u32, 0x69, 0x66] },
        // "GIF" "89a"
        Entry { sig: Signature::Starts(seq![0x47u8, 0x49, 0x46, 0x38, 0x39, 0x61]), type_: s_image(), subtype: seq![0x67u32, 0x69, 0x66] },
        // "RIFF", four bytes (the file size), "WEBP", then "VP" (VP8 , VP8L, VP8X).
        Entry { sig: Signature::Gap(seq![0x52u8, 0x49, 0x46, 0x46], 4, seq![0x57u8, 0x45, 0x42, 0x50, 0x56, 0x50]), type_: s_image(), subtype: seq![0x77u32, 0x65, 0x62, 0x70] },
        // PNG signature, in decimal as in PNG §5.2.
        Entry { sig: Signature::Starts(seq![137u8, 80, 78, 71, 13, 10, 26, 10]), type_: s_image(), subtype: seq![0x70u32, 0x6E, 0x67] },
        // SOI (0xFF 0xD8), then 0xFF, the first byte of the next marker.
        Entry { sig: Signature::Starts(seq![0xFFu8, 0xD8, 0xFF]), type_: s_image(), subtype: seq![0x6Au32, 0x70, 0x65, 0x67] },
    ]
}

/// §6.2's rows, in order.
pub open spec fn audio_or_video_entries() -> Seq<Entry> {
    seq![
        // "FORM", four bytes, "AIFF".
        Entry { sig: Signature::Gap(seq![0x46u8, 0x4F, 0x52, 0x4D], 4, seq![0x41u8, 0x49, 0x46, 0x46]), type_: s_audio(), subtype: seq![0x61u32, 0x69, 0x66, 0x66] },
        // "ID3"
        Entry { sig: Signature::Starts(seq![0x49u8, 0x44, 0x33]), type_: s_audio(), subtype: s_mpeg() },
        // "OggS", version 0.
        Entry { sig: Signature::Starts(seq![0x4Fu8, 0x67, 0x67, 0x53, 0]), type_: s_application(), subtype: seq![0x6Fu32, 0x67, 0x67] },
        // "MThd", header length 6 as a 32-bit big-endian number.
        Entry { sig: Signature::Starts(seq![0x4Du8, 0x54, 0x68, 0x64, 0, 0, 0, 6]), type_: s_audio(), subtype: seq![0x6Du32, 0x69, 0x64, 0x69] },
        // "RIFF", four bytes, "AVI ".
        Entry { sig: Signature::Gap(seq![0x52u8, 0x49, 0x46, 0x46], 4, seq![0x41u8, 0x56, 0x49, 0x20]), type_: s_video(), subtype: seq![0x61u32, 0x76, 0x69] },
        // "RIFF", four bytes, "WAVE".
        Entry { sig: Signature::Gap(seq![0x52u8, 0x49, 0x46, 0x46], 4, seq![0x57u8, 0x41, 0x56, 0x45]), type_: s_audio(), subtype: seq![0x77u32, 0x61, 0x76, 0x65] },
    ]
}

/// §6.3's rows, in order.
pub open spec fn font_entries() -> Seq<Entry> {
    seq![
        // 34 bytes, then the EOT MagicNumber 0x504C, stored little-endian: "LP".
        Entry { sig: Signature::Gap(seq![], 34, seq![0x4Cu8, 0x50]), type_: s_application(), subtype: seq![0x76u32, 0x6E, 0x64, 0x2E, 0x6D, 0x73, 0x2D, 0x66, 0x6F, 0x6E, 0x74, 0x6F, 0x62, 0x6A, 0x65, 0x63, 0x74] },
        // sfntVersion 0x00010000 (version 1.0), big-endian.
        Entry { sig: Signature::Starts(seq![0u8, 1, 0, 0]), type_: s_font(), subtype: seq![0x74u32, 0x74, 0x66] },
        // "OTTO"
        Entry { sig: Signature::Starts(seq![0x4Fu8, 0x54, 0x54, 0x4F]), type_: s_font(), subtype: seq![0x6Fu32, 0x74, 0x66] },
        // "ttcf"
        Entry { sig: Signature::Starts(seq![0x74u8, 0x74, 0x63, 0x66]), type_: s_font(), subtype: seq![0x63u32, 0x6F, 0x6C, 0x6C, 0x65, 0x63, 0x74, 0x69, 0x6F, 0x6E] },
        // "wOFF"
        Entry { sig: Signature::Starts(seq![0x77u8, 0x4F, 0x46, 0x46]), type_: s_font(), subtype: seq![0x77u32, 0x6F, 0x66, 0x66] },
        // "wOF2"
        Entry { sig: Signature::Starts(seq![0x77u8, 0x4F, 0x46, 0x32]), type_: s_font(), subtype: seq![0x77u32, 0x6F, 0x66, 0x66, 0x32] },
    ]
}

/// §6.4's rows, in order.
pub open spec fn archive_entries() -> Seq<Entry> {
    seq![
        // RFC 1952: ID1 31, ID2 139, CM 8.
        Entry { sig: Signature::Starts(seq![31u8, 139, 8]), type_: s_application(), subtype: seq![0x78u32, 0x2D, 0x67, 0x7A, 0x69, 0x70] },
        // 0x04034b50 little-endian: "PK" 3 4.
        Entry { sig: Signature::Starts(seq![0x50u8, 0x4B, 3, 4]), type_: s_application(), subtype: seq![0x7Au32, 0x69, 0x70] },
        // "Rar!" 0x1A 0x07 0x00.
        Entry { sig: Signature::Starts(seq![0x52u8, 0x61, 0x72, 0x21, 0x1A, 0x07, 0x00]), type_: s_application(), subtype: seq![0x78u32, 0x2D, 0x72, 0x61, 0x72, 0x2D, 0x63, 0x6F, 0x6D, 0x70, 0x72, 0x65, 0x73, 0x73, 0x65, 0x64] },
    ]
}

/// A row giving "text/html" for a case-insensitive tag.
pub open spec fn html_tag(tag: Seq<u8>) -> Entry {
    Entry { sig: Signature::CaseInsensitiveTag(tag), type_: s_text(), subtype: s_html() }
}

/// §7.1 step 1's rows, in order.
pub open spec fn scriptable_entries() -> Seq<Entry> {
    seq![
        // "<!DOCTYPE HTML"
        html_tag(seq![0x3Cu8, 0x21, 0x44, 0x4F, 0x43, 0x54, 0x59, 0x50, 0x45, 0x20, 0x48, 0x54, 0x4D, 0x4C]),
        // "<HTML"
        html_tag(seq![0x3Cu8, 0x48, 0x54, 0x4D, 0x4C]),
        // "<HEAD"
        html_tag(seq![0x3Cu8, 0x48, 0x45, 0x41, 0x44]),
        // "<SCRIPT"
        html_tag(seq![0x3Cu8, 0x53, 0x43, 0x52, 0x49, 0x50, 0x54]),
        // "<IFRAME"
        html_tag(seq![0x3Cu8, 0x49, 0x46, 0x52, 0x41, 0x4D, 0x45]),
        // "<H1"
        html_tag(seq![0x3Cu8, 0x48, 0x31]),
        // "<DIV"
        html_tag(seq![0x3Cu8, 0x44, 0x49, 0x56]),
        // "<FONT"
        html_tag(seq![0x3Cu8, 0x46, 0x4F, 0x4E, 0x54]),
        // "<TABLE"
        html_tag(seq![0x3Cu8, 0x54, 0x41, 0x42, 0x4C, 0x45]),
        // "<A"
        html_tag(seq![0x3Cu8, 0x41]),
        // "<STYLE"
        html_tag(seq![0x3Cu8, 0x53, 0x54, 0x59, 0x4C, 0x45]),
        // "<TITLE"
        html_tag(seq![0x3Cu8, 0x54, 0x49, 0x54, 0x4C, 0x45]),
        // "<B"
        html_tag(seq![0x3Cu8, 0x42]),
        // "<BODY"
        html_tag(seq![0x3Cu8, 0x42, 0x4F, 0x44, 0x59]),
        // "<BR"
        html_tag(seq![0x3Cu8, 0x42, 0x52]),
        // "<P"
        html_tag(seq![0x3Cu8, 0x50]),
        // "<!--" followed by a tag-terminating byte (not case-insensitive).
        Entry { sig: Signature::Tag(seq![0x3Cu8, 0x21, 0x2D, 0x2D]), type_: s_text(), subtype: s_html() },
        // "<?xml"
        Entry { sig: Signature::StartsAfterWhitespace(seq![0x3Cu8, 0x3F, 0x78, 0x6D, 0x6C]), type_: s_text(), subtype: seq![0x78u32, 0x6D, 0x6C] },
        // "%PDF-"
        Entry { sig: Signature::Starts(seq![0x25u8, 0x50, 0x44, 0x46, 0x2D]), type_: s_application(), subtype: seq![0x70u32, 0x64, 0x66] },
    ]
}

/// §7.1 step 2's rows, in order.
pub open spec fn non_scriptable_entries() -> Seq<Entry> {
    seq![
        // "%!PS-Adobe-"
        Entry { sig: Signature::Starts(seq![0x25u8, 0x21, 0x50, 0x53, 0x2D, 0x41, 0x64, 0x6F, 0x62, 0x65, 0x2D]), type_: s_application(), subtype: seq![0x70u32, 0x6F, 0x73, 0x74, 0x73, 0x63, 0x72, 0x69, 0x70, 0x74] },
        // U+FEFF in UTF-16BE, then two bytes.
        Entry { sig: Signature::Gap(seq![0xFEu8, 0xFF], 2, seq![]), type_: s_text(), subtype: s_plain() },
        // U+FEFF in UTF-16LE, then two bytes.
        Entry { sig: Signature::Gap(seq![0xFFu8, 0xFE], 2, seq![]), type_: s_text(), subtype: s_plain() },
        // U+FEFF in UTF-8, then one byte.
        Entry { sig: Signature::Gap(seq![0xEFu8, 0xBB, 0xBF], 1, seq![]), type_: s_text(), subtype: s_plain() },
    ]
}

/// The 32-bit big-endian number in `input[0..4]` (the box size).
pub open spec fn box_size(input: Seq<u8>) -> nat {
    ((input[0] as nat * 256 + input[1] as nat) * 256 + input[2] as nat) * 256 + input[3] as nat
}

/// The brand (a four-character code) at `offset` starts with "mp4".
pub open spec fn mp4_brand_at(input: Seq<u8>, offset: int) -> bool {
    input[offset] == 0x6D && input[offset + 1] == 0x70 && input[offset + 2] == 0x34
}

/// The checks of §6.2.1 steps 3–6 on the `FileTypeBox`.
pub open spec fn ftyp_box(input: Seq<u8>) -> bool {
    input.len() >= 12 && box_size(input) <= input.len() && box_size(input) % 4 == 0
        && input[4] == 0x66 && input[5] == 0x74 && input[6] == 0x79 && input[7] == 0x70
}

/// The `j`th compatible brand (at 16 + 4j, inside the box) starts with
/// "mp4".
pub open spec fn mp4_compatible_brand(input: Seq<u8>, j: nat) -> bool {
    16 + 4 * j < box_size(input) && mp4_brand_at(input, (16 + 4 * j) as int)
}

/// The MP4 signature, read with ISO/IEC 14496-12's `FileTypeBox`: the
/// major brand or some compatible brand starts with "mp4".
pub open spec fn indep_mp4(input: Seq<u8>) -> bool {
    ftyp_box(input) && (mp4_brand_at(input, 8) || exists|j: nat| mp4_compatible_brand(input, j))
}

/// §6.1.
pub open spec fn indep_image(input: Seq<u8>) -> Option<crate::mime_type::spec::MimeTypeRecord> {
    first_match(input, image_entries(), 0)
}

/// §6.2, given whether the input matches the WebM and MP3-without-ID3
/// signatures (not transcribed here).
pub open spec fn indep_audio_or_video(input: Seq<u8>, webm: bool, mp3: bool) -> Option<crate::mime_type::spec::MimeTypeRecord> {
    match first_match(input, audio_or_video_entries(), 0) {
        Some(t) => Some(t),
        None => if indep_mp4(input) {
            Some(literal(s_video(), seq![0x6Du32, 0x70, 0x34]))
        } else if webm {
            Some(literal(s_video(), seq![0x77u32, 0x65, 0x62, 0x6D]))
        } else if mp3 {
            Some(literal(s_audio(), s_mpeg()))
        } else {
            None
        },
    }
}

/// §6.3.
pub open spec fn indep_font(input: Seq<u8>) -> Option<crate::mime_type::spec::MimeTypeRecord> {
    first_match(input, font_entries(), 0)
}

/// §6.4.
pub open spec fn indep_archive(input: Seq<u8>) -> Option<crate::mime_type::spec::MimeTypeRecord> {
    first_match(input, archive_entries(), 0)
}

/// "text/plain" or "application/octet-stream", by whether `input` has
/// binary data bytes.
pub open spec fn text_or_octet_stream(input: Seq<u8>) -> crate::mime_type::spec::MimeTypeRecord {
    if no_binary_data(input) { literal(s_text(), s_plain()) } else { literal(s_application(), s_octet_stream()) }
}

/// §7.1, given the WebM and MP3 results.
pub open spec fn indep_identify_unknown(input: Seq<u8>, sniff_scriptable: bool, webm: bool, mp3: bool) -> crate::mime_type::spec::MimeTypeRecord {
    let found = if sniff_scriptable { first_match(input, scriptable_entries(), 0) } else { None };
    let found = if found is Some { found } else { first_match(input, non_scriptable_entries(), 0) };
    let found = if found is Some { found } else { indep_image(input) };
    let found = if found is Some { found } else { indep_audio_or_video(input, webm, mp3) };
    let found = if found is Some { found } else { indep_archive(input) };
    match found {
        Some(t) => t,
        None => text_or_octet_stream(input),
    }
}

/// §7.2: a UTF-16 or UTF-8 byte order mark, or no binary data bytes, is
/// text.
pub open spec fn indep_text_or_binary(input: Seq<u8>) -> crate::mime_type::spec::MimeTypeRecord {
    if begins_with_at(input, 0, seq![0xFEu8, 0xFF], false) || begins_with_at(input, 0, seq![0xFFu8, 0xFE], false)
        || begins_with_at(input, 0, seq![0xEFu8, 0xBB, 0xBF], false) {
        literal(s_text(), s_plain())
    } else {
        text_or_octet_stream(input)
    }
}

// ===========================================================================
// Proof. From here on, `spec.rs` is used.
// ===========================================================================

// ---------------------------------------------------------------------------
// Bytes and strings.
// ---------------------------------------------------------------------------

/// Bytes `a` and `b` are the same, ignoring ASCII case if `ci`.
pub open spec fn same(a: u8, b: u8, ci: bool) -> bool {
    if ci { lower(a) == lower(b) } else { a == b }
}

/// `begins_with_at`, as a quantifier.
pub proof fn lemma_begins_with_at(input: Seq<u8>, offset: nat, s: Seq<u8>, ci: bool)
    ensures
        begins_with_at(input, offset, s, ci) == ((s.len() == 0 || offset + s.len() <= input.len())
            && forall|k: int| 0 <= k < s.len() ==> same(#[trigger] input[offset + k], s[k], ci)),
    decreases s.len(),
{
    if s.len() > 0 {
        let rest = s.drop_first();
        lemma_begins_with_at(input, offset + 1, rest, ci);
        let q = forall|k: int| 0 <= k < s.len() ==> same(#[trigger] input[offset + k], s[k], ci);
        let r = forall|k: int| 0 <= k < rest.len() ==> same(#[trigger] input[(offset + 1) + k], rest[k], ci);
        if q {
            assert forall|k: int| 0 <= k < rest.len() implies same(#[trigger] input[(offset + 1) + k], rest[k], ci) by {
                assert(input[offset + (k + 1)] == input[(offset + 1) + k]);
                assert(rest[k] == s[k + 1]);
            }
            assert(input[offset + 0int] == input[offset as int]);
        }
        if r && offset < input.len() && same(input[offset as int], s[0], ci) {
            assert forall|k: int| 0 <= k < s.len() implies same(#[trigger] input[offset + k], s[k], ci) by {
                if k > 0 {
                    assert(input[(offset + 1) + (k - 1)] == input[offset + k]);
                    assert(rest[k - 1] == s[k]);
                }
            }
        }
        if begins_with_at(input, offset, s, ci) {
            assert(offset < input.len());
        }
    }
}

/// Skipping whitespace bytes (§6 step 4) skips `leading_whitespace`.
pub proof fn lemma_leading_whitespace(input: Seq<u8>, s: nat)
    requires
        s <= input.len(),
    ensures
        skip_ignored(input, s, Ignored::WhitespaceBytes) == s + leading_whitespace(input.subrange(s as int, input.len() as int)),
    decreases input.len() - s,
{
    let rest = input.subrange(s as int, input.len() as int);
    if s < input.len() {
        assert(rest[0] == input[s as int]);
        assert(rest.drop_first() =~= input.subrange(s + 1int, input.len() as int));
        lemma_leading_whitespace(input, s + 1);
    }
}

/// `leading_whitespace` of the whole input.
proof fn lemma_skip_whitespace(input: Seq<u8>)
    ensures
        skip_ignored(input, 0, Ignored::WhitespaceBytes) == leading_whitespace(input),
        skip_ignored(input, 0, Ignored::None) == 0,
{
    lemma_leading_whitespace(input, 0);
    assert(input.subrange(0, input.len() as int) =~= input);
}

/// §3's two readings of a binary data byte agree.
proof fn lemma_binary_data_byte(b: u8)
    ensures
        is_binary_data_byte(b) == binary_data(b),
{
}

/// The spec's "contains a binary data byte" is "not no binary data".
pub proof fn lemma_no_binary_data(input: Seq<u8>)
    ensures
        contains_binary_data_byte(input) == !no_binary_data(input),
    decreases input.len(),
{
    if input.len() > 0 {
        lemma_binary_data_byte(input[0]);
        lemma_no_binary_data(input.drop_first());
    }
}

// ---------------------------------------------------------------------------
// Each signature as the standard's table rows.
// ---------------------------------------------------------------------------

/// `n` copies of `b`.
pub open spec fn repeat(b: u8, n: nat) -> Seq<u8>
    decreases n
{
    if n == 0 { seq![] } else { repeat(b, (n - 1) as nat).push(b) }
}

/// An ASCII letter.
pub open spec fn letter(b: u8) -> bool {
    (0x41 <= b <= 0x5A) || (0x61 <= b <= 0x7A)
}

/// A byte's pattern-mask byte in a case-insensitive pattern: 0xDF (clear
/// the case bit) for a letter, else 0xFF.
pub open spec fn ci_mask_byte(b: u8) -> u8 {
    if letter(b) { 0xDF } else { 0xFF }
}

/// A byte's pattern byte in a case-insensitive pattern: the uppercase
/// letter, or the byte.
pub open spec fn ci_pattern_byte(b: u8) -> u8 {
    if 0x61 <= b <= 0x7A { (b - 0x20) as u8 } else { b }
}

/// The case-insensitive byte pattern of `s`.
pub open spec fn ci_pattern(s: Seq<u8>) -> Seq<u8>
    decreases s.len()
{
    if s.len() == 0 { seq![] } else { seq![ci_pattern_byte(s[0])] + ci_pattern(s.drop_first()) }
}

/// The pattern mask of `s` compared case-insensitively.
pub open spec fn ci_mask(s: Seq<u8>) -> Seq<u8>
    decreases s.len()
{
    if s.len() == 0 { seq![] } else { seq![ci_mask_byte(s[0])] + ci_mask(s.drop_first()) }
}

/// The spec's row for `pattern`, `mask` and `ignored` giving `e`'s type.
pub open spec fn row(pattern: Seq<u8>, mask: Seq<u8>, ignored: Ignored, e: Entry) -> Row {
    Row { pattern, mask, ignored, computed: literal(e.type_, e.subtype) }
}

/// The standard's table rows for `e`: one, or two for a row with a
/// tag-terminating byte (0x20, then 0x3E; see spec.rs).
pub open spec fn encode(e: Entry) -> Seq<Row> {
    match e.sig {
        Signature::Starts(x) => seq![row(x, repeat(0xFF, x.len()), Ignored::None, e)],
        Signature::Gap(x, n, y) => seq![row(x + repeat(0, n) + y, repeat(0xFF, x.len()) + repeat(0, n) + repeat(0xFF, y.len()), Ignored::None, e)],
        Signature::CaseInsensitiveTag(x) => seq![
            row(ci_pattern(x).push(0x20), ci_mask(x).push(0xFF), Ignored::WhitespaceBytes, e),
            row(ci_pattern(x).push(0x3E), ci_mask(x).push(0xFF), Ignored::WhitespaceBytes, e),
        ],
        Signature::Tag(x) => seq![
            row(x.push(0x20), repeat(0xFF, x.len() + 1), Ignored::WhitespaceBytes, e),
            row(x.push(0x3E), repeat(0xFF, x.len() + 1), Ignored::WhitespaceBytes, e),
        ],
        Signature::StartsAfterWhitespace(x) => seq![row(x, repeat(0xFF, x.len()), Ignored::WhitespaceBytes, e)],
    }
}

/// The table rows of `entries` from `i` on.
pub open spec fn expand(entries: Seq<Entry>, i: nat) -> Seq<Row>
    decreases entries.len() - i
{
    if i < entries.len() { encode(entries[i as int]) + expand(entries, i + 1) } else { seq![] }
}

/// `repeat`'s length and bytes.
pub proof fn lemma_repeat(b: u8, n: nat)
    ensures
        repeat(b, n).len() == n,
        forall|k: int| 0 <= k < n ==> #[trigger] repeat(b, n)[k] == b,
    decreases n,
{
    if n > 0 {
        lemma_repeat(b, (n - 1) as nat);
    }
}

/// `ci_pattern` and `ci_mask` byte by byte.
pub proof fn lemma_ci(s: Seq<u8>)
    ensures
        ci_pattern(s).len() == s.len(),
        ci_mask(s).len() == s.len(),
        forall|k: int| 0 <= k < s.len() ==> #[trigger] ci_pattern(s)[k] == ci_pattern_byte(s[k]) && ci_mask(s)[k] == ci_mask_byte(s[k]),
    decreases s.len(),
{
    if s.len() > 0 {
        let rest = s.drop_first();
        lemma_ci(rest);
        assert forall|k: int| 0 <= k < s.len() implies #[trigger] ci_pattern(s)[k] == ci_pattern_byte(s[k]) && ci_mask(s)[k] == ci_mask_byte(s[k]) by {
            if k > 0 {
                assert(ci_pattern(s)[k] == ci_pattern(rest)[k - 1]);
                assert(ci_mask(s)[k] == ci_mask(rest)[k - 1]);
                assert(rest[k - 1] == s[k]);
            }
        }
    }
}

/// One byte under a case-insensitive mask matches exactly when the two
/// bytes are equal ignoring ASCII case.
pub proof fn lemma_ci_byte(a: u8, c: u8)
    ensures
        ((a & ci_mask_byte(c)) == ci_pattern_byte(c)) == (lower(a) == lower(c)),
{
    let m = ci_mask_byte(c);
    let p = ci_pattern_byte(c);
    let la = lower(a);
    let lc = lower(c);
    assert(((a & m) == p) == (la == lc)) by (bit_vector)
        requires
            m == (if (0x41 <= c && c <= 0x5A) || (0x61 <= c && c <= 0x7A) { 0xDFu8 } else { 0xFFu8 }),
            p == (if 0x61 <= c && c <= 0x7A { (c - 0x20) as u8 } else { c }),
            la == (if 0x41 <= a && a <= 0x5A { (a + 0x20) as u8 } else { a }),
            lc == (if 0x41 <= c && c <= 0x5A { (c + 0x20) as u8 } else { c }),
    ;
}

/// A byte under mask 0xFF is itself; under mask 0 it is 0.
proof fn lemma_mask_byte(a: u8)
    ensures
        (a & 0xFF) == a,
        (a & 0) == 0,
{
    assert((a & 0xFF) == a && (a & 0) == 0) by (bit_vector);
}

/// One row: the pattern matching algorithm on `row(...)` decides the
/// table at `i`.
proof fn lemma_one_row(input: Seq<u8>, rows: Seq<Row>, i: nat)
    requires
        i < rows.len(),
    ensures
        match_table(input, rows, i) == if pattern_matching(input, rows[i as int].pattern, rows[i as int].mask, rows[i as int].ignored) {
            Some(rows[i as int].computed)
        } else {
            match_table(input, rows, i + 1)
        },
{
}

/// The table rows for one entry match exactly when the input has the
/// entry's signature.
pub proof fn lemma_encode(input: Seq<u8>, e: Entry)
    ensures
        match_table(input, encode(e), 0) == if has(input, e.sig) { Some(literal(e.type_, e.subtype)) } else { None },
{
    let rows = encode(e);
    let w = leading_whitespace(input);
    lemma_skip_whitespace(input);
    lemma_one_row(input, rows, 0);
    match e.sig {
        Signature::Starts(x) => {
            lemma_repeat(0xFF, x.len());
            lemma_pattern_matching_in_bounds(input, x, repeat(0xFF, x.len()), Ignored::None);
            lemma_begins_with_at(input, 0, x, false);
            assert forall|k: int| 0 <= k < x.len() implies ((#[trigger] input[0 + k] & repeat(0xFFu8, x.len())[k]) == x[k]) == (input[0 + k] == x[k]) by {
                lemma_mask_byte(input[0 + k]);
            }
        },
        Signature::StartsAfterWhitespace(x) => {
            lemma_repeat(0xFF, x.len());
            lemma_pattern_matching_in_bounds(input, x, repeat(0xFF, x.len()), Ignored::WhitespaceBytes);
            lemma_begins_with_at(input, w, x, false);
            assert forall|k: int| 0 <= k < x.len() implies ((#[trigger] input[w + k] & repeat(0xFFu8, x.len())[k]) == x[k]) == (input[w + k] == x[k]) by {
                lemma_mask_byte(input[w + k]);
            }
        },
        Signature::Gap(x, n, y) => {
            let p = x + repeat(0, n) + y;
            let m = repeat(0xFF, x.len()) + repeat(0, n) + repeat(0xFF, y.len());
            lemma_repeat(0xFF, x.len());
            lemma_repeat(0, n);
            lemma_repeat(0xFF, y.len());
            lemma_pattern_matching_in_bounds(input, p, m, Ignored::None);
            lemma_begins_with_at(input, 0, x, false);
            lemma_begins_with_at(input, x.len() + n, y, false);
            let all = forall|k: int| 0 <= k < p.len() ==> (#[trigger] input[0 + k] & m[k]) == p[k];
            assert forall|k: int| 0 <= k < p.len() implies ((#[trigger] input[0 + k] & m[k]) == p[k]) == (
                if k < x.len() { input[0 + k] == x[k] } else if k < x.len() + n { true } else { input[0 + k] == y[k - x.len() - n] }) by {
                lemma_mask_byte(input[0 + k]);
                if k < x.len() {
                    assert(p[k] == x[k] && m[k] == 0xFF);
                } else if k < x.len() + n {
                    assert(p[k] == 0 && m[k] == 0);
                } else {
                    assert(p[k] == y[k - x.len() - n] && m[k] == 0xFF);
                }
            }
            if all {
                assert forall|k: int| 0 <= k < x.len() implies #[trigger] input[0 + k] == x[k] by {}
                assert forall|k: int| 0 <= k < y.len() implies #[trigger] input[(x.len() + n) + k] == y[k] by {
                    let j = x.len() + n + k;
                    assert(input[0 + j] == input[(x.len() + n) + k]);
                    assert(y[j - x.len() - n] == y[k]);
                }
            }
            if has(input, e.sig) {
                assert forall|k: int| 0 <= k < p.len() implies (#[trigger] input[0 + k] & m[k]) == p[k] by {
                    if k >= x.len() + n {
                        let j = k - x.len() - n;
                        assert(input[(x.len() + n) + j] == input[0 + k]);
                    }
                }
            }
        },
        Signature::CaseInsensitiveTag(x) => {
            lemma_one_row(input, rows, 1);
            lemma_ci(x);
            lemma_begins_with_at(input, w, x, true);
            let m = ci_mask(x).push(0xFF);
            assert forall|tt: u8| tt == 0x20 || tt == 0x3E implies
                pattern_matching(input, #[trigger] ci_pattern(x).push(tt), m, Ignored::WhitespaceBytes) == (begins_with_at(input, w, x, true)
                    && w + x.len() < input.len() && input[(w + x.len()) as int] == tt) by {
                let p = ci_pattern(x).push(tt);
                lemma_pattern_matching_in_bounds(input, p, m, Ignored::WhitespaceBytes);
                assert forall|k: int| 0 <= k < p.len() implies ((#[trigger] input[w + k] & m[k]) == p[k]) == (
                    if k < x.len() { lower(input[w + k]) == lower(x[k]) } else { input[w + k] == tt }) by {
                    lemma_mask_byte(input[w + k]);
                    if k < x.len() {
                        lemma_ci_byte(input[w + k], x[k]);
                    }
                }
                if pattern_matching(input, p, m, Ignored::WhitespaceBytes) {
                    assert(input[(w + x.len()) as int] == tt);
                }
            }
            assert(rows[0].pattern == ci_pattern(x).push(0x20));
            assert(rows[1].pattern == ci_pattern(x).push(0x3E));
            assert(match_table(input, rows, 2) is None);
        },
        Signature::Tag(x) => {
            lemma_one_row(input, rows, 1);
            lemma_begins_with_at(input, w, x, false);
            let m = repeat(0xFF, x.len() + 1);
            lemma_repeat(0xFF, x.len() + 1);
            assert forall|tt: u8| tt == 0x20 || tt == 0x3E implies
                pattern_matching(input, #[trigger] x.push(tt), m, Ignored::WhitespaceBytes) == (begins_with_at(input, w, x, false)
                    && w + x.len() < input.len() && input[(w + x.len()) as int] == tt) by {
                let p = x.push(tt);
                lemma_pattern_matching_in_bounds(input, p, m, Ignored::WhitespaceBytes);
                assert forall|k: int| 0 <= k < p.len() implies ((#[trigger] input[w + k] & m[k]) == p[k]) == (
                    if k < x.len() { input[w + k] == x[k] } else { input[w + k] == tt }) by {
                    lemma_mask_byte(input[w + k]);
                }
                if pattern_matching(input, p, m, Ignored::WhitespaceBytes) {
                    assert(input[(w + x.len()) as int] == tt);
                }
            }
            assert(rows[0].pattern == x.push(0x20));
            assert(rows[1].pattern == x.push(0x3E));
            assert(match_table(input, rows, 2) is None);
        },
    }
}

// ---------------------------------------------------------------------------
// Tables.
// ---------------------------------------------------------------------------

/// Matching from row `|a| + j` of `a + b` is matching from row `j` of `b`.
proof fn lemma_match_table_shift(input: Seq<u8>, a: Seq<Row>, b: Seq<Row>, j: nat)
    ensures
        match_table(input, a + b, a.len() + j) == match_table(input, b, j),
    decreases b.len() - j,
{
    if j < b.len() {
        assert((a + b)[(a.len() + j) as int] == b[j as int]);
        lemma_match_table_shift(input, a, b, j + 1);
    }
}

/// Matching `a + b` from row `i` of `a`: `a`'s rows, then `b`'s.
proof fn lemma_match_table_concat(input: Seq<u8>, a: Seq<Row>, b: Seq<Row>, i: nat)
    requires
        i <= a.len(),
    ensures
        match_table(input, a + b, i) == match match_table(input, a, i) {
            Some(t) => Some(t),
            None => match_table(input, b, 0),
        },
    decreases a.len() - i,
{
    if i < a.len() {
        assert((a + b)[i as int] == a[i as int]);
        lemma_match_table_concat(input, a, b, i + 1);
    } else {
        lemma_match_table_shift(input, a, b, 0);
    }
}

/// The expanded rows match as the entries do.
pub proof fn lemma_expand(input: Seq<u8>, entries: Seq<Entry>, i: nat)
    ensures
        match_table(input, expand(entries, i), 0) == first_match(input, entries, i),
    decreases entries.len() - i,
{
    if i < entries.len() {
        lemma_expand(input, entries, i + 1);
        lemma_match_table_concat(input, encode(entries[i as int]), expand(entries, i + 1), 0);
        lemma_encode(input, entries[i as int]);
    }
}

/// `a` and `b` agree field by field from row `i` on.
pub open spec fn rows_equal(a: Seq<Row>, b: Seq<Row>, i: nat) -> bool
    decreases a.len() - i
{
    a.len() == b.len() && (i >= a.len() || (a[i as int].pattern =~= b[i as int].pattern && a[i as int].mask =~= b[i as int].mask
        && (a[i as int].ignored is None) == (b[i as int].ignored is None)
        && a[i as int].computed.type_ =~= b[i as int].computed.type_ && a[i as int].computed.subtype =~= b[i as int].computed.subtype
        && a[i as int].computed.parameters.len() == 0 && b[i as int].computed.parameters.len() == 0 && rows_equal(a, b, i + 1)))
}

/// [`rows_equal`] is equality.
pub proof fn lemma_rows_equal(a: Seq<Row>, b: Seq<Row>, i: nat)
    requires
        rows_equal(a, b, i),
    ensures
        forall|j: int| i <= j < a.len() ==> #[trigger] a[j] == b[j],
    decreases a.len() - i,
{
    if i < a.len() {
        lemma_rows_equal(a, b, i + 1);
        assert(a[i as int].computed.parameters =~= b[i as int].computed.parameters);
        assert(a[i as int].computed == b[i as int].computed);
        assert(a[i as int].ignored == b[i as int].ignored);
    }
}

/// A spec table that equals the expanded entries matches as they do.
proof fn lemma_table(input: Seq<u8>, table: Seq<Row>, entries: Seq<Entry>)
    requires
        rows_equal(table, expand(entries, 0), 0),
    ensures
        match_table(input, table, 0) == first_match(input, entries, 0),
{
    lemma_rows_equal(table, expand(entries, 0), 0);
    assert(table =~= expand(entries, 0));
    lemma_expand(input, entries, 0);
}

/// §6.1's table is its notes: for every input, the image type pattern
/// matching algorithm agrees with [`indep_image`].
pub proof fn lemma_agree_image(input: Seq<u8>)
    ensures
        image_type_pattern_matching(input) == indep_image(input),
{
    super::checks::lemma_tables_evaluated();
    lemma_table(input, image_type_table(), image_entries());
}

/// §6.3 agrees with [`indep_font`].
pub proof fn lemma_agree_font(input: Seq<u8>)
    ensures
        font_type_pattern_matching(input) == indep_font(input),
{
    super::checks::lemma_tables_evaluated();
    lemma_table(input, font_type_table(), font_entries());
}

/// §6.4 agrees with [`indep_archive`].
pub proof fn lemma_agree_archive(input: Seq<u8>)
    ensures
        archive_type_pattern_matching(input) == indep_archive(input),
{
    super::checks::lemma_tables_evaluated();
    lemma_table(input, archive_type_table(), archive_entries());
}

/// §7.1's two tables agree with their notes.
pub proof fn lemma_agree_unknown_tables(input: Seq<u8>)
    ensures
        match_table(input, unknown_scriptable_table(), 0) == first_match(input, scriptable_entries(), 0),
        match_table(input, unknown_non_scriptable_table(), 0) == first_match(input, non_scriptable_entries(), 0),
{
    super::checks::lemma_tables_evaluated();
    lemma_table(input, unknown_scriptable_table(), scriptable_entries());
    lemma_table(input, unknown_non_scriptable_table(), non_scriptable_entries());
}

// ---------------------------------------------------------------------------
// MP4, §6.2, §7.1, §7.2.
// ---------------------------------------------------------------------------

/// Steps 8–10's loop, from bytes-read 16 + 4k, is "some compatible brand
/// from the kth on".
proof fn lemma_mp4_loop(input: Seq<u8>, k: nat)
    ensures
        mp4_loop(input, box_size(input), 16 + 4 * k) == exists|j: nat| j >= k && #[trigger] mp4_compatible_brand(input, j),
    decreases box_size(input) + 4 - (16 + 4 * k),
{
    let b = box_size(input);
    if 16 + 4 * k < b {
        lemma_mp4_loop(input, k + 1);
        assert(16 + 4 * k + 4 == 16 + 4 * (k + 1));
        if mp4_brand_at(input, (16 + 4 * k) as int) {
            assert(mp4_compatible_brand(input, k));
        } else {
            if exists|j: nat| j >= k && #[trigger] mp4_compatible_brand(input, j) {
                let j = choose|j: nat| j >= k && #[trigger] mp4_compatible_brand(input, j);
                assert(j != k);
                assert(j >= k + 1);
            }
        }
    } else {
        if exists|j: nat| j >= k && #[trigger] mp4_compatible_brand(input, j) {
            let j = choose|j: nat| j >= k && #[trigger] mp4_compatible_brand(input, j);
            assert(16 + 4 * j >= 16 + 4 * k) by (nonlinear_arith)
                requires
                    j >= k,
            ;
        }
    }
}

/// §6.2.1 agrees with the `FileTypeBox` reading, [`indep_mp4`].
pub proof fn lemma_agree_mp4(input: Seq<u8>)
    ensures
        matches_mp4(input) == indep_mp4(input),
{
    if input.len() >= 12 {
        lemma_mp4_loop(input, 0);
        assert(16 + 4 * 0nat == 16);
        assert forall|j: nat| #[trigger] mp4_compatible_brand(input, j) implies j >= 0 by {}
    }
}

/// A file whose `ftyp` box passes steps 3–6 and whose `j`th compatible
/// brand starts with "mp4" matches the MP4 signature. (For certificates:
/// no quantifier to evaluate.)
pub proof fn lemma_mp4_compatible_brand(input: Seq<u8>, j: nat)
    ensures
        ftyp_box(input) && mp4_compatible_brand(input, j) ==> matches_mp4(input),
{
    lemma_agree_mp4(input);
}

/// §6.2 agrees with [`indep_audio_or_video`], given the spec's WebM and
/// MP3-without-ID3 results.
pub proof fn lemma_agree_audio_or_video(input: Seq<u8>)
    ensures
        audio_or_video_type_pattern_matching(input) == indep_audio_or_video(input, matches_webm(input), matches_mp3_without_id3(input)),
{
    super::checks::lemma_tables_evaluated();
    lemma_table(input, audio_or_video_type_table(), audio_or_video_entries());
    lemma_agree_mp4(input);
    assert(mime_type(seq![0x76u32, 0x69, 0x64, 0x65, 0x6F], seq![0x6Du32, 0x70, 0x34]) == literal(s_video(), seq![0x6Du32, 0x70, 0x34]));
}

/// §7.1 agrees with [`indep_identify_unknown`], given the spec's WebM and
/// MP3-without-ID3 results.
pub proof fn lemma_agree_identify_unknown(input: Seq<u8>, sniff_scriptable: bool)
    ensures
        identify_unknown_mime_type(input, sniff_scriptable)
            == indep_identify_unknown(input, sniff_scriptable, matches_webm(input), matches_mp3_without_id3(input)),
{
    lemma_agree_unknown_tables(input);
    lemma_agree_image(input);
    lemma_agree_audio_or_video(input);
    lemma_agree_archive(input);
    lemma_no_binary_data(input);
    assert(mime_type(s_text(), s_plain()) == literal(s_text(), s_plain()));
}

/// §7.2 agrees with [`indep_text_or_binary`].
pub proof fn lemma_agree_text_or_binary(input: Seq<u8>)
    ensures
        distinguish_text_or_binary(input) == indep_text_or_binary(input),
{
    lemma_no_binary_data(input);
    lemma_begins_with_at(input, 0, seq![0xFEu8, 0xFF], false);
    lemma_begins_with_at(input, 0, seq![0xFFu8, 0xFE], false);
    lemma_begins_with_at(input, 0, seq![0xEFu8, 0xBB, 0xBF], false);
    if input.len() >= 2 {
        assert(input[0int + 0] == input[0] && input[0int + 1] == input[1]);
    }
    if input.len() >= 3 {
        assert(input[0int + 2] == input[2]);
    }
}

} // verus!
