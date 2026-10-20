//! Executable-style specification of MIME type sniffing, transcribed from
//! the WHATWG MIME Sniffing Standard §3, §5–§7. Nothing here runs; it
//! defines what "correct" means. Each `// N.` comment is the step number
//! in the cited algorithm.
//!
//! Source: MIME Sniffing Standard, Living Standard, last updated 19 October
//! 2026, commit `ba4b3c385b9765ddfe4a994e2bb89e0ab96068e2`,
//! <https://mimesniff.spec.whatwg.org/>: §3 (binary data byte, whitespace
//! byte, tag-terminating byte), §5.1 the check-for-apache-bug table, §6 the
//! pattern matching algorithm, §6.1–§6.4 the image, audio or video, font
//! and archive type pattern matching algorithms with their tables, §6.2.1–
//! §6.2.3 the MP4, WebM and MP3-without-ID3 signatures, §7 the MIME type
//! sniffing algorithm, §7.1 the rules for identifying an unknown MIME type,
//! §7.2 the rules for distinguishing if a resource is text or binary.
//! MIME types are the records of [`crate::mime_type::spec`].
//!
//! The pattern tables below were generated from the pinned commit's
//! `mimesniff.bs` (each row keeps the standard's note and its four cells as
//! a comment, so it can be read against the standard row by row).
//!
//! Not transcribed: §5.1's other steps (how a user agent obtains the
//! supplied MIME type depends on how it retrieved the resource; Fetch now
//! does this for HTTP), §5.2 reading the resource header (the header is an
//! input here; how many bytes to wait for is the caller's choice), and §8
//! context-specific sniffing.
//!
//! Modelling choices (each one is a deliberate, reviewable deviation in form,
//! never in meaning):
//! - A byte sequence is a `Seq<u8>`, a MIME type a [`MimeTypeRecord`](crate::mime_type::spec::MimeTypeRecord);
//!   "undefined" is `None`. A MIME type the standard writes as a literal
//!   ("text/html") is the record with that type and subtype and no
//!   parameters, which is what parsing the literal gives.
//! - A resource ([`Resource`]) is its supplied MIME type, its
//!   check-for-apache-bug and no-sniff flags, and its resource header.
//!   "Supported by the user agent" is not defined by the standard; it is an
//!   input, `supported`, that says whether the supplied MIME type is.
//! - "Abort these steps" after "If X, the computed MIME type is Y." in §7
//!   belongs to the condition: read unconditionally, step 1 would end the
//!   algorithm for every resource and steps 2–8 could never run.
//! - A table row whose byte pattern has "TT" (a tag-terminating byte: 0x20
//!   or 0x3E) is two rows, one per byte, in that order. The row matches
//!   exactly when either does, and both give the same MIME type, so the
//!   table's result is unchanged.
//! - "Leading bytes to be ignored" is [`Ignored`]: none, or whitespace
//!   bytes.
//! - "/" in §6.2.3 is integer division returning the quotient (Encoding's
//!   operators, which §3 adopts); all operands are non-negative.
//! - Numbers in §6.2.2 and §6.2.3 are `nat`s; bytes stay `u8` for the bit
//!   operations.
//!
//! Errata (see `docs/ERRATA.md`; each is marked where it applies):
//! - §6 pattern matching reads `input[s]` past the end of input when
//!   leading ignored bytes leave fewer bytes than the pattern. We return
//!   false there.
//! - §6.2.2 WebM: the two-byte comparison reads one byte past the end when
//!   iter is length − 1; "parse a vint" starts at index 0 instead of iter;
//!   "abort these steps" inside it can only mean leaving its loop; and
//!   "matching a padded sequence" is called without the end it is defined
//!   with. We compare only when two bytes remain, start at iter, leave the
//!   loop, and let end be wherever the pattern, after any 0x00 bytes,
//!   ends.
//! - §6.2.3 MP3 without ID3: step 2 of "match an mp3 header" says "and"
//!   where it must say "or"; its length check ignores the offset; "&" and
//!   ">>" in "sequence[s as int + 1] & 0x06 >> 1" bind as in Mozilla's
//!   `mp3sniff.c`, which the algorithm is taken from; step 7 compares with
//!   "s − length", always ≤ 0; and the bitrate table and scale are chosen
//!   by the MPEG version bit the other way round from MPEG audio (and
//!   from `mp3sniff.c`), which makes ordinary MPEG-1 Layer III files fail.
//!   We specify `mp3sniff.c`'s behaviour for each.

#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ===========================================================================
// §3 byte classes.
// ===========================================================================

/// A binary data byte (§3): "0x00 to 0x08 (NUL to BS), the byte 0x0B (VT),
/// a byte in the range 0x0E to 0x1A (SO to SUB), or a byte in the range
/// 0x1C to 0x1F (FS to US)."
pub open spec fn is_binary_data_byte(b: u8) -> bool {
    b <= 0x08 || b == 0x0B || (0x0E <= b <= 0x1A) || (0x1C <= b <= 0x1F)
}

/// A whitespace byte (§3): "0x09 (HT), 0x0A (LF), 0x0C (FF), 0x0D (CR),
/// 0x20 (SP)."
pub open spec fn is_whitespace_byte(b: u8) -> bool {
    b == 0x09 || b == 0x0A || b == 0x0C || b == 0x0D || b == 0x20
}

/// `bytes` contains a binary data byte.
pub open spec fn contains_binary_data_byte(bytes: Seq<u8>) -> bool
    decreases bytes.len()
{
    bytes.len() > 0 && (is_binary_data_byte(bytes[0]) || contains_binary_data_byte(bytes.drop_first()))
}

/// A MIME type the standard writes as a literal: this type and subtype, no
/// parameters.
pub open spec fn mime_type(type_: Seq<u32>, subtype: Seq<u32>) -> crate::mime_type::spec::MimeTypeRecord {
    crate::mime_type::spec::MimeTypeRecord { type_, subtype, parameters: seq![] }
}

// ===========================================================================
// §6 Matching a MIME type pattern.
// ===========================================================================

/// The bytes to be ignored at the start of the input.
pub enum Ignored {
    /// "None."
    None,
    /// "Whitespace bytes." (0xWS)
    WhitespaceBytes,
}

/// "ignored contains `b`".
pub open spec fn ignored_contains(ignored: Ignored, b: u8) -> bool {
    match ignored {
        Ignored::None => false,
        Ignored::WhitespaceBytes => is_whitespace_byte(b),
    }
}

/// Pattern matching algorithm, step 4: "While s < input's length:" skip
/// ignored bytes. Returns s.
pub open spec fn skip_ignored(input: Seq<u8>, s: nat, ignored: Ignored) -> nat
    decreases input.len() - s
{
    if s < input.len() {
        if !ignored_contains(ignored, input[s as int]) {
            // 4.1 "If ignored does not contain input[s], break."
            s
        } else {
            // 4.2 "Set s to s + 1."
            skip_ignored(input, s + 1, ignored)
        }
    } else {
        s
    }
}

/// Pattern matching algorithm, step 6: "While p < pattern's length:".
pub open spec fn compare_pattern(input: Seq<u8>, pattern: Seq<u8>, mask: Seq<u8>, s: nat, p: nat) -> bool
    decreases pattern.len() - p
{
    if p < pattern.len() {
        if s >= input.len() {
            // Erratum: step 6.1 would read input[s] past the end of input
            // (step 2 checks the length before step 4 skips bytes). No byte
            // there matches, so return false.
            false
        } else {
            // 6.1 "Let maskedData be the result of applying the bitwise AND
            //     operator to input[s] and mask[p]."
            let masked_data = input[s as int] & mask[p as int];
            if masked_data != pattern[p as int] {
                // 6.2 "If maskedData is not equal to pattern[p], return false."
                false
            } else {
                // 6.3 "Set s to s + 1." 6.4 "Set p to p + 1."
                compare_pattern(input, pattern, mask, s + 1, p + 1)
            }
        }
    } else {
        // 7. "Return true."
        true
    }
}

/// The pattern matching algorithm (§6, #pattern-matching-algorithm).
pub open spec fn pattern_matching(input: Seq<u8>, pattern: Seq<u8>, mask: Seq<u8>, ignored: Ignored) -> bool {
    // 1. "Assert: pattern's length is equal to mask's length." Every row of
    //    every table below meets it (`lemmas::lemma_tables_well_formed`).
    if input.len() < pattern.len() {
        // 2. "If input's length is less than pattern's length, return false."
        false
    } else {
        // 3. "Let s be 0." 4. skip ignored bytes.
        let s = skip_ignored(input, 0, ignored);
        // 5. "Let p be 0." 6–7.
        compare_pattern(input, pattern, mask, s, 0)
    }
}

/// A row of a pattern table: byte pattern, pattern mask, leading bytes to
/// be ignored, and the MIME type it gives.
pub struct Row {
    /// Byte Pattern
    pub pattern: Seq<u8>,
    /// Pattern Mask
    pub mask: Seq<u8>,
    /// Leading Bytes to Be Ignored
    pub ignored: Ignored,
    /// The MIME type (fourth column)
    pub computed: crate::mime_type::spec::MimeTypeRecord,
}

/// "Execute the following steps for each row row in the following table:
/// 1. Let patternMatched be the result of the pattern matching algorithm
/// given input, [the row's first three columns]. 2. If patternMatched is
/// true, return the value in the fourth column of row." From row `i` on;
/// `None` when no row matches.
pub open spec fn match_table(input: Seq<u8>, table: Seq<Row>, i: nat) -> Option<crate::mime_type::spec::MimeTypeRecord>
    decreases table.len() - i
{
    if i < table.len() {
        let row = table[i as int];
        if pattern_matching(input, row.pattern, row.mask, row.ignored) {
            Some(row.computed)
        } else {
            match_table(input, table, i + 1)
        }
    } else {
        None
    }
}

/// The image type pattern matching algorithm (§6.1): the table, then
/// "Return undefined."
pub open spec fn image_type_pattern_matching(input: Seq<u8>) -> Option<crate::mime_type::spec::MimeTypeRecord> {
    match_table(input, image_type_table(), 0)
}

/// The audio or video type pattern matching algorithm (§6.2).
pub open spec fn audio_or_video_type_pattern_matching(input: Seq<u8>) -> Option<crate::mime_type::spec::MimeTypeRecord> {
    match match_table(input, audio_or_video_type_table(), 0) {
        // 1. the table.
        Some(t) => Some(t),
        None => if matches_mp4(input) {
            // 2. "If input matches the signature for MP4, return "video/mp4"."
            Some(mime_type(seq![0x76u32, 0x69, 0x64, 0x65, 0x6F], seq![0x6Du32, 0x70, 0x34]))
        } else if matches_webm(input) {
            // 3. "If input matches the signature for WebM, return "video/webm"."
            Some(mime_type(seq![0x76u32, 0x69, 0x64, 0x65, 0x6F], seq![0x77u32, 0x65, 0x62, 0x6D]))
        } else if matches_mp3_without_id3(input) {
            // 4. "If input matches the signature for MP3 without ID3, return
            //    "audio/mpeg"."
            Some(mime_type(seq![0x61u32, 0x75, 0x64, 0x69, 0x6F], seq![0x6Du32, 0x70, 0x65, 0x67]))
        } else {
            // 5. "Return undefined."
            None
        },
    }
}

/// The font type pattern matching algorithm (§6.3).
pub open spec fn font_type_pattern_matching(input: Seq<u8>) -> Option<crate::mime_type::spec::MimeTypeRecord> {
    match_table(input, font_type_table(), 0)
}

/// The archive type pattern matching algorithm (§6.4).
pub open spec fn archive_type_pattern_matching(input: Seq<u8>) -> Option<crate::mime_type::spec::MimeTypeRecord> {
    match_table(input, archive_type_table(), 0)
}

// ===========================================================================
// §6.2.1 Signature for MP4.
// ===========================================================================

/// `sequence[i..i+3]` is "mp4" (0x6D 0x70 0x34).
pub open spec fn is_mp4_at(sequence: Seq<u8>, i: int) -> bool {
    sequence[i] == 0x6D && sequence[i + 1] == 0x70 && sequence[i + 2] == 0x34
}

/// Signature for MP4, step 9: "While bytes-read is less than box-size,
/// continuously loop through these steps:".
pub open spec fn mp4_loop(sequence: Seq<u8>, box_size: nat, bytes_read: nat) -> bool
    decreases box_size + 4 - bytes_read
{
    if bytes_read < box_size {
        if is_mp4_at(sequence, bytes_read as int) {
            // 9.1 "If the three bytes from sequence[bytes-read] to
            //     sequence[bytes-read + 2] are equal to 0x6D 0x70 0x34
            //     ("mp4"), return true."
            true
        } else {
            // 9.2 "Increment bytes-read by 4."
            mp4_loop(sequence, box_size, bytes_read + 4)
        }
    } else {
        // 10. "Return false."
        false
    }
}

/// Matches the signature for MP4 (§6.2.1, #signature-for-mp4).
pub open spec fn matches_mp4(sequence: Seq<u8>) -> bool {
    // 1. sequence; 2. "Let length be the number of bytes in sequence."
    let length = sequence.len();
    if length < 12 {
        // 3. "If length is less than 12, return false."
        false
    } else {
        // 4. "Let box-size be the four bytes from sequence[0] to sequence[3],
        //    interpreted as a 32-bit unsigned big-endian integer."
        let box_size = sequence[0] as nat * 0x100_0000 + sequence[1] as nat * 0x1_0000
            + sequence[2] as nat * 0x100 + sequence[3] as nat;
        if length < box_size || box_size % 4 != 0 {
            // 5. "If length is less than box-size or if box-size modulo 4 is
            //    not equal to 0, return false."
            false
        } else if !(sequence[4] == 0x66 && sequence[5] == 0x74 && sequence[6] == 0x79 && sequence[7] == 0x70) {
            // 6. "If the four bytes from sequence[4] to sequence[7] are not
            //    equal to 0x66 0x74 0x79 0x70 ("ftyp"), return false."
            false
        } else if is_mp4_at(sequence, 8) {
            // 7. "If the three bytes from sequence[8] to sequence[10] are
            //    equal to 0x6D 0x70 0x34 ("mp4"), return true."
            true
        } else {
            // 8. "Let bytes-read be 16." 9–10. the loop.
            mp4_loop(sequence, box_size, 16)
        }
    }
}

// ===========================================================================
// §6.2.2 Signature for WebM.
// ===========================================================================

/// Parse a vint, step 5: "While number size is less than max vint length,
/// and less than length, continuously loop through these steps:". Returns
/// (mask, number size).
pub open spec fn vint_size_loop(byte: u8, length: nat, mask: u8, number_size: nat) -> (u8, nat)
    decreases 8 - number_size
{
    if number_size < 8 && number_size < length {
        if byte & mask != 0 {
            // 5.1 "If the sequence[index] & mask is not zero, abort these
            //     steps." Erratum: aborting the whole algorithm would leave
            //     nothing to return; this leaves the loop.
            (mask, number_size)
        } else {
            // 5.2 "Let mask be the value of mask >> 1."
            // 5.3 "Increment number size by one."
            vint_size_loop(byte, length, mask >> 1u8, number_size + 1)
        }
    } else {
        (mask, number_size)
    }
}

/// Parse a vint, step 9: "While bytes remaining is not zero, execute these
/// steps:". Returns parsed number.
pub open spec fn vint_number_loop(sequence: Seq<u8>, length: nat, parsed_number: nat, index: nat, bytes_remaining: nat) -> nat
    decreases bytes_remaining
{
    if bytes_remaining != 0 {
        // 9.1 "Let parsed number be parsed number << 8."
        // 9.2 "Let parsed number be parsed number | sequence[index]."
        let parsed_number = parsed_number * 0x100 + sequence[index as int] as nat;
        // 9.3 "Increment index by one."
        let index = index + 1;
        if index >= length {
            // 9.4 "If index is greater or equal than length, abort these
            //     steps." (As in step 5.1, this leaves the loop.)
            parsed_number
        } else {
            // 9.5 "Decrement bytes remaining by one."
            vint_number_loop(sequence, length, parsed_number, index, (bytes_remaining - 1) as nat)
        }
    } else {
        parsed_number
    }
}

/// Parse a vint (§6.2.2, #parse-a-vint) on `sequence`, starting at index
/// `iter`. Returns (parsed number, number size).
pub open spec fn parse_a_vint(sequence: Seq<u8>, iter: nat) -> (nat, nat) {
    let length = sequence.len();
    // 1. "Let mask be 128." 2. "Let max vint length be 8."
    // 3. "Let number size be 1."
    // 4. "Let index be 0." Erratum: the algorithm is "starting at index
    //    iter", and index 0 is always 0x1A, the first byte of the EBML
    //    signature its one caller has already checked; we let index be iter.
    let index = iter;
    // 5. the loop.
    let (mask, number_size) = vint_size_loop(sequence[index as int], length, 128, 1);
    // 6. "Let parsed number be sequence[index] & ~mask."
    let parsed_number = (sequence[index as int] & !mask) as nat;
    // 7. "Increment index by one."
    // 8. "Let bytes remaining be the value of number size - 1."
    // 9. the loop. 10. "Return parsed number and number size".
    (vint_number_loop(sequence, length, parsed_number, index + 1, (number_size - 1) as nat), number_size)
}

/// Where the 0x00 bytes starting at `i` end.
pub open spec fn skip_zero_bytes(sequence: Seq<u8>, i: nat) -> nat
    decreases sequence.len() - i
{
    if i < sequence.len() && sequence[i as int] == 0x00 {
        skip_zero_bytes(sequence, i + 1)
    } else {
        i
    }
}

/// Matching a padded sequence `pattern` on `sequence` at `offset`
/// (§6.2.2, #matching-a-padded-sequence): "true if sequence has a length
/// greater than end, and contains exactly, in the range [offset, end], the
/// bytes in pattern, in the same order, eventually preceded by bytes with a
/// value of 0x00". Erratum: the caller gives no end; we let end be the
/// last byte of the pattern after the 0x00 bytes.
pub open spec fn matches_padded_sequence(pattern: Seq<u8>, sequence: Seq<u8>, offset: nat) -> bool {
    let start = skip_zero_bytes(sequence, offset);
    start + pattern.len() <= sequence.len() && sequence.subrange(start as int, start + pattern.len() as int) == pattern
}

/// Signature for WebM, step 6: "While iter is less than length and iter is
/// less than 38, continuously loop through these steps:".
pub open spec fn webm_loop(sequence: Seq<u8>, iter: nat) -> bool
    decreases if iter < 38 { 38 - iter } else { 0 }
{
    let length = sequence.len();
    if iter < length && iter < 38 {
        // 6.1 "If the two bytes from sequence[iter] to sequence[iter as int + 1]
        //     are equal to 0x42 0x82," Erratum: when iter is length − 1 there
        //     is no sequence[iter as int + 1]; the two bytes are then not 0x42 0x82.
        if iter + 1 < length && sequence[iter as int] == 0x42 && sequence[iter as int + 1] == 0x82 {
            // 6.1.1 "Increment iter by 2."
            let iter = iter + 2;
            if iter >= length {
                // 6.1.2 "If iter is greater or equal than length, abort these
                //       steps." (Nothing matched: false.)
                false
            } else {
                // 6.1.3 "Let number size be the result of parsing a vint
                //       starting at sequence[iter]."
                let number_size = parse_a_vint(sequence, iter).1;
                // 6.1.4 "Increment iter by number size."
                let iter = iter + number_size;
                if iter + 4 >= length {
                    // 6.1.5 "If iter is greater than or equal to length - 4,
                    //       abort these steps."
                    false
                } else if matches_padded_sequence(seq![0x77u8, 0x65, 0x62, 0x6D], sequence, iter) {
                    // 6.1.6 matched = matching a padded sequence "webm".
                    // 6.1.7 "If matched is true, abort these steps and
                    //       return true."
                    true
                } else {
                    // 6.2 "Increment iter by 1."
                    webm_loop(sequence, iter + 1)
                }
            }
        } else {
            // 6.2 "Increment iter by 1."
            webm_loop(sequence, iter + 1)
        }
    } else {
        // 7. "Return false."
        false
    }
}

/// Matches the signature for WebM (§6.2.2, #signature-for-webm).
pub open spec fn matches_webm(sequence: Seq<u8>) -> bool {
    // 1. sequence; 2. "Let length be the number of bytes in sequence."
    let length = sequence.len();
    if length < 4 {
        // 3. "If length is less than 4, return false."
        false
    } else if !(sequence[0] == 0x1A && sequence[1] == 0x45 && sequence[2] == 0xDF && sequence[3] == 0xA3) {
        // 4. "If the four bytes from sequence[0] to sequence[3], are not
        //    equal to 0x1A 0x45 0xDF 0xA3, return false."
        false
    } else {
        // 5. "Let iter be 4." 6–7. the loop.
        webm_loop(sequence, 4)
    }
}

// ===========================================================================
// §6.2.3 Signature for MP3 without ID3.
// ===========================================================================

/// Match an mp3 header (§6.2.3, #match-an-mp3-header) in `sequence` at
/// offset `s`.
pub open spec fn match_an_mp3_header(sequence: Seq<u8>, s: nat) -> bool {
    let length = sequence.len();
    if length < s + 4 {
        // 1. "If length is less than 4, return false." Erratum: the header
        //    is read at offset s (the second call has s > 0), so the four
        //    bytes needed are from s on: `mp3sniff.c` checks the bytes
        //    available after the offset.
        false
    } else if sequence[s as int] != 0xFF || (sequence[s as int + 1] & 0xE0) != 0xE0 {
        // 2. "If sequence[s] is not equal to 0xff and sequence[s as int + 1] & 0xe0
        //    is not equal to 0xe0, return false." Erratum: "or" (a frame
        //    sync needs both, as in `mp3sniff.c`); with "and", 0xFF 0x00 ...
        //    would pass.
        false
    } else {
        // 3. "Let layer be the result of sequence[s as int + 1] & 0x06 >> 1."
        //    Erratum: (sequence[s as int + 1] & 0x06) >> 1, as in `mp3sniff.c`;
        //    0x06 >> 1 first would test a different bit.
        let layer = (sequence[s as int + 1] & 0x06) >> 1u8;
        // 5. "Let bit-rate be sequence[s as int + 2] & 0xf0 >> 4." (Same.)
        let bit_rate = (sequence[s as int + 2] & 0xF0) >> 4u8;
        // 7. "Let sample-rate be sequence[s as int + 2] & 0x0c >> 2." (Same.)
        let sample_rate = (sequence[s as int + 2] & 0x0C) >> 2u8;
        // 10. "Let final-layer be the result of 4 - ((sequence[s as int + 1] &
        //     0x06) >> 1)."
        let final_layer = 4 - layer;
        if layer == 0 {
            // 4. "If layer is 0, return false."
            false
        } else if bit_rate == 15 {
            // 6. "If bit-rate is 15, return false."
            false
        } else if sample_rate == 3 {
            // 8. "If sample-rate is 3, return false."
            false
        } else {
            // 9. "Let freq be the value given by sample-rate in the table
            //    sample-rate." (Unused here.)
            // 11. "If final-layer is not 3, return false." 12. "Return true."
            final_layer == 3
        }
    }
}

/// What "parse an mp3 frame" sets: version, bitrate, samplerate, pad.
pub struct Mp3Frame {
    /// version
    pub version: u8,
    /// bitrate
    pub bitrate: nat,
    /// samplerate
    pub samplerate: nat,
    /// pad
    pub pad: u8,
}

/// Parse an mp3 frame (§6.2.3, #parse-an-mp3-frame) in `sequence` at offset
/// `s`. Only called after "match an mp3 header" accepted the same bytes, so
/// bitrate-index is not 15 and samplerate-index is not 3.
pub open spec fn parse_an_mp3_frame(sequence: Seq<u8>, s: nat) -> Mp3Frame {
    // 1. "Let version be sequence[s as int + 1] & 0x18 >> 3." (Erratum as in match
    //    an mp3 header step 3: the AND first.)
    let version = (sequence[s as int + 1] & 0x18) >> 3u8;
    // 2. "Let bitrate-index be sequence[s as int + 2] & 0xf0 >> 4."
    let bitrate_index = ((sequence[s as int + 2] & 0xF0) >> 4u8) as int;
    // 3. "If the version & 0x01 is non-zero, let bitrate be the value given
    //    by bitrate-index in the table mp2.5-rates"
    // 4. "If version & 0x01 is zero, let bitrate be the value given by
    //    bitrate-index in the table mp3-rates"
    //    Erratum: the other way round. Version 3 (0b11) is MPEG-1, whose
    //    Layer III bitrates are the mp3-rates table; versions 2 and 0 are
    //    MPEG-2 and 2.5 (mp2.5-rates). `mp3sniff.c` picks the MPEG-1 table
    //    when version & 1 is non-zero.
    let bitrate = if version & 0x01 != 0 { mp3_rates()[bitrate_index] } else { mp2_5_rates()[bitrate_index] };
    // 5. "Let samplerate-index be sequence[s as int + 2] & 0x0c >> 2."
    let samplerate_index = ((sequence[s as int + 2] & 0x0C) >> 2u8) as int;
    // 6. "Let samplerate be the value given by samplerate-index in the
    //    sample-rate table."
    let samplerate = sample_rates()[samplerate_index];
    // 7. "If version is 2, let samplerate be the result of samplerate / 2."
    // 8. "If version is 0, let samplerate be the result of samplerate / 4."
    let samplerate = if version == 2 { samplerate / 2 } else if version == 0 { samplerate / 4 } else { samplerate };
    // 9. "Let pad be sequence[s as int + 2] & 0x02 >> 1."
    let pad = (sequence[s as int + 2] & 0x02) >> 1u8;
    Mp3Frame { version, bitrate, samplerate, pad }
}

/// Compute an mp3 frame size (§6.2.3, #compute-an-mp3-frame-size).
pub open spec fn compute_an_mp3_frame_size(frame: Mp3Frame) -> nat {
    // 1. "If version is 1, let scale be 72, else, let scale be 144."
    //    Erratum: MPEG-1 Layer III frames hold 1152 samples (scale 144),
    //    MPEG-2 and 2.5 hold 576 (72). `mp3sniff.c`: 72 when version & 1 is
    //    zero, else 144.
    let scale: nat = if frame.version & 0x01 == 0 { 72 } else { 144 };
    // 2. "Let size be bitrate * scale / freq." (freq is the samplerate of
    //    parse an mp3 frame; never 0.)
    let size = frame.bitrate * scale / frame.samplerate;
    // 3. "If pad is not zero, increment size by 1." 4. "Return size."
    if frame.pad != 0 { size + 1 } else { size }
}

/// Matches the signature for MP3 without ID3 (§6.2.3,
/// #signature-for-mp3-without-id3).
pub open spec fn matches_mp3_without_id3(sequence: Seq<u8>) -> bool {
    // 1. sequence; 2. "Let length be the number of bytes in sequence."
    let length = sequence.len();
    // 3. "Initialize s to 0."
    let s = 0nat;
    if !match_an_mp3_header(sequence, s) {
        // 4. "If the result of the operation match mp3 header is false,
        //    return false."
        false
    } else {
        // 5. "Parse an mp3 frame on sequence at offset s"
        let frame = parse_an_mp3_frame(sequence, s);
        // 6. "Let skipped-bytes [be] the return value of the execution of
        //    mp3 framesize computation"
        let skipped_bytes = compute_an_mp3_frame_size(frame);
        if skipped_bytes < 4 || skipped_bytes > length - s {
            // 7. "If skipped-bytes is less than 4, or skipped-bytes is
            //    greater than s - length, return false." Erratum: s − length
            //    is never positive, so read literally every frame fails;
            //    we take length − s, the bytes left.
            false
        } else {
            // 8. "Increment s by skipped-bytes."
            let s = s + skipped_bytes;
            // 9. "If the result of the operation match mp3 header operation
            //    is false, return false, else, return true."
            match_an_mp3_header(sequence, s)
        }
    }
}

// ===========================================================================
// §5.1 check-for-apache-bug, §7 determining the computed MIME type.
// ===========================================================================

/// `s` is one of `list`.
pub open spec fn is_one_of_bytes(s: Seq<u8>, list: Seq<Seq<u8>>) -> bool
    decreases list.len()
{
    list.len() > 0 && (s == list[0] || is_one_of_bytes(s, list.drop_first()))
}

/// §5.1 step 2.1.2: "Set the check-for-apache-bug flag if supplied-type is
/// exactly equal to one of the values in the following table", given the
/// value of the last Content-Type header.
pub open spec fn check_for_apache_bug(supplied_type: Seq<u8>) -> bool {
    is_one_of_bytes(supplied_type, apache_bug_values())
}

/// A resource and the metadata §5 says a user agent tracks for it.
pub struct Resource {
    /// The supplied MIME type; `None` is undefined.
    pub supplied: Option<crate::mime_type::spec::MimeTypeRecord>,
    /// The check-for-apache-bug flag.
    pub check_for_apache_bug: bool,
    /// The no-sniff flag.
    pub no_sniff: bool,
    /// The resource header.
    pub header: Seq<u8>,
}

/// The rules for distinguishing if a resource is text or binary (§7.2).
pub open spec fn distinguish_text_or_binary(header: Seq<u8>) -> crate::mime_type::spec::MimeTypeRecord {
    // 1. "Let length be the number of bytes in the resource header."
    let length = header.len();
    let text_plain = mime_type(seq![0x74u32, 0x65, 0x78, 0x74], seq![0x70u32, 0x6C, 0x61, 0x69, 0x6E]);
    if length >= 2 && ((header[0] == 0xFE && header[1] == 0xFF) || (header[0] == 0xFF && header[1] == 0xFE)) {
        // 2. "If length is greater than or equal to 2 and the first 2 bytes
        //    of the resource header are equal to 0xFE 0xFF (UTF-16BE BOM) or
        //    0xFF 0xFE (UTF-16LE BOM), the computed MIME type is
        //    "text/plain"."
        text_plain
    } else if length >= 3 && header[0] == 0xEF && header[1] == 0xBB && header[2] == 0xBF {
        // 3. "If length is greater than or equal to 3 and the first 3 bytes
        //    of the resource header are equal to 0xEF 0xBB 0xBF (UTF-8 BOM),
        //    the computed MIME type is "text/plain"."
        text_plain
    } else if !contains_binary_data_byte(header) {
        // 4. "If the resource header contains no binary data bytes, the
        //    computed MIME type is "text/plain"."
        text_plain
    } else {
        // 5. "The computed MIME type is "application/octet-stream"."
        mime_type(seq![0x61u32, 0x70, 0x70, 0x6C, 0x69, 0x63, 0x61, 0x74, 0x69, 0x6F, 0x6E],
            seq![0x6Fu32, 0x63, 0x74, 0x65, 0x74, 0x2D, 0x73, 0x74, 0x72, 0x65, 0x61, 0x6D])
    }
}

/// The rules for identifying an unknown MIME type (§7.1), given the
/// resource header and the sniff-scriptable flag.
pub open spec fn identify_unknown_mime_type(header: Seq<u8>, sniff_scriptable: bool) -> crate::mime_type::spec::MimeTypeRecord {
    // 1. "If the sniff-scriptable flag is set, execute the following steps
    //    for each row row in the following table:" (returns on a match)
    let scriptable = if sniff_scriptable { match_table(header, unknown_scriptable_table(), 0) } else { None };
    match scriptable {
        Some(t) => t,
        // 2. the second table.
        None => match match_table(header, unknown_non_scriptable_table(), 0) {
            Some(t) => t,
            // 3. "Let matchedType be the result of executing the image type
            //    pattern matching algorithm given resource's resource header."
            // 4. "If matchedType is not undefined, return matchedType."
            None => match image_type_pattern_matching(header) {
                Some(t) => t,
                // 5–6. the same for the audio or video type pattern matching
                //      algorithm.
                None => match audio_or_video_type_pattern_matching(header) {
                    Some(t) => t,
                    // (Font sniffing is commented out in the standard.)
                    // 7–8. the same for the archive type pattern matching
                    //      algorithm.
                    None => match archive_type_pattern_matching(header) {
                        Some(t) => t,
                        None => if !contains_binary_data_byte(header) {
                            // 9. "If resource's resource header contains no
                            //    binary data bytes, return "text/plain"."
                            mime_type(seq![0x74u32, 0x65, 0x78, 0x74], seq![0x70u32, 0x6C, 0x61, 0x69, 0x6E])
                        } else {
                            // 10. "Return "application/octet-stream"."
                            mime_type(seq![0x61u32, 0x70, 0x70, 0x6C, 0x69, 0x63, 0x61, 0x74, 0x69, 0x6F, 0x6E],
                                seq![0x6Fu32, 0x63, 0x74, 0x65, 0x74, 0x2D, 0x73, 0x74, 0x72, 0x65, 0x61, 0x6D])
                        },
                    },
                },
            },
        },
    }
}

/// The supplied MIME type's essence is "unknown/unknown",
/// "application/unknown", or "*/*" (§7 step 2).
pub open spec fn is_unknown_essence(m: crate::mime_type::spec::MimeTypeRecord) -> bool {
    let e = crate::mime_type::spec::essence(m);
    // unknown/unknown
    e == seq![0x75u32, 0x6E, 0x6B, 0x6E, 0x6F, 0x77, 0x6E, 0x2F, 0x75, 0x6E, 0x6B, 0x6E, 0x6F, 0x77, 0x6E]
    // application/unknown
    || e == seq![0x61u32, 0x70, 0x70, 0x6C, 0x69, 0x63, 0x61, 0x74, 0x69, 0x6F, 0x6E, 0x2F, 0x75, 0x6E, 0x6B, 0x6E, 0x6F, 0x77, 0x6E]
    // */*
    || e == seq![0x2Au32, 0x2F, 0x2A]
}

/// The MIME type sniffing algorithm (§7,
/// #determining-the-computed-mime-type-of-a-resource): the computed MIME
/// type of `resource`. `supported`: the supplied MIME type is supported by
/// the user agent.
pub open spec fn computed_mime_type(resource: Resource, supported: bool) -> crate::mime_type::spec::MimeTypeRecord {
    match resource.supplied {
        Some(supplied) if crate::mime_type::spec::is_xml_mime_type(supplied) || crate::mime_type::spec::is_html_mime_type(supplied) => {
            // 1. "If the supplied MIME type is an XML MIME type or HTML MIME
            //    type, the computed MIME type is the supplied MIME type.
            //    Abort these steps."
            supplied
        },
        Some(supplied) if !is_unknown_essence(supplied) => {
            if resource.no_sniff {
                // 3. "If the no-sniff flag is set, the computed MIME type is
                //    the supplied MIME type. Abort these steps."
                supplied
            } else if resource.check_for_apache_bug {
                // 4. "If the check-for-apache-bug flag is set, execute the
                //    rules for distinguishing if a resource is text or binary
                //    and abort these steps."
                distinguish_text_or_binary(resource.header)
            } else {
                // 5. "If the supplied MIME type is an image MIME type
                //    supported by the user agent, let matched-type be the
                //    result of executing the image type pattern matching
                //    algorithm with the resource header ..."
                let image = if crate::mime_type::spec::is_image_mime_type(supplied) && supported {
                    image_type_pattern_matching(resource.header)
                } else {
                    None
                };
                match image {
                    // 6. "If matched-type is not undefined, the computed
                    //    MIME type is matched-type. Abort these steps."
                    Some(t) => t,
                    None => {
                        // 7. the same with the audio or video type pattern
                        //    matching algorithm.
                        let av = if crate::mime_type::spec::is_audio_or_video_mime_type(supplied) && supported {
                            audio_or_video_type_pattern_matching(resource.header)
                        } else {
                            None
                        };
                        match av {
                            // 8. "If matched-type is not undefined, ..."
                            Some(t) => t,
                            // 9. "The computed MIME type is the supplied MIME
                            //    type."
                            None => supplied,
                        }
                    },
                }
            }
        },
        _ => {
            // 2. "If the supplied MIME type is undefined or if the supplied
            //    MIME type's essence is "unknown/unknown",
            //    "application/unknown", or "*/*", execute the rules for
            //    identifying an unknown MIME type with the sniff-scriptable
            //    flag equal to the inverse of the no-sniff flag and abort
            //    these steps."
            identify_unknown_mime_type(resource.header, !resource.no_sniff)
        },
    }
}

// ===========================================================================
// The standard's tables, generated from the pinned `mimesniff.bs` (see the
// header). Each row's comment is its Note, then its four cells.
// ===========================================================================

/// The table in §6.1, one [`Row`] per row, in order.
pub open spec fn image_type_table() -> Seq<Row> {
    seq![
        // A Windows Icon signature.
        // 00 00 01 00 / FF FF FF FF / None. / image/x-icon
        Row {
            pattern: seq![0x00u8, 0x00, 0x01, 0x00],
            mask: seq![0xFFu8, 0xFF, 0xFF, 0xFF],
            ignored: Ignored::None,
            computed: mime_type(seq![0x69u32, 0x6D, 0x61, 0x67, 0x65], seq![0x78u32, 0x2D, 0x69, 0x63, 0x6F, 0x6E]),
        },
        // A Windows Cursor signature.
        // 00 00 02 00 / FF FF FF FF / None. / image/x-icon
        Row {
            pattern: seq![0x00u8, 0x00, 0x02, 0x00],
            mask: seq![0xFFu8, 0xFF, 0xFF, 0xFF],
            ignored: Ignored::None,
            computed: mime_type(seq![0x69u32, 0x6D, 0x61, 0x67, 0x65], seq![0x78u32, 0x2D, 0x69, 0x63, 0x6F, 0x6E]),
        },
        // The string "BM", a BMP signature.
        // 42 4D / FF FF / None. / image/bmp
        Row {
            pattern: seq![0x42u8, 0x4D],
            mask: seq![0xFFu8, 0xFF],
            ignored: Ignored::None,
            computed: mime_type(seq![0x69u32, 0x6D, 0x61, 0x67, 0x65], seq![0x62u32, 0x6D, 0x70]),
        },
        // The string "GIF87a", a GIF signature.
        // 47 49 46 38 37 61 / FF FF FF FF FF FF / None. / image/gif
        Row {
            pattern: seq![0x47u8, 0x49, 0x46, 0x38, 0x37, 0x61],
            mask: seq![0xFFu8, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF],
            ignored: Ignored::None,
            computed: mime_type(seq![0x69u32, 0x6D, 0x61, 0x67, 0x65], seq![0x67u32, 0x69, 0x66]),
        },
        // The string "GIF89a", a GIF signature.
        // 47 49 46 38 39 61 / FF FF FF FF FF FF / None. / image/gif
        Row {
            pattern: seq![0x47u8, 0x49, 0x46, 0x38, 0x39, 0x61],
            mask: seq![0xFFu8, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF],
            ignored: Ignored::None,
            computed: mime_type(seq![0x69u32, 0x6D, 0x61, 0x67, 0x65], seq![0x67u32, 0x69, 0x66]),
        },
        // The string "RIFF" followed by four bytes followed by the string "WEBPVP".
        // 52 49 46 46 00 00 00 00 57 45 42 50 56 50 / FF FF FF FF 00 00 00 00 FF FF FF FF FF FF / None. / image/webp
        Row {
            pattern: seq![0x52u8, 0x49, 0x46, 0x46, 0x00, 0x00, 0x00, 0x00, 0x57, 0x45, 0x42, 0x50, 0x56, 0x50],
            mask: seq![0xFFu8, 0xFF, 0xFF, 0xFF, 0x00, 0x00, 0x00, 0x00, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF],
            ignored: Ignored::None,
            computed: mime_type(seq![0x69u32, 0x6D, 0x61, 0x67, 0x65], seq![0x77u32, 0x65, 0x62, 0x70]),
        },
        // An error-checking byte followed by the string "PNG" followed by CR LF SUB LF, the PNG signature.
        // 89 50 4E 47 0D 0A 1A 0A / FF FF FF FF FF FF FF FF / None. / image/png
        Row {
            pattern: seq![0x89u8, 0x50, 0x4E, 0x47, 0x0D, 0x0A, 0x1A, 0x0A],
            mask: seq![0xFFu8, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF],
            ignored: Ignored::None,
            computed: mime_type(seq![0x69u32, 0x6D, 0x61, 0x67, 0x65], seq![0x70u32, 0x6E, 0x67]),
        },
        // The JPEG Start of Image marker followed by the indicator byte of another marker.
        // FF D8 FF / FF FF FF / None. / image/jpeg
        Row {
            pattern: seq![0xFFu8, 0xD8, 0xFF],
            mask: seq![0xFFu8, 0xFF, 0xFF],
            ignored: Ignored::None,
            computed: mime_type(seq![0x69u32, 0x6D, 0x61, 0x67, 0x65], seq![0x6Au32, 0x70, 0x65, 0x67]),
        },
    ]
}

/// The table in §6.2, one [`Row`] per row, in order.
pub open spec fn audio_or_video_type_table() -> Seq<Row> {
    seq![
        // The string "FORM" followed by four bytes followed by the string "AIFF", the AIFF signature.
        // 46 4F 52 4D 00 00 00 00 41 49 46 46 / FF FF FF FF 00 00 00 00 FF FF FF FF / None. / audio/aiff
        Row {
            pattern: seq![0x46u8, 0x4F, 0x52, 0x4D, 0x00, 0x00, 0x00, 0x00, 0x41, 0x49, 0x46, 0x46],
            mask: seq![0xFFu8, 0xFF, 0xFF, 0xFF, 0x00, 0x00, 0x00, 0x00, 0xFF, 0xFF, 0xFF, 0xFF],
            ignored: Ignored::None,
            computed: mime_type(seq![0x61u32, 0x75, 0x64, 0x69, 0x6F], seq![0x61u32, 0x69, 0x66, 0x66]),
        },
        // The string "ID3", the ID3v2-tagged MP3 signature.
        // 49 44 33 / FF FF FF / None. / audio/mpeg
        Row {
            pattern: seq![0x49u8, 0x44, 0x33],
            mask: seq![0xFFu8, 0xFF, 0xFF],
            ignored: Ignored::None,
            computed: mime_type(seq![0x61u32, 0x75, 0x64, 0x69, 0x6F], seq![0x6Du32, 0x70, 0x65, 0x67]),
        },
        // The string "OggS" followed by NUL, the Ogg container signature.
        // 4F 67 67 53 00 / FF FF FF FF FF / None. / application/ogg
        Row {
            pattern: seq![0x4Fu8, 0x67, 0x67, 0x53, 0x00],
            mask: seq![0xFFu8, 0xFF, 0xFF, 0xFF, 0xFF],
            ignored: Ignored::None,
            computed: mime_type(seq![0x61u32, 0x70, 0x70, 0x6C, 0x69, 0x63, 0x61, 0x74, 0x69, 0x6F, 0x6E], seq![0x6Fu32, 0x67, 0x67]),
        },
        // The string "MThd" followed by four bytes representing the number 6 in 32 bits (big-endian), the MIDI signature.
        // 4D 54 68 64 00 00 00 06 / FF FF FF FF FF FF FF FF / None. / audio/midi
        Row {
            pattern: seq![0x4Du8, 0x54, 0x68, 0x64, 0x00, 0x00, 0x00, 0x06],
            mask: seq![0xFFu8, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF],
            ignored: Ignored::None,
            computed: mime_type(seq![0x61u32, 0x75, 0x64, 0x69, 0x6F], seq![0x6Du32, 0x69, 0x64, 0x69]),
        },
        // The string "RIFF" followed by four bytes followed by the string "AVI ", the AVI signature.
        // 52 49 46 46 00 00 00 00 41 56 49 20 / FF FF FF FF 00 00 00 00 FF FF FF FF / None. / video/avi
        Row {
            pattern: seq![0x52u8, 0x49, 0x46, 0x46, 0x00, 0x00, 0x00, 0x00, 0x41, 0x56, 0x49, 0x20],
            mask: seq![0xFFu8, 0xFF, 0xFF, 0xFF, 0x00, 0x00, 0x00, 0x00, 0xFF, 0xFF, 0xFF, 0xFF],
            ignored: Ignored::None,
            computed: mime_type(seq![0x76u32, 0x69, 0x64, 0x65, 0x6F], seq![0x61u32, 0x76, 0x69]),
        },
        // The string "RIFF" followed by four bytes followed by the string "WAVE", the WAVE signature.
        // 52 49 46 46 00 00 00 00 57 41 56 45 / FF FF FF FF 00 00 00 00 FF FF FF FF / None. / audio/wave
        Row {
            pattern: seq![0x52u8, 0x49, 0x46, 0x46, 0x00, 0x00, 0x00, 0x00, 0x57, 0x41, 0x56, 0x45],
            mask: seq![0xFFu8, 0xFF, 0xFF, 0xFF, 0x00, 0x00, 0x00, 0x00, 0xFF, 0xFF, 0xFF, 0xFF],
            ignored: Ignored::None,
            computed: mime_type(seq![0x61u32, 0x75, 0x64, 0x69, 0x6F], seq![0x77u32, 0x61, 0x76, 0x65]),
        },
    ]
}

/// The table in §6.3, one [`Row`] per row, in order.
pub open spec fn font_type_table() -> Seq<Row> {
    seq![
        // 34 bytes followed by the string "LP", the Embedded OpenType signature.
        // 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 4C 50 / 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 FF FF / None. / application/vnd.ms-fontobject
        Row {
            pattern: seq![0x00u8, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x4C, 0x50],
            mask: seq![0x00u8, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xFF, 0xFF],
            ignored: Ignored::None,
            computed: mime_type(seq![0x61u32, 0x70, 0x70, 0x6C, 0x69, 0x63, 0x61, 0x74, 0x69, 0x6F, 0x6E], seq![0x76u32, 0x6E, 0x64, 0x2E, 0x6D, 0x73, 0x2D, 0x66, 0x6F, 0x6E, 0x74, 0x6F, 0x62, 0x6A, 0x65, 0x63, 0x74]),
        },
        // 4 bytes representing the version number 1.0, a TrueType signature.
        // 00 01 00 00 / FF FF FF FF / None. / font/ttf
        Row {
            pattern: seq![0x00u8, 0x01, 0x00, 0x00],
            mask: seq![0xFFu8, 0xFF, 0xFF, 0xFF],
            ignored: Ignored::None,
            computed: mime_type(seq![0x66u32, 0x6F, 0x6E, 0x74], seq![0x74u32, 0x74, 0x66]),
        },
        // The string "OTTO", the OpenType signature.
        // 4F 54 54 4F / FF FF FF FF / None. / font/otf
        Row {
            pattern: seq![0x4Fu8, 0x54, 0x54, 0x4F],
            mask: seq![0xFFu8, 0xFF, 0xFF, 0xFF],
            ignored: Ignored::None,
            computed: mime_type(seq![0x66u32, 0x6F, 0x6E, 0x74], seq![0x6Fu32, 0x74, 0x66]),
        },
        // The string "ttcf", the TrueType Collection signature.
        // 74 74 63 66 / FF FF FF FF / None. / font/collection
        Row {
            pattern: seq![0x74u8, 0x74, 0x63, 0x66],
            mask: seq![0xFFu8, 0xFF, 0xFF, 0xFF],
            ignored: Ignored::None,
            computed: mime_type(seq![0x66u32, 0x6F, 0x6E, 0x74], seq![0x63u32, 0x6F, 0x6C, 0x6C, 0x65, 0x63, 0x74, 0x69, 0x6F, 0x6E]),
        },
        // The string "wOFF", the Web Open Font Format 1.0 signature.
        // 77 4F 46 46 / FF FF FF FF / None. / font/woff
        Row {
            pattern: seq![0x77u8, 0x4F, 0x46, 0x46],
            mask: seq![0xFFu8, 0xFF, 0xFF, 0xFF],
            ignored: Ignored::None,
            computed: mime_type(seq![0x66u32, 0x6F, 0x6E, 0x74], seq![0x77u32, 0x6F, 0x66, 0x66]),
        },
        // The string "wOF2", the Web Open Font Format 2.0 signature.
        // 77 4F 46 32 / FF FF FF FF / None. / font/woff2
        Row {
            pattern: seq![0x77u8, 0x4F, 0x46, 0x32],
            mask: seq![0xFFu8, 0xFF, 0xFF, 0xFF],
            ignored: Ignored::None,
            computed: mime_type(seq![0x66u32, 0x6F, 0x6E, 0x74], seq![0x77u32, 0x6F, 0x66, 0x66, 0x32]),
        },
    ]
}

/// The table in §6.4, one [`Row`] per row, in order.
pub open spec fn archive_type_table() -> Seq<Row> {
    seq![
        // The GZIP archive signature.
        // 1F 8B 08 / FF FF FF / None. / application/x-gzip
        Row {
            pattern: seq![0x1Fu8, 0x8B, 0x08],
            mask: seq![0xFFu8, 0xFF, 0xFF],
            ignored: Ignored::None,
            computed: mime_type(seq![0x61u32, 0x70, 0x70, 0x6C, 0x69, 0x63, 0x61, 0x74, 0x69, 0x6F, 0x6E], seq![0x78u32, 0x2D, 0x67, 0x7A, 0x69, 0x70]),
        },
        // The string "PK" followed by ETX EOT, the ZIP archive signature.
        // 50 4B 03 04 / FF FF FF FF / None. / application/zip
        Row {
            pattern: seq![0x50u8, 0x4B, 0x03, 0x04],
            mask: seq![0xFFu8, 0xFF, 0xFF, 0xFF],
            ignored: Ignored::None,
            computed: mime_type(seq![0x61u32, 0x70, 0x70, 0x6C, 0x69, 0x63, 0x61, 0x74, 0x69, 0x6F, 0x6E], seq![0x7Au32, 0x69, 0x70]),
        },
        // The string "Rar!" followed by SUB BEL NUL, the RAR 4.x archive signature.
        // 52 61 72 21 1A 07 00 / FF FF FF FF FF FF FF / None. / application/x-rar-compressed
        Row {
            pattern: seq![0x52u8, 0x61, 0x72, 0x21, 0x1A, 0x07, 0x00],
            mask: seq![0xFFu8, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF],
            ignored: Ignored::None,
            computed: mime_type(seq![0x61u32, 0x70, 0x70, 0x6C, 0x69, 0x63, 0x61, 0x74, 0x69, 0x6F, 0x6E], seq![0x78u32, 0x2D, 0x72, 0x61, 0x72, 0x2D, 0x63, 0x6F, 0x6D, 0x70, 0x72, 0x65, 0x73, 0x73, 0x65, 0x64]),
        },
    ]
}

/// The table in §7.1 step 1 (sniff-scriptable), one [`Row`] per row, in order.
pub open spec fn unknown_scriptable_table() -> Seq<Row> {
    seq![
        // The case-insensitive string "<!DOCTYPE HTML" followed by a tag-terminating byte. (TT = 0x20)
        // 3C 21 44 4F 43 54 59 50 45 20 48 54 4D 4C TT / FF FF DF DF DF DF DF DF DF FF DF DF DF DF FF / Whitespace bytes. / text/html
        Row {
            pattern: seq![0x3Cu8, 0x21, 0x44, 0x4F, 0x43, 0x54, 0x59, 0x50, 0x45, 0x20, 0x48, 0x54, 0x4D, 0x4C, 0x20],
            mask: seq![0xFFu8, 0xFF, 0xDF, 0xDF, 0xDF, 0xDF, 0xDF, 0xDF, 0xDF, 0xFF, 0xDF, 0xDF, 0xDF, 0xDF, 0xFF],
            ignored: Ignored::WhitespaceBytes,
            computed: mime_type(seq![0x74u32, 0x65, 0x78, 0x74], seq![0x68u32, 0x74, 0x6D, 0x6C]),
        },
        // The case-insensitive string "<!DOCTYPE HTML" followed by a tag-terminating byte. (TT = 0x3E)
        // 3C 21 44 4F 43 54 59 50 45 20 48 54 4D 4C TT / FF FF DF DF DF DF DF DF DF FF DF DF DF DF FF / Whitespace bytes. / text/html
        Row {
            pattern: seq![0x3Cu8, 0x21, 0x44, 0x4F, 0x43, 0x54, 0x59, 0x50, 0x45, 0x20, 0x48, 0x54, 0x4D, 0x4C, 0x3E],
            mask: seq![0xFFu8, 0xFF, 0xDF, 0xDF, 0xDF, 0xDF, 0xDF, 0xDF, 0xDF, 0xFF, 0xDF, 0xDF, 0xDF, 0xDF, 0xFF],
            ignored: Ignored::WhitespaceBytes,
            computed: mime_type(seq![0x74u32, 0x65, 0x78, 0x74], seq![0x68u32, 0x74, 0x6D, 0x6C]),
        },
        // The case-insensitive string "<HTML" followed by a tag-terminating byte. (TT = 0x20)
        // 3C 48 54 4D 4C TT / FF DF DF DF DF FF / Whitespace bytes. / text/html
        Row {
            pattern: seq![0x3Cu8, 0x48, 0x54, 0x4D, 0x4C, 0x20],
            mask: seq![0xFFu8, 0xDF, 0xDF, 0xDF, 0xDF, 0xFF],
            ignored: Ignored::WhitespaceBytes,
            computed: mime_type(seq![0x74u32, 0x65, 0x78, 0x74], seq![0x68u32, 0x74, 0x6D, 0x6C]),
        },
        // The case-insensitive string "<HTML" followed by a tag-terminating byte. (TT = 0x3E)
        // 3C 48 54 4D 4C TT / FF DF DF DF DF FF / Whitespace bytes. / text/html
        Row {
            pattern: seq![0x3Cu8, 0x48, 0x54, 0x4D, 0x4C, 0x3E],
            mask: seq![0xFFu8, 0xDF, 0xDF, 0xDF, 0xDF, 0xFF],
            ignored: Ignored::WhitespaceBytes,
            computed: mime_type(seq![0x74u32, 0x65, 0x78, 0x74], seq![0x68u32, 0x74, 0x6D, 0x6C]),
        },
        // The case-insensitive string "<HEAD" followed by a tag-terminating byte. (TT = 0x20)
        // 3C 48 45 41 44 TT / FF DF DF DF DF FF / Whitespace bytes. / text/html
        Row {
            pattern: seq![0x3Cu8, 0x48, 0x45, 0x41, 0x44, 0x20],
            mask: seq![0xFFu8, 0xDF, 0xDF, 0xDF, 0xDF, 0xFF],
            ignored: Ignored::WhitespaceBytes,
            computed: mime_type(seq![0x74u32, 0x65, 0x78, 0x74], seq![0x68u32, 0x74, 0x6D, 0x6C]),
        },
        // The case-insensitive string "<HEAD" followed by a tag-terminating byte. (TT = 0x3E)
        // 3C 48 45 41 44 TT / FF DF DF DF DF FF / Whitespace bytes. / text/html
        Row {
            pattern: seq![0x3Cu8, 0x48, 0x45, 0x41, 0x44, 0x3E],
            mask: seq![0xFFu8, 0xDF, 0xDF, 0xDF, 0xDF, 0xFF],
            ignored: Ignored::WhitespaceBytes,
            computed: mime_type(seq![0x74u32, 0x65, 0x78, 0x74], seq![0x68u32, 0x74, 0x6D, 0x6C]),
        },
        // The case-insensitive string "<SCRIPT" followed by a tag-terminating byte. (TT = 0x20)
        // 3C 53 43 52 49 50 54 TT / FF DF DF DF DF DF DF FF / Whitespace bytes. / text/html
        Row {
            pattern: seq![0x3Cu8, 0x53, 0x43, 0x52, 0x49, 0x50, 0x54, 0x20],
            mask: seq![0xFFu8, 0xDF, 0xDF, 0xDF, 0xDF, 0xDF, 0xDF, 0xFF],
            ignored: Ignored::WhitespaceBytes,
            computed: mime_type(seq![0x74u32, 0x65, 0x78, 0x74], seq![0x68u32, 0x74, 0x6D, 0x6C]),
        },
        // The case-insensitive string "<SCRIPT" followed by a tag-terminating byte. (TT = 0x3E)
        // 3C 53 43 52 49 50 54 TT / FF DF DF DF DF DF DF FF / Whitespace bytes. / text/html
        Row {
            pattern: seq![0x3Cu8, 0x53, 0x43, 0x52, 0x49, 0x50, 0x54, 0x3E],
            mask: seq![0xFFu8, 0xDF, 0xDF, 0xDF, 0xDF, 0xDF, 0xDF, 0xFF],
            ignored: Ignored::WhitespaceBytes,
            computed: mime_type(seq![0x74u32, 0x65, 0x78, 0x74], seq![0x68u32, 0x74, 0x6D, 0x6C]),
        },
        // The case-insensitive string "<IFRAME" followed by a tag-terminating byte. (TT = 0x20)
        // 3C 49 46 52 41 4D 45 TT / FF DF DF DF DF DF DF FF / Whitespace bytes. / text/html
        Row {
            pattern: seq![0x3Cu8, 0x49, 0x46, 0x52, 0x41, 0x4D, 0x45, 0x20],
            mask: seq![0xFFu8, 0xDF, 0xDF, 0xDF, 0xDF, 0xDF, 0xDF, 0xFF],
            ignored: Ignored::WhitespaceBytes,
            computed: mime_type(seq![0x74u32, 0x65, 0x78, 0x74], seq![0x68u32, 0x74, 0x6D, 0x6C]),
        },
        // The case-insensitive string "<IFRAME" followed by a tag-terminating byte. (TT = 0x3E)
        // 3C 49 46 52 41 4D 45 TT / FF DF DF DF DF DF DF FF / Whitespace bytes. / text/html
        Row {
            pattern: seq![0x3Cu8, 0x49, 0x46, 0x52, 0x41, 0x4D, 0x45, 0x3E],
            mask: seq![0xFFu8, 0xDF, 0xDF, 0xDF, 0xDF, 0xDF, 0xDF, 0xFF],
            ignored: Ignored::WhitespaceBytes,
            computed: mime_type(seq![0x74u32, 0x65, 0x78, 0x74], seq![0x68u32, 0x74, 0x6D, 0x6C]),
        },
        // The case-insensitive string "<H1" followed by a tag-terminating byte. (TT = 0x20)
        // 3C 48 31 TT / FF DF FF FF / Whitespace bytes. / text/html
        Row {
            pattern: seq![0x3Cu8, 0x48, 0x31, 0x20],
            mask: seq![0xFFu8, 0xDF, 0xFF, 0xFF],
            ignored: Ignored::WhitespaceBytes,
            computed: mime_type(seq![0x74u32, 0x65, 0x78, 0x74], seq![0x68u32, 0x74, 0x6D, 0x6C]),
        },
        // The case-insensitive string "<H1" followed by a tag-terminating byte. (TT = 0x3E)
        // 3C 48 31 TT / FF DF FF FF / Whitespace bytes. / text/html
        Row {
            pattern: seq![0x3Cu8, 0x48, 0x31, 0x3E],
            mask: seq![0xFFu8, 0xDF, 0xFF, 0xFF],
            ignored: Ignored::WhitespaceBytes,
            computed: mime_type(seq![0x74u32, 0x65, 0x78, 0x74], seq![0x68u32, 0x74, 0x6D, 0x6C]),
        },
        // The case-insensitive string "<DIV" followed by a tag-terminating byte. (TT = 0x20)
        // 3C 44 49 56 TT / FF DF DF DF FF / Whitespace bytes. / text/html
        Row {
            pattern: seq![0x3Cu8, 0x44, 0x49, 0x56, 0x20],
            mask: seq![0xFFu8, 0xDF, 0xDF, 0xDF, 0xFF],
            ignored: Ignored::WhitespaceBytes,
            computed: mime_type(seq![0x74u32, 0x65, 0x78, 0x74], seq![0x68u32, 0x74, 0x6D, 0x6C]),
        },
        // The case-insensitive string "<DIV" followed by a tag-terminating byte. (TT = 0x3E)
        // 3C 44 49 56 TT / FF DF DF DF FF / Whitespace bytes. / text/html
        Row {
            pattern: seq![0x3Cu8, 0x44, 0x49, 0x56, 0x3E],
            mask: seq![0xFFu8, 0xDF, 0xDF, 0xDF, 0xFF],
            ignored: Ignored::WhitespaceBytes,
            computed: mime_type(seq![0x74u32, 0x65, 0x78, 0x74], seq![0x68u32, 0x74, 0x6D, 0x6C]),
        },
        // The case-insensitive string "<FONT" followed by a tag-terminating byte. (TT = 0x20)
        // 3C 46 4F 4E 54 TT / FF DF DF DF DF FF / Whitespace bytes. / text/html
        Row {
            pattern: seq![0x3Cu8, 0x46, 0x4F, 0x4E, 0x54, 0x20],
            mask: seq![0xFFu8, 0xDF, 0xDF, 0xDF, 0xDF, 0xFF],
            ignored: Ignored::WhitespaceBytes,
            computed: mime_type(seq![0x74u32, 0x65, 0x78, 0x74], seq![0x68u32, 0x74, 0x6D, 0x6C]),
        },
        // The case-insensitive string "<FONT" followed by a tag-terminating byte. (TT = 0x3E)
        // 3C 46 4F 4E 54 TT / FF DF DF DF DF FF / Whitespace bytes. / text/html
        Row {
            pattern: seq![0x3Cu8, 0x46, 0x4F, 0x4E, 0x54, 0x3E],
            mask: seq![0xFFu8, 0xDF, 0xDF, 0xDF, 0xDF, 0xFF],
            ignored: Ignored::WhitespaceBytes,
            computed: mime_type(seq![0x74u32, 0x65, 0x78, 0x74], seq![0x68u32, 0x74, 0x6D, 0x6C]),
        },
        // The case-insensitive string "<TABLE" followed by a tag-terminating byte. (TT = 0x20)
        // 3C 54 41 42 4C 45 TT / FF DF DF DF DF DF FF / Whitespace bytes. / text/html
        Row {
            pattern: seq![0x3Cu8, 0x54, 0x41, 0x42, 0x4C, 0x45, 0x20],
            mask: seq![0xFFu8, 0xDF, 0xDF, 0xDF, 0xDF, 0xDF, 0xFF],
            ignored: Ignored::WhitespaceBytes,
            computed: mime_type(seq![0x74u32, 0x65, 0x78, 0x74], seq![0x68u32, 0x74, 0x6D, 0x6C]),
        },
        // The case-insensitive string "<TABLE" followed by a tag-terminating byte. (TT = 0x3E)
        // 3C 54 41 42 4C 45 TT / FF DF DF DF DF DF FF / Whitespace bytes. / text/html
        Row {
            pattern: seq![0x3Cu8, 0x54, 0x41, 0x42, 0x4C, 0x45, 0x3E],
            mask: seq![0xFFu8, 0xDF, 0xDF, 0xDF, 0xDF, 0xDF, 0xFF],
            ignored: Ignored::WhitespaceBytes,
            computed: mime_type(seq![0x74u32, 0x65, 0x78, 0x74], seq![0x68u32, 0x74, 0x6D, 0x6C]),
        },
        // The case-insensitive string "<A" followed by a tag-terminating byte. (TT = 0x20)
        // 3C 41 TT / FF DF FF / Whitespace bytes. / text/html
        Row {
            pattern: seq![0x3Cu8, 0x41, 0x20],
            mask: seq![0xFFu8, 0xDF, 0xFF],
            ignored: Ignored::WhitespaceBytes,
            computed: mime_type(seq![0x74u32, 0x65, 0x78, 0x74], seq![0x68u32, 0x74, 0x6D, 0x6C]),
        },
        // The case-insensitive string "<A" followed by a tag-terminating byte. (TT = 0x3E)
        // 3C 41 TT / FF DF FF / Whitespace bytes. / text/html
        Row {
            pattern: seq![0x3Cu8, 0x41, 0x3E],
            mask: seq![0xFFu8, 0xDF, 0xFF],
            ignored: Ignored::WhitespaceBytes,
            computed: mime_type(seq![0x74u32, 0x65, 0x78, 0x74], seq![0x68u32, 0x74, 0x6D, 0x6C]),
        },
        // The case-insensitive string "<STYLE" followed by a tag-terminating byte. (TT = 0x20)
        // 3C 53 54 59 4C 45 TT / FF DF DF DF DF DF FF / Whitespace bytes. / text/html
        Row {
            pattern: seq![0x3Cu8, 0x53, 0x54, 0x59, 0x4C, 0x45, 0x20],
            mask: seq![0xFFu8, 0xDF, 0xDF, 0xDF, 0xDF, 0xDF, 0xFF],
            ignored: Ignored::WhitespaceBytes,
            computed: mime_type(seq![0x74u32, 0x65, 0x78, 0x74], seq![0x68u32, 0x74, 0x6D, 0x6C]),
        },
        // The case-insensitive string "<STYLE" followed by a tag-terminating byte. (TT = 0x3E)
        // 3C 53 54 59 4C 45 TT / FF DF DF DF DF DF FF / Whitespace bytes. / text/html
        Row {
            pattern: seq![0x3Cu8, 0x53, 0x54, 0x59, 0x4C, 0x45, 0x3E],
            mask: seq![0xFFu8, 0xDF, 0xDF, 0xDF, 0xDF, 0xDF, 0xFF],
            ignored: Ignored::WhitespaceBytes,
            computed: mime_type(seq![0x74u32, 0x65, 0x78, 0x74], seq![0x68u32, 0x74, 0x6D, 0x6C]),
        },
        // The case-insensitive string "<TITLE" followed by a tag-terminating byte. (TT = 0x20)
        // 3C 54 49 54 4C 45 TT / FF DF DF DF DF DF FF / Whitespace bytes. / text/html
        Row {
            pattern: seq![0x3Cu8, 0x54, 0x49, 0x54, 0x4C, 0x45, 0x20],
            mask: seq![0xFFu8, 0xDF, 0xDF, 0xDF, 0xDF, 0xDF, 0xFF],
            ignored: Ignored::WhitespaceBytes,
            computed: mime_type(seq![0x74u32, 0x65, 0x78, 0x74], seq![0x68u32, 0x74, 0x6D, 0x6C]),
        },
        // The case-insensitive string "<TITLE" followed by a tag-terminating byte. (TT = 0x3E)
        // 3C 54 49 54 4C 45 TT / FF DF DF DF DF DF FF / Whitespace bytes. / text/html
        Row {
            pattern: seq![0x3Cu8, 0x54, 0x49, 0x54, 0x4C, 0x45, 0x3E],
            mask: seq![0xFFu8, 0xDF, 0xDF, 0xDF, 0xDF, 0xDF, 0xFF],
            ignored: Ignored::WhitespaceBytes,
            computed: mime_type(seq![0x74u32, 0x65, 0x78, 0x74], seq![0x68u32, 0x74, 0x6D, 0x6C]),
        },
        // The case-insensitive string "<B" followed by a tag-terminating byte. (TT = 0x20)
        // 3C 42 TT / FF DF FF / Whitespace bytes. / text/html
        Row {
            pattern: seq![0x3Cu8, 0x42, 0x20],
            mask: seq![0xFFu8, 0xDF, 0xFF],
            ignored: Ignored::WhitespaceBytes,
            computed: mime_type(seq![0x74u32, 0x65, 0x78, 0x74], seq![0x68u32, 0x74, 0x6D, 0x6C]),
        },
        // The case-insensitive string "<B" followed by a tag-terminating byte. (TT = 0x3E)
        // 3C 42 TT / FF DF FF / Whitespace bytes. / text/html
        Row {
            pattern: seq![0x3Cu8, 0x42, 0x3E],
            mask: seq![0xFFu8, 0xDF, 0xFF],
            ignored: Ignored::WhitespaceBytes,
            computed: mime_type(seq![0x74u32, 0x65, 0x78, 0x74], seq![0x68u32, 0x74, 0x6D, 0x6C]),
        },
        // The case-insensitive string "<BODY" followed by a tag-terminating byte. (TT = 0x20)
        // 3C 42 4F 44 59 TT / FF DF DF DF DF FF / Whitespace bytes. / text/html
        Row {
            pattern: seq![0x3Cu8, 0x42, 0x4F, 0x44, 0x59, 0x20],
            mask: seq![0xFFu8, 0xDF, 0xDF, 0xDF, 0xDF, 0xFF],
            ignored: Ignored::WhitespaceBytes,
            computed: mime_type(seq![0x74u32, 0x65, 0x78, 0x74], seq![0x68u32, 0x74, 0x6D, 0x6C]),
        },
        // The case-insensitive string "<BODY" followed by a tag-terminating byte. (TT = 0x3E)
        // 3C 42 4F 44 59 TT / FF DF DF DF DF FF / Whitespace bytes. / text/html
        Row {
            pattern: seq![0x3Cu8, 0x42, 0x4F, 0x44, 0x59, 0x3E],
            mask: seq![0xFFu8, 0xDF, 0xDF, 0xDF, 0xDF, 0xFF],
            ignored: Ignored::WhitespaceBytes,
            computed: mime_type(seq![0x74u32, 0x65, 0x78, 0x74], seq![0x68u32, 0x74, 0x6D, 0x6C]),
        },
        // The case-insensitive string "<BR" followed by a tag-terminating byte. (TT = 0x20)
        // 3C 42 52 TT / FF DF DF FF / Whitespace bytes. / text/html
        Row {
            pattern: seq![0x3Cu8, 0x42, 0x52, 0x20],
            mask: seq![0xFFu8, 0xDF, 0xDF, 0xFF],
            ignored: Ignored::WhitespaceBytes,
            computed: mime_type(seq![0x74u32, 0x65, 0x78, 0x74], seq![0x68u32, 0x74, 0x6D, 0x6C]),
        },
        // The case-insensitive string "<BR" followed by a tag-terminating byte. (TT = 0x3E)
        // 3C 42 52 TT / FF DF DF FF / Whitespace bytes. / text/html
        Row {
            pattern: seq![0x3Cu8, 0x42, 0x52, 0x3E],
            mask: seq![0xFFu8, 0xDF, 0xDF, 0xFF],
            ignored: Ignored::WhitespaceBytes,
            computed: mime_type(seq![0x74u32, 0x65, 0x78, 0x74], seq![0x68u32, 0x74, 0x6D, 0x6C]),
        },
        // The case-insensitive string "<P" followed by a tag-terminating byte. (TT = 0x20)
        // 3C 50 TT / FF DF FF / Whitespace bytes. / text/html
        Row {
            pattern: seq![0x3Cu8, 0x50, 0x20],
            mask: seq![0xFFu8, 0xDF, 0xFF],
            ignored: Ignored::WhitespaceBytes,
            computed: mime_type(seq![0x74u32, 0x65, 0x78, 0x74], seq![0x68u32, 0x74, 0x6D, 0x6C]),
        },
        // The case-insensitive string "<P" followed by a tag-terminating byte. (TT = 0x3E)
        // 3C 50 TT / FF DF FF / Whitespace bytes. / text/html
        Row {
            pattern: seq![0x3Cu8, 0x50, 0x3E],
            mask: seq![0xFFu8, 0xDF, 0xFF],
            ignored: Ignored::WhitespaceBytes,
            computed: mime_type(seq![0x74u32, 0x65, 0x78, 0x74], seq![0x68u32, 0x74, 0x6D, 0x6C]),
        },
        // The string "<!--" followed by a tag-terminating byte. (TT = 0x20)
        // 3C 21 2D 2D TT / FF FF FF FF FF / Whitespace bytes. / text/html
        Row {
            pattern: seq![0x3Cu8, 0x21, 0x2D, 0x2D, 0x20],
            mask: seq![0xFFu8, 0xFF, 0xFF, 0xFF, 0xFF],
            ignored: Ignored::WhitespaceBytes,
            computed: mime_type(seq![0x74u32, 0x65, 0x78, 0x74], seq![0x68u32, 0x74, 0x6D, 0x6C]),
        },
        // The string "<!--" followed by a tag-terminating byte. (TT = 0x3E)
        // 3C 21 2D 2D TT / FF FF FF FF FF / Whitespace bytes. / text/html
        Row {
            pattern: seq![0x3Cu8, 0x21, 0x2D, 0x2D, 0x3E],
            mask: seq![0xFFu8, 0xFF, 0xFF, 0xFF, 0xFF],
            ignored: Ignored::WhitespaceBytes,
            computed: mime_type(seq![0x74u32, 0x65, 0x78, 0x74], seq![0x68u32, 0x74, 0x6D, 0x6C]),
        },
        // The string "<?xml".
        // 3C 3F 78 6D 6C / FF FF FF FF FF / Whitespace bytes. / text/xml
        Row {
            pattern: seq![0x3Cu8, 0x3F, 0x78, 0x6D, 0x6C],
            mask: seq![0xFFu8, 0xFF, 0xFF, 0xFF, 0xFF],
            ignored: Ignored::WhitespaceBytes,
            computed: mime_type(seq![0x74u32, 0x65, 0x78, 0x74], seq![0x78u32, 0x6D, 0x6C]),
        },
        // The string "%PDF-", the PDF signature.
        // 25 50 44 46 2D / FF FF FF FF FF / None. / application/pdf
        Row {
            pattern: seq![0x25u8, 0x50, 0x44, 0x46, 0x2D],
            mask: seq![0xFFu8, 0xFF, 0xFF, 0xFF, 0xFF],
            ignored: Ignored::None,
            computed: mime_type(seq![0x61u32, 0x70, 0x70, 0x6C, 0x69, 0x63, 0x61, 0x74, 0x69, 0x6F, 0x6E], seq![0x70u32, 0x64, 0x66]),
        },
    ]
}

/// The table in §7.1 step 2, one [`Row`] per row, in order.
pub open spec fn unknown_non_scriptable_table() -> Seq<Row> {
    seq![
        // The string "%!PS-Adobe-", the PostScript signature.
        // 25 21 50 53 2D 41 64 6F 62 65 2D / FF FF FF FF FF FF FF FF FF FF FF / None. / application/postscript
        Row {
            pattern: seq![0x25u8, 0x21, 0x50, 0x53, 0x2D, 0x41, 0x64, 0x6F, 0x62, 0x65, 0x2D],
            mask: seq![0xFFu8, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF],
            ignored: Ignored::None,
            computed: mime_type(seq![0x61u32, 0x70, 0x70, 0x6C, 0x69, 0x63, 0x61, 0x74, 0x69, 0x6F, 0x6E], seq![0x70u32, 0x6F, 0x73, 0x74, 0x73, 0x63, 0x72, 0x69, 0x70, 0x74]),
        },
        // UTF-16BE BOM
        // FE FF 00 00 / FF FF 00 00 / None. / text/plain
        Row {
            pattern: seq![0xFEu8, 0xFF, 0x00, 0x00],
            mask: seq![0xFFu8, 0xFF, 0x00, 0x00],
            ignored: Ignored::None,
            computed: mime_type(seq![0x74u32, 0x65, 0x78, 0x74], seq![0x70u32, 0x6C, 0x61, 0x69, 0x6E]),
        },
        // UTF-16LE BOM
        // FF FE 00 00 / FF FF 00 00 / None. / text/plain
        Row {
            pattern: seq![0xFFu8, 0xFE, 0x00, 0x00],
            mask: seq![0xFFu8, 0xFF, 0x00, 0x00],
            ignored: Ignored::None,
            computed: mime_type(seq![0x74u32, 0x65, 0x78, 0x74], seq![0x70u32, 0x6C, 0x61, 0x69, 0x6E]),
        },
        // UTF-8 BOM
        // EF BB BF 00 / FF FF FF 00 / None. / text/plain
        Row {
            pattern: seq![0xEFu8, 0xBB, 0xBF, 0x00],
            mask: seq![0xFFu8, 0xFF, 0xFF, 0x00],
            ignored: Ignored::None,
            computed: mime_type(seq![0x74u32, 0x65, 0x78, 0x74], seq![0x70u32, 0x6C, 0x61, 0x69, 0x6E]),
        },
    ]
}

/// The check-for-apache-bug table in §5.1 ("Bytes in Hexadecimal"), in order.
pub open spec fn apache_bug_values() -> Seq<Seq<u8>> {
    seq![
        // text/plain
        seq![0x74u8, 0x65, 0x78, 0x74, 0x2F, 0x70, 0x6C, 0x61, 0x69, 0x6E],
        // text/plain; charset=ISO-8859-1
        seq![0x74u8, 0x65, 0x78, 0x74, 0x2F, 0x70, 0x6C, 0x61, 0x69, 0x6E, 0x3B, 0x20, 0x63, 0x68, 0x61, 0x72, 0x73, 0x65, 0x74, 0x3D, 0x49, 0x53, 0x4F, 0x2D, 0x38, 0x38, 0x35, 0x39, 0x2D, 0x31],
        // text/plain; charset=iso-8859-1
        seq![0x74u8, 0x65, 0x78, 0x74, 0x2F, 0x70, 0x6C, 0x61, 0x69, 0x6E, 0x3B, 0x20, 0x63, 0x68, 0x61, 0x72, 0x73, 0x65, 0x74, 0x3D, 0x69, 0x73, 0x6F, 0x2D, 0x38, 0x38, 0x35, 0x39, 0x2D, 0x31],
        // text/plain; charset=UTF-8
        seq![0x74u8, 0x65, 0x78, 0x74, 0x2F, 0x70, 0x6C, 0x61, 0x69, 0x6E, 0x3B, 0x20, 0x63, 0x68, 0x61, 0x72, 0x73, 0x65, 0x74, 0x3D, 0x55, 0x54, 0x46, 0x2D, 0x38],
    ]
}

/// The mp3-rates table in §6.2.3, by index (index 15 and up: not in the table).
pub open spec fn mp3_rates() -> Seq<nat> {
    seq![0, 32000, 40000, 48000, 56000, 64000, 80000, 96000, 112000, 128000, 160000, 192000, 224000, 256000, 320000]
}

/// The mp2.5-rates table in §6.2.3, by index (index 15 and up: not in the table).
pub open spec fn mp2_5_rates() -> Seq<nat> {
    seq![0, 8000, 16000, 24000, 32000, 40000, 48000, 56000, 64000, 80000, 96000, 112000, 128000, 144000, 160000]
}

/// The samplerate table in §6.2.3, by index (index 3 and up: not in the table).
pub open spec fn sample_rates() -> Seq<nat> {
    seq![44100, 48000, 32000]
}


} // verus!
