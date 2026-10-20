//! The MP4, WebM and MP3-without-ID3 signatures (MIME Sniffing §6.2.1–
//! §6.2.3), each proven equal to its spec definition, and the audio or
//! video type pattern matching algorithm (§6.2) that uses them, proven
//! against [`super::contract`].

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;
use super::pattern::mime_literal;
use crate::mime_type::record::MimeType;

verus! {

/// `sequence[i]`.
fn byte_at(sequence: &[u8], i: usize) -> (r: u8)
    requires
        i < sequence.len(),
    ensures
        r == sequence@[i as int],
{
    match sequence.get(i) {
        Some(b) => *b,
        None => 0,
    }
}

// ===========================================================================
// §6.2.1 Signature for MP4.
// ===========================================================================

/// Four bytes as a 32-bit unsigned big-endian integer.
fn big_endian_u32(b0: u8, b1: u8, b2: u8, b3: u8) -> (r: u32)
    ensures
        r as nat == b0 as nat * 0x100_0000 + b1 as nat * 0x1_0000 + b2 as nat * 0x100 + b3 as nat,
{
    let (x0, x1, x2, x3) = (b0 as u32, b1 as u32, b2 as u32, b3 as u32);
    assert((x0 << 24u32) | (x1 << 16u32) | (x2 << 8u32) | x3 == x0 * 0x100_0000 + x1 * 0x1_0000 + x2 * 0x100 + x3)
        by (bit_vector)
        requires
            x0 < 0x100 && x1 < 0x100 && x2 < 0x100 && x3 < 0x100,
    ;
    (x0 << 24u32) | (x1 << 16u32) | (x2 << 8u32) | x3
}

/// The three bytes from `sequence[i]` are 0x6D 0x70 0x34 ("mp4").
fn is_mp4_at_exec(sequence: &[u8], i: usize) -> (r: bool)
    requires
        i + 2 < sequence.len(),
    ensures
        r == is_mp4_at(sequence@, i as int),
{
    // Never saturates: i + 2 < sequence.len().
    byte_at(sequence, i) == 0x6D && byte_at(sequence, i.saturating_add(1)) == 0x70
        && byte_at(sequence, i.saturating_add(2)) == 0x34
}

/// Matches the signature for MP4 (§6.2.1, #signature-for-mp4).
pub fn matches_mp4_exec(sequence: &[u8]) -> (r: bool)
    ensures
        r == matches_mp4(sequence@),
{
    // 2. "Let length be the number of bytes in sequence."
    let length = sequence.len();
    // 3. "If length is less than 12, return false."
    if length < 12 {
        return false;
    }
    // 4. "Let box-size be the four bytes from sequence[0] to sequence[3],
    //    interpreted as a 32-bit unsigned big-endian integer."
    let box_size = big_endian_u32(byte_at(sequence, 0), byte_at(sequence, 1), byte_at(sequence, 2), byte_at(sequence, 3));
    let box_size = box_size as usize;
    // 5. "If length is less than box-size or if box-size modulo 4 is not
    //    equal to 0, return false."
    if length < box_size || box_size.checked_rem(4) != Some(0) {
        return false;
    }
    // 6. "If the four bytes from sequence[4] to sequence[7] are not equal
    //    to 0x66 0x74 0x79 0x70 ("ftyp"), return false."
    if !(byte_at(sequence, 4) == 0x66 && byte_at(sequence, 5) == 0x74 && byte_at(sequence, 6) == 0x79
        && byte_at(sequence, 7) == 0x70) {
        return false;
    }
    // 7. "If the three bytes from sequence[8] to sequence[10] are equal to
    //    0x6D 0x70 0x34 ("mp4"), return true."
    if is_mp4_at_exec(sequence, 8) {
        return true;
    }
    // 8. "Let bytes-read be 16."
    let mut bytes_read: usize = 16;
    assert(matches_mp4(sequence@) == mp4_loop(sequence@, box_size as nat, 16));
    // 9. "While bytes-read is less than box-size, continuously loop through
    //    these steps:"
    while bytes_read < box_size
        invariant
            box_size <= length == sequence.len(),
            box_size % 4 == 0,
            bytes_read % 4 == 0,
            matches_mp4(sequence@) == mp4_loop(sequence@, box_size as nat, bytes_read as nat),
        decreases box_size - bytes_read,
    {
        assert(bytes_read + 4 <= box_size);
        // 9.1 "If the three bytes from sequence[bytes-read] to
        //     sequence[bytes-read + 2] are equal to 0x6D 0x70 0x34 ("mp4"),
        //     return true."
        if is_mp4_at_exec(sequence, bytes_read) {
            assert(is_mp4_at(sequence@, (bytes_read as nat) as int));
            assert(mp4_loop(sequence@, box_size as nat, bytes_read as nat));
            return true;
        }
        // 9.2 "Increment bytes-read by 4." Never saturates: bytes_read + 4
        //     <= box_size.
        bytes_read = bytes_read.saturating_add(4);
    }
    // 10. "Return false."
    false
}

// ===========================================================================
// §6.2.2 Signature for WebM.
// ===========================================================================

/// Parse a vint (§6.2.2) on `sequence` starting at index `iter`: the
/// number size (steps 1–5; the parsed number is never used).
fn vint_number_size(sequence: &[u8], iter: usize) -> (r: usize)
    requires
        iter < sequence.len(),
    ensures
        r == parse_a_vint(sequence@, iter as nat).1,
        1 <= r <= 8,
{
    let length = sequence.len();
    let byte = byte_at(sequence, iter);
    // 1. "Let mask be 128." 3. "Let number size be 1."
    let mut mask: u8 = 128;
    let mut number_size: usize = 1;
    // 5. "While number size is less than max vint length, and less than
    //    length, continuously loop through these steps:" 5.1 "If the
    //    sequence[index] & mask is not zero, abort these steps."
    while number_size < 8 && number_size < length && byte & mask == 0
        invariant
            1 <= number_size <= 8,
            length == sequence.len(),
            vint_size_loop(byte, length as nat, 128, 1) == vint_size_loop(byte, length as nat, mask, number_size as nat),
        decreases 8 - number_size,
    {
        // 5.2 "Let mask be the value of mask >> 1."
        mask >>= 1u8;
        // 5.3 "Increment number size by one." Never saturates: < 8.
        number_size = number_size.saturating_add(1);
    }
    number_size
}

/// Matching a padded sequence "webm" on `sequence` at `offset` (§6.2.2).
fn matches_padded_webm(sequence: &[u8], offset: usize) -> (r: bool)
    requires
        offset <= sequence.len(),
    ensures
        r == matches_padded_sequence(seq![0x77u8, 0x65, 0x62, 0x6D], sequence@, offset as nat),
{
    let mut start = offset;
    while start < sequence.len() && byte_at(sequence, start) == 0x00
        invariant
            offset <= start <= sequence.len(),
            skip_zero_bytes(sequence@, offset as nat) == skip_zero_bytes(sequence@, start as nat),
        decreases sequence.len() - start,
    {
        // Never saturates: start < sequence.len().
        start = start.saturating_add(1);
    }
    assert(skip_zero_bytes(sequence@, start as nat) == start);
    if sequence.len().saturating_sub(start) < 4 {
        return false;
    }
    // Never saturates: start + 3 < sequence.len().
    let r = byte_at(sequence, start) == 0x77 && byte_at(sequence, start.saturating_add(1)) == 0x65
        && byte_at(sequence, start.saturating_add(2)) == 0x62 && byte_at(sequence, start.saturating_add(3)) == 0x6D;
    assert(r == (sequence@.subrange(start as int, start + 4) =~= seq![0x77u8, 0x65, 0x62, 0x6D]));
    r
}

/// Matches the signature for WebM (§6.2.2, #signature-for-webm).
pub fn matches_webm_exec(sequence: &[u8]) -> (r: bool)
    ensures
        r == matches_webm(sequence@),
{
    // 2. "Let length be the number of bytes in sequence."
    let length = sequence.len();
    // 3. "If length is less than 4, return false."
    if length < 4 {
        return false;
    }
    // 4. "If the four bytes from sequence[0] to sequence[3], are not equal
    //    to 0x1A 0x45 0xDF 0xA3, return false."
    if !(byte_at(sequence, 0) == 0x1A && byte_at(sequence, 1) == 0x45 && byte_at(sequence, 2) == 0xDF
        && byte_at(sequence, 3) == 0xA3) {
        return false;
    }
    // 5. "Let iter be 4."
    let mut iter: usize = 4;
    assert(matches_webm(sequence@) == webm_loop(sequence@, 4));
    // 6. "While iter is less than length and iter is less than 38,
    //    continuously loop through these steps:"
    while iter < length && iter < 38
        invariant
            iter <= 48,
            length == sequence.len(),
            matches_webm(sequence@) == webm_loop(sequence@, iter as nat),
        decreases 48 - iter,
    {
        // 6.1 "If the two bytes from sequence[iter] to sequence[iter + 1]
        //     are equal to 0x42 0x82," (Erratum: only when both exist.)
        // Never saturates: iter < 38.
        let next = iter.saturating_add(1);
        if next < length && byte_at(sequence, iter) == 0x42 && byte_at(sequence, next) == 0x82 {
            // 6.1.1 "Increment iter by 2."
            let at = iter.saturating_add(2);
            // 6.1.2 "If iter is greater or equal than length, abort these
            //       steps."
            if at >= length {
                return false;
            }
            // 6.1.3 "Let number size be the result of parsing a vint
            //       starting at sequence[iter]."
            let number_size = vint_number_size(sequence, at);
            // 6.1.4 "Increment iter by number size." Never saturates: small.
            let at = at.saturating_add(number_size);
            // 6.1.5 "If iter is greater than or equal to length - 4, abort
            //       these steps."
            if at.saturating_add(4) >= length {
                return false;
            }
            // 6.1.6–6.1.7 "matching a padded sequence 0x77 0x65 0x62 0x6D
            //       ("webm") on sequence at offset iter"; if true, return true.
            if matches_padded_webm(sequence, at) {
                assert(parse_a_vint(sequence@, (iter + 2) as nat).1 == number_size);
                assert(webm_loop(sequence@, iter as nat));
                return true;
            }
            // 6.2 "Increment iter by 1."
            iter = at.saturating_add(1);
        } else {
            // 6.2 "Increment iter by 1."
            iter = next;
        }
    }
    // 7. "Return false."
    false
}

// ===========================================================================
// §6.2.3 Signature for MP3 without ID3.
// ===========================================================================

/// Match an mp3 header (§6.2.3) in `sequence` at offset `s`.
fn match_an_mp3_header_exec(sequence: &[u8], s: usize) -> (r: bool)
    ensures
        r == match_an_mp3_header(sequence@, s as nat),
{
    let length = sequence.len();
    // 1. (Erratum: the four bytes from s.)
    if s > length || length.saturating_sub(s) < 4 {
        return false;
    }
    // Never saturate: s + 3 < length.
    let b0 = byte_at(sequence, s);
    let b1 = byte_at(sequence, s.saturating_add(1));
    let b2 = byte_at(sequence, s.saturating_add(2));
    // 2. (Erratum: "or".)
    if b0 != 0xFF || (b1 & 0xE0) != 0xE0 {
        return false;
    }
    // 3. "Let layer be the result of sequence[s + 1] & 0x06 >> 1."
    let layer = (b1 & 0x06) >> 1u8;
    // 5. "Let bit-rate be sequence[s + 2] & 0xf0 >> 4."
    let bit_rate = (b2 & 0xF0) >> 4u8;
    // 7. "Let sample-rate be sequence[s + 2] & 0x0c >> 2."
    let sample_rate = (b2 & 0x0C) >> 2u8;
    // 4. "If layer is 0, return false." 6. "If bit-rate is 15, return
    //    false." 8. "If sample-rate is 3, return false."
    if layer == 0 || bit_rate == 15 || sample_rate == 3 {
        return false;
    }
    assert(layer <= 3) by (bit_vector)
        requires
            layer == (b1 & 0x06) >> 1u8,
    ;
    // 10. "Let final-layer be the result of 4 - ((sequence[s + 1] & 0x06)
    //     >> 1)." 11. "If final-layer is not 3, return false." 12. "Return
    //     true."
    layer == 1
}

/// The mp3-rates table in §6.2.3.
fn mp3_rate(i: u8) -> (r: u32)
    requires
        i < 15,
    ensures
        r as nat == mp3_rates()[i as int],
{
    match i {
        0 => 0,
        1 => 32000,
        2 => 40000,
        3 => 48000,
        4 => 56000,
        5 => 64000,
        6 => 80000,
        7 => 96000,
        8 => 112000,
        9 => 128000,
        10 => 160000,
        11 => 192000,
        12 => 224000,
        13 => 256000,
        _ => 320000,
    }
}

/// The mp2.5-rates table in §6.2.3.
fn mp2_5_rate(i: u8) -> (r: u32)
    requires
        i < 15,
    ensures
        r as nat == mp2_5_rates()[i as int],
{
    match i {
        0 => 0,
        1 => 8000,
        2 => 16000,
        3 => 24000,
        4 => 32000,
        5 => 40000,
        6 => 48000,
        7 => 56000,
        8 => 64000,
        9 => 80000,
        10 => 96000,
        11 => 112000,
        12 => 128000,
        13 => 144000,
        _ => 160000,
    }
}

/// The samplerate table in §6.2.3.
fn sample_rate(i: u8) -> (r: u32)
    requires
        i < 3,
    ensures
        r as nat == sample_rates()[i as int],
{
    match i {
        0 => 44100,
        1 => 48000,
        _ => 32000,
    }
}

/// Parse an mp3 frame and compute an mp3 frame size (§6.2.3) at offset 0,
/// after "match an mp3 header" accepted it.
fn mp3_frame_size(sequence: &[u8]) -> (r: u32)
    requires
        match_an_mp3_header(sequence@, 0),
    ensures
        r as nat == compute_an_mp3_frame_size(parse_an_mp3_frame(sequence@, 0)),
{
    let b1 = byte_at(sequence, 1);
    let b2 = byte_at(sequence, 2);
    let ghost frame = parse_an_mp3_frame(sequence@, 0);
    // Parse an mp3 frame, 1. "Let version be sequence[s + 1] & 0x18 >> 3."
    let version = (b1 & 0x18) >> 3u8;
    // 2. "Let bitrate-index be sequence[s + 2] & 0xf0 >> 4."
    let bitrate_index = (b2 & 0xF0) >> 4u8;
    // 5. "Let samplerate-index be sequence[s + 2] & 0x0c >> 2."
    let samplerate_index = (b2 & 0x0C) >> 2u8;
    assert(bitrate_index < 16 && samplerate_index < 4 && version < 4) by (bit_vector)
        requires
            bitrate_index == (b2 & 0xF0) >> 4u8,
            samplerate_index == (b2 & 0x0C) >> 2u8,
            version == (b1 & 0x18) >> 3u8,
    ;
    // match an mp3 header rejected 15 and 3.
    assert(bitrate_index != 15 && samplerate_index != 3);
    // 3–4. (Erratum: the MPEG-1 table when version & 0x01 is non-zero.)
    let bitrate = if version & 0x01 != 0 { mp3_rate(bitrate_index) } else { mp2_5_rate(bitrate_index) };
    assert(bitrate as nat == frame.bitrate);
    // 6. "Let samplerate be the value given by samplerate-index in the
    //    sample-rate table." 7. "If version is 2, let samplerate be the
    //    result of samplerate / 2." 8. "If version is 0, let samplerate be
    //    the result of samplerate / 4."
    let base = sample_rate(samplerate_index);
    let samplerate = if version == 2 { base / 2 } else if version == 0 { base / 4 } else { base };
    assert(samplerate as nat == frame.samplerate);
    assert(samplerate >= 8000);
    // 9. "Let pad be sequence[s + 2] & 0x02 >> 1."
    let pad = (b2 & 0x02) >> 1u8;
    // Compute an mp3 frame size, 1. (Erratum: 72 when version & 1 is zero.)
    let scale: u32 = if version & 0x01 == 0 { 72 } else { 144 };
    // 2. "Let size be bitrate * scale / freq."
    assert(bitrate <= 320000);
    assert(bitrate as nat * scale as nat <= 320000 * 144) by (nonlinear_arith)
        requires
            bitrate <= 320000,
            scale <= 144,
    ;
    let product = bitrate.saturating_mul(scale);
    let size = product.checked_div(samplerate).unwrap_or_default();
    assert(size <= product);
    // 3. "If pad is not zero, increment size by 1." Never saturates.
    if pad != 0 {
        size.saturating_add(1)
    } else {
        size
    }
}

/// Matches the signature for MP3 without ID3 (§6.2.3,
/// #signature-for-mp3-without-id3).
pub fn matches_mp3_without_id3_exec(sequence: &[u8]) -> (r: bool)
    ensures
        r == matches_mp3_without_id3(sequence@),
{
    // 2. "Let length be the number of bytes in sequence."
    let length = sequence.len();
    // 3. "Initialize s to 0." 4. "If the result of the operation match mp3
    //    header is false, return false."
    if !match_an_mp3_header_exec(sequence, 0) {
        return false;
    }
    // 5–6. "Parse an mp3 frame on sequence at offset s"; "Let
    //    skipped-bytes [be] the return value of the execution of mp3
    //    framesize computation"
    let skipped_bytes = mp3_frame_size(sequence) as usize;
    // 7. "If skipped-bytes is less than 4, or skipped-bytes is greater than
    //    s - length, return false." (Erratum: length - s.)
    if skipped_bytes < 4 || skipped_bytes > length {
        return false;
    }
    // 8. "Increment s by skipped-bytes." 9. "If the result of the operation
    //    match mp3 header operation is false, return false, else, return
    //    true."
    match_an_mp3_header_exec(sequence, skipped_bytes)
}

// ===========================================================================
// §6.2 The audio or video type pattern matching algorithm.
// ===========================================================================

/// The audio or video type pattern matching algorithm (§6.2).
pub fn match_audio_or_video_type_pattern(input: &[u8]) -> (r: Option<MimeType>)
    ensures
        super::contract::type_pattern_ensures(super::contract::TypePattern::AudioOrVideo, input@, crate::mime_type::record::option_view(r)),
{
    // 1. the table.
    let t = super::tables::match_audio_or_video_table(input);
    if t.is_some() {
        return t;
    }
    // 2. "If input matches the signature for MP4, return "video/mp4"."
    if matches_mp4_exec(input) {
        let m = mime_literal(&[0x76u32, 0x69, 0x64, 0x65, 0x6F], &[0x6Du32, 0x70, 0x34]);
        assert(m@ =~= mime_type(seq![0x76u32, 0x69, 0x64, 0x65, 0x6F], seq![0x6Du32, 0x70, 0x34]));
        return Some(m);
    }
    // 3. "If input matches the signature for WebM, return "video/webm"."
    if matches_webm_exec(input) {
        let m = mime_literal(&[0x76u32, 0x69, 0x64, 0x65, 0x6F], &[0x77u32, 0x65, 0x62, 0x6D]);
        assert(m@ =~= mime_type(seq![0x76u32, 0x69, 0x64, 0x65, 0x6F], seq![0x77u32, 0x65, 0x62, 0x6D]));
        return Some(m);
    }
    // 4. "If input matches the signature for MP3 without ID3, return
    //    "audio/mpeg"."
    if matches_mp3_without_id3_exec(input) {
        let m = mime_literal(&[0x61u32, 0x75, 0x64, 0x69, 0x6F], &[0x6Du32, 0x70, 0x65, 0x67]);
        assert(m@ =~= mime_type(seq![0x61u32, 0x75, 0x64, 0x69, 0x6F], seq![0x6Du32, 0x70, 0x65, 0x67]));
        return Some(m);
    }
    // 5. "Return undefined."
    None
}

} // verus!
