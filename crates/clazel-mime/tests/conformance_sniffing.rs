//! MIME sniffing conformance (docs/phases/phase-1.md item 1.7).
//!
//! The proofs show the exec code equals `sniff/spec.rs`, and
//! `sniff/independent.rs` shows the spec's tables agree with their notes
//! and the file-format specifications. This file checks them against the
//! outside world:
//!
//! 1. WPT `mimesniff/media/` and `mimesniff/sniffing/`: the resources those
//!    browser tests serve, converted by `cargo xtask testdata`
//!    (`tests/data/wpt-mimesniff/`, whose SOURCE.md says what each test
//!    asserts and what is not converted).
//! 2. A differential test against the `infer` crate (a file-type detector
//!    by magic numbers, written without the WHATWG standard): format by
//!    format, `infer`'s rule is the same as the standard's, looser, or
//!    stricter, as recorded in `formats()`, on seeded and random headers;
//!    and both name the WPT media vectors alike.

use clazel_mime::mime_type::parse::parse_from_bytes;
use clazel_mime::mime_type::record::MimeType;
use clazel_mime::sniff::algorithms::{
    Resource, check_for_apache_bug_exec, computed_mime_type_exec, identify_unknown_mime_type_exec,
    match_archive_type_pattern, match_audio_or_video_type_pattern, match_font_type_pattern,
    match_image_type_pattern,
};

/// One converted WPT resource.
struct Case {
    file: &'static str,
    /// The Content-Type it is served with; `None` for the media vectors,
    /// which are served with each of `MEDIA_CONTENT_TYPES`.
    content_type: Option<&'static str>,
    bytes: &'static [u8],
}

// `MEDIA_CONTENT_TYPES`, `MEDIA`, `MISLABELED`, `FEEDS`, generated from the
// vendored WPT files.
include!("generated/wpt_mimesniff.rs");

fn essence(m: &MimeType) -> String {
    let mut s: String = m
        .type_
        .iter()
        .map(|&c| char::from_u32(c).unwrap_or('\u{FFFD}'))
        .collect();
    s.push('/');
    s.extend(
        m.subtype
            .iter()
            .map(|&c| char::from_u32(c).unwrap_or('\u{FFFD}')),
    );
    s
}

/// The resource header (§5.2): at most the first 1445 bytes.
fn header(bytes: &[u8]) -> &[u8] {
    bytes.get(..1445).unwrap_or(bytes)
}

/// The computed MIME type (§7) of `bytes` served with `content_type`
/// ("" is no Content-Type), the supplied type being supported.
fn computed(content_type: &str, bytes: &[u8]) -> String {
    let ct = content_type.as_bytes();
    let resource = Resource {
        supplied: if ct.is_empty() {
            None
        } else {
            parse_from_bytes(ct)
        },
        check_for_apache_bug: check_for_apache_bug_exec(ct),
        no_sniff: false,
        header: header(bytes).to_vec(),
    };
    essence(&computed_mime_type_exec(&resource, true))
}

/// `media-sniff.window.js`: "<vector> loads when served with Content-Type
/// <type>". The standard's part: §6.2 recognises every vector but FLAC
/// (no FLAC signature in the standard), and with no Content-Type §7 gives
/// the same type.
#[test]
fn wpt_media() {
    let expected = |file: &str| match file {
        "mp3-raw.mp3" | "mp3-with-id3.mp3" => Some("audio/mpeg"),
        "ogg.ogg" => Some("application/ogg"),
        "mp4.mp4" => Some("video/mp4"),
        "wav.wav" => Some("audio/wave"),
        "webm.webm" => Some("video/webm"),
        // A gap in the standard: §6.2 has no FLAC row.
        "flac.flac" => None,
        _ => Some("(not a known vector)"),
    };
    let mut failures = Vec::new();
    for case in MEDIA {
        let want = expected(case.file);
        let got = match_audio_or_video_type_pattern(header(case.bytes)).map(|m| essence(&m));
        if got.as_deref() != want {
            failures.push(format!(
                "{}: §6.2 gave {got:?}, expected {want:?}",
                case.file
            ));
        }
        for ct in MEDIA_CONTENT_TYPES {
            if ct.is_empty() {
                let got = computed(ct, case.bytes);
                let want = want.unwrap_or("application/octet-stream");
                if got != want {
                    failures.push(format!(
                        "{} with no Content-Type: §7 gave {got}, expected {want}",
                        case.file
                    ));
                }
            }
        }
    }
    assert!(MEDIA.len() == 7 && !MEDIA_CONTENT_TYPES.is_empty());
    assert!(
        failures.is_empty(),
        "{} failures:\n{}",
        failures.len(),
        failures.join("\n")
    );
}

/// `mislabeled-binary-resource.tentative.window.js`: served as text/plain,
/// binary data must not be sniffed into a privileged type (download:
/// application/octet-stream), HTML must not be rendered as HTML, and a PNG
/// must not become an image ("produces application/octet-stream").
#[test]
fn wpt_mislabeled_binary() {
    let mut failures = Vec::new();
    for case in MISLABELED {
        let ct = case.content_type.unwrap_or_default();
        assert!(
            check_for_apache_bug_exec(ct.as_bytes()),
            "{}: {ct} sets the flag",
            case.file
        );
        let want = match case.file {
            "html-content.html" => "text/plain",
            _ => "application/octet-stream",
        };
        let got = computed(ct, case.bytes);
        if got != want {
            failures.push(format!("{}: gave {got}, expected {want}", case.file));
        }
    }
    assert!(MISLABELED.len() == 3);
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

/// `html.window.js`: "HTML is not sniffed for a feed": atom.html and
/// rss.html, served as text/html, have content type text/html.
#[test]
fn wpt_feeds() {
    for case in FEEDS {
        let got = computed(case.content_type.unwrap_or_default(), case.bytes);
        assert_eq!(got, "text/html", "{}", case.file);
    }
    assert!(FEEDS.len() == 2);
}

fn image(b: &[u8]) -> String {
    match_image_type_pattern(b)
        .map(|m| essence(&m))
        .unwrap_or_default()
}

fn av(b: &[u8]) -> String {
    match_audio_or_video_type_pattern(b)
        .map(|m| essence(&m))
        .unwrap_or_default()
}

fn font(b: &[u8]) -> String {
    match_font_type_pattern(b)
        .map(|m| essence(&m))
        .unwrap_or_default()
}

fn archive(b: &[u8]) -> String {
    match_archive_type_pattern(b)
        .map(|m| essence(&m))
        .unwrap_or_default()
}

fn unknown(b: &[u8]) -> String {
    essence(&identify_unknown_mime_type_exec(b, true))
}

/// How `infer`'s rule for a format relates to the standard's.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Relation {
    /// The same bytes.
    Same,
    /// `infer` checks a prefix of what the standard checks (or less), so
    /// whatever the standard recognises, `infer` does.
    InferLooser,
    /// `infer` checks more, so whatever it recognises, the standard does.
    InferStricter,
}

/// One format both know: the standard's answer, `infer`'s, and how they
/// relate. Each relation is read off `infer` 0.19.0's matcher.
struct Format {
    name: &'static str,
    ours: fn(&[u8]) -> bool,
    theirs: fn(&[u8]) -> bool,
    relation: Relation,
    /// A header with the format's signature, for seeding.
    seed: &'static [u8],
}

fn formats() -> Vec<Format> {
    use Relation::{InferLooser, InferStricter, Same};
    vec![
        // infer: the first 4 of the 8 signature bytes.
        Format { name: "png", ours: |b| image(b) == "image/png", theirs: infer::image::is_png, relation: InferLooser, seed: b"\x89PNG\r\n\x1a\n" },
        // infer: "GIF" only.
        Format { name: "gif", ours: |b| image(b) == "image/gif", theirs: infer::image::is_gif, relation: InferLooser, seed: b"GIF89a" },
        Format { name: "jpeg", ours: |b| image(b) == "image/jpeg", theirs: infer::image::is_jpeg, relation: Same, seed: b"\xFF\xD8\xFF" },
        // infer: "WEBP" at 8 only.
        Format { name: "webp", ours: |b| image(b) == "image/webp", theirs: infer::image::is_webp, relation: InferLooser, seed: b"RIFF\x00\x00\x00\x00WEBPVP" },
        Format { name: "bmp", ours: |b| image(b) == "image/bmp", theirs: infer::image::is_bmp, relation: Same, seed: b"BM" },
        // The standard also calls a cursor (00 00 02 00) image/x-icon;
        // infer only checks the icon type, which the standard checks first.
        Format { name: "ico", ours: |b| image(b) == "image/x-icon" && b.get(2) == Some(&1), theirs: infer::image::is_ico, relation: Same, seed: b"\x00\x00\x01\x00" },
        // infer: the EBML magic only (any Matroska file).
        Format { name: "webm", ours: |b| av(b) == "video/webm", theirs: infer::video::is_webm, relation: InferLooser, seed: b"\x1A\x45\xDF\xA3\x9F\x42\x82\x84webm" },
        // infer: "RIFF", then "AVI" at 8 (not the space).
        Format { name: "avi", ours: |b| av(b) == "video/avi", theirs: infer::video::is_avi, relation: InferLooser, seed: b"RIFF\x00\x00\x00\x00AVI " },
        // infer: "MThd" without the header length 6.
        Format { name: "midi", ours: |b| av(b) == "audio/midi", theirs: infer::audio::is_midi, relation: InferLooser, seed: b"MThd\x00\x00\x00\x06" },
        // infer: "OggS" without the version byte 0.
        Format { name: "ogg", ours: |b| av(b) == "application/ogg", theirs: infer::audio::is_ogg, relation: InferLooser, seed: b"OggS\x00" },
        // ID3v2-tagged MP3 only: for frames without a tag, infer checks
        // FF FB and the standard parses two frame headers, and neither
        // rule implies the other.
        Format { name: "mp3 (ID3)", ours: |b| av(b) == "audio/mpeg" && b.starts_with(b"ID3"), theirs: |b| infer::audio::is_mp3(b) && b.starts_with(b"ID3"), relation: Same, seed: b"ID3" },
        Format { name: "wav", ours: |b| av(b) == "audio/wave", theirs: infer::audio::is_wav, relation: Same, seed: b"RIFF\x00\x00\x00\x00WAVE" },
        Format { name: "aiff", ours: |b| av(b) == "audio/aiff", theirs: infer::audio::is_aiff, relation: Same, seed: b"FORM\x00\x00\x00\x00AIFF" },
        // infer also needs flavor 0x00010000 at 4. (The standard's EOT row
        // comes first, so "ours" counts an EOT match too.)
        Format { name: "woff", ours: |b| matches!(font(b).as_str(), "font/woff" | "application/vnd.ms-fontobject"), theirs: infer::font::is_woff, relation: InferStricter, seed: b"wOFF\x00\x01\x00\x00" },
        Format { name: "woff2", ours: |b| matches!(font(b).as_str(), "font/woff2" | "application/vnd.ms-fontobject"), theirs: infer::font::is_woff2, relation: InferStricter, seed: b"wOF2\x00\x01\x00\x00" },
        // infer also needs a 0 at 4.
        Format { name: "ttf", ours: |b| matches!(font(b).as_str(), "font/ttf" | "application/vnd.ms-fontobject"), theirs: infer::font::is_ttf, relation: InferStricter, seed: b"\x00\x01\x00\x00\x00" },
        Format { name: "otf", ours: |b| matches!(font(b).as_str(), "font/otf" | "application/vnd.ms-fontobject"), theirs: infer::font::is_otf, relation: InferStricter, seed: b"OTTO\x00" },
        // infer also checks the EOT version at 8.
        Format { name: "eot", ours: |b| font(b) == "application/vnd.ms-fontobject", theirs: infer::archive::is_eot, relation: InferStricter, seed: b"\x00\x00\x00\x00\x00\x00\x00\x00\x02\x00\x01\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00LP" },
        Format { name: "gzip", ours: |b| archive(b) == "application/x-gzip", theirs: infer::archive::is_gz, relation: Same, seed: b"\x1F\x8B\x08" },
        // infer also takes PK 05 06, PK 07 08 and WinZip's PK00PK 03 04.
        Format { name: "zip", ours: |b| archive(b) == "application/zip", theirs: infer::archive::is_zip, relation: InferLooser, seed: b"PK\x03\x04" },
        // infer also takes RAR 5 (07 01 after "Rar!" 1A).
        Format { name: "rar", ours: |b| archive(b) == "application/x-rar-compressed", theirs: infer::archive::is_rar, relation: InferLooser, seed: b"Rar!\x1A\x07\x00" },
        // infer: "%PDF" without the "-".
        Format { name: "pdf", ours: |b| unknown(b) == "application/pdf", theirs: infer::archive::is_pdf, relation: InferLooser, seed: b"%PDF-" },
        // infer: "%!" only.
        Format { name: "postscript", ours: |b| unknown(b) == "application/postscript", theirs: infer::archive::is_ps, relation: InferLooser, seed: b"%!PS-Adobe-" },
    ]
}

/// A small deterministic generator (xorshift).
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }

    fn below(&mut self, n: usize) -> usize {
        self.next()
            .checked_rem(u64::try_from(n).unwrap_or(1))
            .and_then(|r| usize::try_from(r).ok())
            .unwrap_or(0)
    }

    fn byte(&mut self) -> u8 {
        self.next().to_le_bytes().first().copied().unwrap_or(0)
    }
}

/// Inputs for one format: random bytes, and its seed (whole, cut short,
/// or with one byte changed) followed by random bytes.
fn inputs(rng: &mut Rng, seed: &[u8], n: usize) -> Vec<Vec<u8>> {
    let mut out = Vec::new();
    for i in 0..n {
        let mut v: Vec<u8> = Vec::new();
        if i % 4 != 0 {
            let keep = seed
                .len()
                .saturating_sub(rng.below(3).saturating_sub(1).min(seed.len()));
            v.extend_from_slice(seed.get(..keep).unwrap_or(seed));
            if i % 4 == 2 && !v.is_empty() {
                let at = rng.below(v.len());
                if let Some(b) = v.get_mut(at) {
                    *b = rng.byte();
                }
            }
        }
        let tail = rng.below(40);
        v.extend((0..tail).map(|_| rng.byte()));
        out.push(v);
    }
    out
}

/// Format by format, the standard's answer and `infer`'s stand in the
/// recorded relation on every input, and both recognise the format's seed
/// (so no relation holds vacuously).
#[test]
fn differential_infer() {
    let n = if cfg!(miri) { 40 } else { 4000 };
    let mut rng = Rng(0x9E37_79B9_7F4A_7C15);
    let mut failures = Vec::new();
    for f in formats() {
        let mut seed = f.seed.to_vec();
        seed.resize(48, 0);
        if !(f.ours)(&seed) || !(f.theirs)(&seed) {
            failures.push(format!(
                "{}: seed not recognised (ours {}, infer {})",
                f.name,
                (f.ours)(&seed),
                (f.theirs)(&seed)
            ));
        }
        for input in inputs(&mut rng, f.seed, n) {
            let (o, t) = ((f.ours)(&input), (f.theirs)(&input));
            let ok = match f.relation {
                Relation::Same => o == t,
                Relation::InferLooser => !o || t,
                Relation::InferStricter => !t || o,
            };
            if !ok {
                failures.push(format!(
                    "{} ({:?}): ours {o}, infer {t} on {input:02X?}",
                    f.name, f.relation
                ));
                break;
            }
        }
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

/// Both agree on the WPT vectors they can both name.
#[test]
fn differential_infer_wpt_media() {
    for case in MEDIA {
        let t = infer::get(case.bytes).map(|t| t.extension());
        let o = av(header(case.bytes));
        let want = match t {
            Some("mp3") => "audio/mpeg",
            Some("ogg") => "application/ogg",
            Some("mp4") => "video/mp4",
            Some("wav") => "audio/wave",
            Some("webm") => "video/webm",
            // FLAC: infer knows it, the standard has no row.
            Some("flac") => "",
            // Anything else: infer names it something unexpected.
            _ => "(infer: unexpected)",
        };
        assert_eq!(o, want, "{}", case.file);
    }
}

/// §7.1 on the vectors with the sniff-scriptable flag set and unset gives
/// the same (none of them looks scriptable).
#[test]
fn wpt_media_unknown() {
    for case in MEDIA {
        let a = essence(&identify_unknown_mime_type_exec(header(case.bytes), true));
        let b = essence(&identify_unknown_mime_type_exec(header(case.bytes), false));
        assert_eq!(a, b, "{}", case.file);
    }
}
