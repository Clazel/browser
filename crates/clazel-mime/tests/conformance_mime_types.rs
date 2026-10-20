//! MIME type conformance (docs/phases/phase-1.md item 1.7).
//!
//! The proofs show the implementation equals `mime_type/spec.rs`, and
//! `independent.rs` shows the spec agrees with RFC 9110 on valid media
//! types. This file checks both against the outside world:
//!
//! 1. Every case in WPT `mimesniff/mime-types/resources/` (`mime-types.json`
//!    and `generated-mime-types.json`), converted from the vendored files by
//!    `cargo xtask testdata` (`tests/data/wpt-mime-types/`): parse a MIME
//!    type, then serialize, gives the expected output, or fails. Each
//!    expected output must also parse back to itself (the round trip that
//!    `lemmas::lemma_parse_serialize_parse` proves).
//! 2. A differential test against the `mime` crate (hyperium's, used by
//!    `reqwest` and `hyper`), on random strings matching RFC 9110's
//!    `media-type` with no repeated parameter names: the class on which
//!    `independent::lemma_equals_parse_a_mime_type` proves the WHATWG parser
//!    agrees with the RFC. Under Miri the sample is smaller.

use clazel_mime::mime_type::groups::{
    is_html_mime_type, is_javascript_mime_type, is_xml_mime_type,
};
use clazel_mime::mime_type::parse::{parse, parse_from_bytes};
use clazel_mime::mime_type::serialize::{serialize, serialize_to_bytes};

/// One converted WPT case.
struct Case {
    file: &'static str,
    index: usize,
    section: &'static str,
    input: &'static [u32],
    /// `None`: parsing must fail.
    output: Option<&'static [u32]>,
}

// `const WPT: &[Case]`, generated from the vendored WPT files.
include!("generated/wpt_mime_types.rs");

fn text(s: &[u32]) -> String {
    s.iter()
        .map(|&c| char::from_u32(c).unwrap_or('\u{FFFD}'))
        .collect()
}

fn scalars(s: &str) -> Vec<u32> {
    s.chars().map(u32::from).collect()
}

#[test]
fn wpt_mime_types() {
    let mut failures = Vec::new();
    for case in WPT {
        let got = parse(case.input).map(|m| serialize(&m));
        if got.as_deref() != case.output {
            failures.push(format!(
                "{}[{}] ({}): {:?} gave {:?}, expected {:?}",
                case.file,
                case.index,
                case.section,
                text(case.input),
                got.as_deref().map(text),
                case.output.map(text)
            ));
        }
        if let Some(out) = case.output {
            let again = parse(out).map(|m| serialize(&m));
            if again.as_deref() != Some(out) {
                failures.push(format!(
                    "{}[{}]: output {:?} does not round-trip",
                    case.file,
                    case.index,
                    text(out)
                ));
            }
        }
        // Inputs that are byte-compatible (every code point at most U+00FF)
        // parse the same way from bytes, and serialize to the same bytes.
        if case.input.iter().all(|&c| c <= 0xFF) {
            let bytes: Vec<u8> = case
                .input
                .iter()
                .filter_map(|&c| u8::try_from(c).ok())
                .collect();
            let from_bytes = parse_from_bytes(&bytes).map(|m| serialize_to_bytes(&m));
            let expected: Option<Vec<u8>> = case
                .output
                .map(|o| o.iter().filter_map(|&c| u8::try_from(c).ok()).collect());
            if from_bytes != expected {
                failures.push(format!("{}[{}]: from bytes differs", case.file, case.index));
            }
        }
    }
    assert!(WPT.len() > 900, "only {} WPT cases", WPT.len());
    assert!(
        failures.is_empty(),
        "{} of {} WPT cases fail:\n{}",
        failures.len(),
        WPT.len(),
        failures.join("\n")
    );
}

#[test]
fn groups() {
    let p = |s: &str| parse(&scalars(s));
    assert!(p("text/html;charset=utf-8").is_some_and(|m| is_html_mime_type(&m)));
    assert!(p("Text/JavaScript").is_some_and(|m| is_javascript_mime_type(&m)));
    assert!(p("image/svg+xml").is_some_and(|m| is_xml_mime_type(&m)));
    assert!(p("text/plain").is_some_and(|m| !is_html_mime_type(&m)));
}

/// A small deterministic generator (xorshift), so failures reproduce.
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }
    fn below(&mut self, n: usize) -> usize {
        usize::try_from(
            self.next()
                .checked_rem(u64::try_from(n).unwrap_or(1))
                .unwrap_or(0),
        )
        .unwrap_or(0)
    }
    fn pick(&mut self, s: &[u8]) -> u8 {
        s.get(self.below(s.len())).copied().unwrap_or(b'a')
    }
}

const TCHAR: &[u8] =
    b"!#$%&'*+-.^_`|~0123456789abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ";
const OWS: &[u8] = b" \t";

fn token(r: &mut Rng) -> String {
    let n = r.below(6).saturating_add(1);
    (0..n).map(|_| char::from(r.pick(TCHAR))).collect()
}

fn ows(r: &mut Rng) -> String {
    let n = if r.below(3) == 0 { r.below(3) } else { 0 };
    (0..n).map(|_| char::from(r.pick(OWS))).collect()
}

/// `OWS` the `mime` crate accepts: at most one SP, and only after ";".
fn ows_simple(r: &mut Rng) -> String {
    if r.below(2) == 0 {
        " ".to_owned()
    } else {
        String::new()
    }
}

/// A random string matching RFC 9110 `media-type`, and its parameters as
/// (lowercased name, value) with no name twice. With `simple`, only the
/// forms the `mime` crate accepts (see [`differential_mime_crate`]).
fn media_type(r: &mut Rng, simple: bool) -> (String, String, String, Vec<(String, String)>) {
    let t = token(r);
    let st = token(r);
    let mut s = format!("{t}/{st}");
    let mut params: Vec<(String, String)> = Vec::new();
    for _ in 0..r.below(4) {
        if simple {
            s.push(';');
            s.push_str(&ows_simple(r));
        } else {
            s.push_str(&ows(r));
            s.push(';');
            s.push_str(&ows(r));
        }
        if !simple && r.below(5) == 0 {
            continue; // [ parameter ] absent
        }
        let name = token(r);
        if params.iter().any(|(n, _)| n.eq_ignore_ascii_case(&name))
            || name.eq_ignore_ascii_case("charset")
        {
            if simple {
                s.pop();
                s.truncate(s.trim_end_matches([' ', ';']).len());
            }
            continue;
        }
        let value = token(r);
        s.push_str(&name);
        s.push('=');
        if r.below(2) == 0 {
            s.push_str(&value);
        } else {
            s.push('"');
            s.push_str(&value);
            s.push('"');
        }
        params.push((name.to_ascii_lowercase(), value));
    }
    (s, t.to_ascii_lowercase(), st.to_ascii_lowercase(), params)
}

/// Our parser on random valid media types, all forms: it returns what
/// RFC 9110 says the string denotes.
#[test]
fn rfc_9110_media_types() {
    let rounds = if cfg!(miri) { 200 } else { 50_000 };
    let mut r = Rng(0x2545_F491_4F6C_DD1D);
    for _ in 0..rounds {
        let (s, t, st, params) = media_type(&mut r, false);
        let ours = parse(&scalars(&s));
        assert!(ours.is_some(), "{s:?} did not parse");
        let Some(ours) = ours else { continue };
        assert_eq!(text(&ours.type_), t, "{s:?}");
        assert_eq!(text(&ours.subtype), st, "{s:?}");
        let ours_params: Vec<(String, String)> = ours
            .parameters
            .iter()
            .map(|(n, v)| (text(n), text(v)))
            .collect();
        assert_eq!(ours_params, params, "{s:?}");
    }
}

/// Against the `mime` crate, on the valid media types it accepts. It
/// rejects some strings RFC 9110 allows (HTAB in `OWS`, `OWS` before ";",
/// an empty parameter as in "a/b;;c=d"), so the generator keeps to the
/// forms it takes, and every one must be accepted. It also lowercases
/// `charset` values, so `charset` is not generated.
#[test]
fn differential_mime_crate() {
    let rounds = if cfg!(miri) { 200 } else { 50_000 };
    let mut r = Rng(0x9E37_79B9_7F4A_7C15);
    for _ in 0..rounds {
        let (s, t, st, params) = media_type(&mut r, true);
        let ours = parse(&scalars(&s));
        assert!(ours.is_some(), "{s:?} did not parse");
        let Some(ours) = ours else { continue };
        let ours_params: Vec<(String, String)> = ours
            .parameters
            .iter()
            .map(|(n, v)| (text(n), text(v)))
            .collect();
        assert_eq!(ours_params, params, "{s:?}");
        let theirs = s.parse::<mime::Mime>();
        assert!(theirs.is_ok(), "mime crate rejects {s:?}: {theirs:?}");
        let Ok(theirs) = theirs else { continue };
        assert_eq!(theirs.essence_str(), format!("{t}/{st}"), "{s:?}");
        assert_eq!(text(&ours.type_), t, "{s:?}");
        assert_eq!(text(&ours.subtype), st, "{s:?}");
        let theirs_params: Vec<(String, String)> = theirs
            .params()
            .map(|(n, v)| (n.as_str().to_owned(), v.as_str().to_owned()))
            .collect();
        assert_eq!(ours_params, theirs_params, "{s:?}");
    }
}
