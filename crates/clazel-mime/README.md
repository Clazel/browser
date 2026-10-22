# clazel-mime

MIME type parsing, serialisation and content sniffing, formally verified with
Verus. Part of [Clazel](../../README.md), a web browser built from the bottom
up by AI using formal verification instead of trust.

## What it is

An implementation of the WHATWG MIME Sniffing Standard:

- `mime_type`: section 4, MIME types: 4.1 the record, 4.2 essence, 4.4
  "parse a MIME type" (from code points or bytes), 4.5 "serialize a MIME
  type" (to code points or bytes) and 4.6 the MIME type groups (image, audio
  or video, font, archive, XML, HTML, scriptable, JavaScript, JSON).
- `sniff`: sections 5.1 (the check-for-apache-bug table), 6 (pattern
  matching, the image, audio or video, font and archive tables, and the MP4,
  WebM and MP3-without-ID3 signatures) and 7 (the MIME type sniffing
  algorithm, 7.1 identifying an unknown MIME type, 7.2 distinguishing text
  from binary).

Strings are sequences of Unicode scalar values held as `u32`. Not included:
"supported by the user agent" and "minimize a supported MIME type" (the
former is an input, `supported`), section 4.3 "valid MIME type string",
how a supplied type is obtained and how long a header to wait for (the
resource header is an input), and section 8 context-specific sniffing.

## Verification

Tier 2: the implementation is proven functionally correct against an
executable specification, with Verus. Verus also proves that it never
panics, overflows or indexes out of bounds. See the
[tiers](../../docs/VERIFICATION.md#tiers).

- Every public function is proven equal to a transcription of the standard
  (`src/mime_type/spec.rs`, `src/sniff/spec.rs`), including the Fetch and
  Infra algorithms they use. Parsing then serialising then parsing gives the
  same record (`lemma_parse_serialize_parse`). Sniffing lemmas include: a
  pattern match never depends on bytes past the end of the input, a match
  survives appending bytes, and section 7.1 never returns a scriptable type
  unless the sniff-scriptable flag is set.
- Independent transcriptions are proven equal to the spec. For MIME types,
  RFC 9110's `media-type` grammar agrees exactly on strings that match it
  and repeat no parameter name (case-insensitively); outside that class the
  WHATWG parser accepts more. For sniffing, the pattern tables are re-read
  from each row's note and the file-format specification it names, MP4 from
  ISO/IEC 14496-12, and the text-or-binary rules from the Unicode BOMs; they
  are proven equal on every input for sections 6.1, 6.3, 6.4, 7.1 and 7.2.
  Not independent: the row order and how the tables combine (same standard),
  and WebM and MP3 without ID3, which no format specification defines.
  WPT's real media files are the evidence for those two.
- Every mutation listed in `mutations.json` is certified as caught by a proof
  that Verus checks.
- Conformance: WPT `mimesniff/mime-types` and `mimesniff/sniffing`, and
  `mimesniff/media` with one expected failure (the standard has no FLAC
  row). Not converted: a gzip-encoded test file and a tentative test for a
  proposed change. Differential tests against `mime` 0.3.17 (parsing) and
  `infer` 0.19.0 (sniffing, format by format).

The spec departs from the literal text of the standard in several places,
each marked in the spec and listed in [docs/ERRATA.md](../../docs/ERRATA.md):
Fetch's "collect an HTTP quoted string" step 7, pattern matching reading
past the end of the input, the WebM signature and "parse a vint", and the
MP3-without-ID3 signature. Some are already open upstream; others are not
yet reported.

Current proof, mutation and conformance counts are in the
[status table](../../README.md#verification-status).

## Trust

The proofs assume the Rust compiler, Verus, and that the spec matches the
standard, which the conformance tests and the independent transcriptions
support but cannot prove. See the
[trusted computing base](../../docs/VERIFICATION.md#trusted-computing-base-what-we-do-not-prove).

## Usage

Not yet published to crates.io (the workspace sets `publish = false`, and
the version is `0.0.0`). Use it as a path dependency:

```toml
[dependencies]
clazel-mime = { path = "crates/clazel-mime" }
```

```rust
use clazel_mime::mime_type::{
    groups::is_image_mime_type, parse::parse_from_bytes, serialize::serialize_to_bytes,
};
use clazel_mime::sniff::algorithms::{computed_mime_type_exec, Resource};

fn main() {
    // Parse and serialise; `None` is failure.
    let m = parse_from_bytes(b" Text/HTML; Charset=\"utf-8\" ").unwrap();
    assert_eq!(serialize_to_bytes(&m), b"text/html;charset=utf-8");
    assert!(parse_from_bytes(b"nonsense").is_none());

    // Sniff a resource with no supplied type from its first bytes.
    let resource = Resource {
        supplied: None,
        check_for_apache_bug: false,
        no_sniff: false,
        header: b"\x89PNG\r\n\x1a\n\0\0\0\rIHDR".to_vec(),
    };
    let computed = computed_mime_type_exec(&resource, false);
    assert!(is_image_mime_type(&computed));
    assert_eq!(serialize_to_bytes(&computed), b"image/png");
}
```

The second argument of `computed_mime_type_exec` says whether the user agent
supports the supplied type.

## Licence

MIT, as in the repository's [LICENSE](../../LICENSE). See the
[main README](../../README.md) for the project.
