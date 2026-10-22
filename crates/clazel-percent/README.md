# clazel-percent

Percent-encoding and percent-decoding for URLs, formally verified with Verus.
Part of [Clazel](../../README.md), a web browser built from the bottom up by
AI using formal verification instead of trust.

## What it is

An implementation of WHATWG URL Standard section 1.3, "Percent-encoded
bytes": "percent-encode", "percent-decode" (on bytes and on strings),
"UTF-8 percent-encode", and the eight percent-encode sets (C0 control,
fragment, query, special-query, path, userinfo, component and
`application/x-www-form-urlencoded`). Strings are sequences of Unicode
scalar values held as `u32`. UTF-8 encoding comes from `clazel-encoding`.

Not included: "percent-encode after encoding" for any encoding other than
UTF-8 (other encoders arrive with HTML in a later phase), and the rest of
the URL Standard (see `clazel-url`).

## Verification

Tier 2: the implementation is proven functionally correct against an
executable specification, with Verus. Verus also proves that it never
panics, overflows or indexes out of bounds. See the
[tiers](../../docs/VERIFICATION.md#tiers).

- Every public function is proven equal to a transcription of the standard
  (`src/spec.rs`, with the standard's step numbers).
- Decoding inverts encoding for every set. The only exceptions are a `%`
  that the set leaves alone, and spaces in the form set.
- A second transcription from RFC 3986 section 2.1 (`src/independent.rs`)
  is proven equal to percent-encode for every byte, and to percent-decode on
  exactly the inputs RFC 3986 can decode. For each set, a lemma proves that
  the listed code points are exactly where its membership differs from the
  RFC rule for the matching URL component, so the equivalence is restricted
  to where the two standards agree.
- Every mutation listed in `mutations.json` is certified as caught by a proof
  that Verus checks.
- Conformance: WPT `url/percent-encoding.json` passes for every UTF-8 row.
  The rows for other encodings are expected failures, each listed by name
  in the test and counted separately. A differential test against
  `percent-encoding` and `form_urlencoded` (rust-url) covers every scalar
  value in all eight sets. rust-url's path set lacks U+005E (^), which the
  standard added in March 2025, and the test asserts that this is the only
  difference.

Modelling choices (listed at the top of `src/spec.rs`): a percent-encode set
is an enum naming one of the eight sets; the byte loops are recursion over a
read position; "percent-encode after encoding" is transcribed for UTF-8 only.
The functions that take strings require scalar values (no surrogates).

Current proof, mutation and conformance counts are in the
[status table](../../README.md#verification-status).

## Trust

The proofs assume the Rust compiler, Verus, and that the spec matches the
standard, which the conformance tests and the independent transcription
support but cannot prove. See the
[trusted computing base](../../docs/VERIFICATION.md#trusted-computing-base-what-we-do-not-prove).

## Usage

Not yet published to crates.io (the workspace sets `publish = false`, and
the version is `0.0.0`). Use it as a path dependency:

```toml
[dependencies]
clazel-percent = { path = "crates/clazel-percent" }
```

```rust
use clazel_percent::{
    decode::percent_decode, encode::utf8_percent_encode, spec::PercentEncodeSet,
};

fn main() {
    // Strings are code points as `u32`.
    let input: Vec<u32> = "a b/é".chars().map(|c| c as u32).collect();
    let out = utf8_percent_encode(&input, PercentEncodeSet::Path);
    let out: String = out.iter().filter_map(|&c| char::from_u32(c)).collect();
    assert_eq!(out, "a%20b/%C3%A9");

    // Percent-decoding works on bytes and leaves malformed escapes alone.
    assert_eq!(percent_decode(b"a%20b%zz%C3%A9"), "a b%zzé".as_bytes());
}
```

## Licence

MIT, as in the repository's [LICENSE](../../LICENSE). See the
[main README](../../README.md) for the project.
