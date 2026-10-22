# clazel-url

The WHATWG URL parser, serialiser and API setters, formally verified with
Verus. Part of [Clazel](../../README.md), a web browser built from the bottom
up by AI using formal verification instead of trust.

## What it is

An implementation of the WHATWG URL Standard (the `url.bs` source at a pinned
commit):

- `host`: section 3, hosts: 3.1 representation, 3.2 forbidden host code
  points, 3.5 "host parser" (with the IPv4 number parser, IPv4 parser, IPv6
  parser and opaque-host parser) and 3.6 host serializing.
- `url`: section 4, URLs: 4.1 the URL record, 4.2 miscellaneous, 4.4 "basic
  URL parser" (the whole state machine, including state override) and 4.5 URL
  serializing.
- `api`: section 6.1, the ten setters of the `URL` class (`href`, `protocol`,
  `username`, `password`, `host`, `hostname`, `port`, `pathname`, `search`
  and `hash`) as functions on the URL record.

Strings are sequences of Unicode scalar values held as `u32`. The host
parser's domain step runs `clazel-idna`'s URL domain parser (UTS #46
ToASCII); percent-encoding and UTF-8 come from `clazel-percent` and
`clazel-encoding`.

Not included: `URLSearchParams` (section 6.2),
`application/x-www-form-urlencoded` (section 5), the URL constructor,
`parse`, `canParse`, `origin` and `toJSON`, the blob URL entry, validation
errors (they never change a result), public suffixes, and query encodings
other than UTF-8 (legacy encodings arrive with HTML in a later phase).

## Verification

Tier 2: the implementation is proven functionally correct against an
executable specification, with Verus. Verus also proves that it never
panics, overflows or indexes out of bounds. See the
[tiers](../../docs/VERIFICATION.md#tiers).

- The host parser, the basic URL parser (with and without a state override),
  the serialisers and the ten setters are proven equal to a transcription of
  the standard, with one spec function per state or setter and the standard's
  step numbers. The spec takes the domain parser as a parameter and every
  theorem holds for any domain parser; the executable code is proven equal
  to the spec instantiated with `clazel-idna`'s.
- Lemmas: the parser is total (within 12 (n + 1) runs); every result meets
  section 4.1's invariants, and so does the result of every setter; setting
  the same value twice equals setting it once for `username`, `password`,
  `port`, `pathname`, `search`, `hash`, `protocol` and `hostname`; serialising
  then parsing a host is the identity.
- Independent transcriptions from RFC 3986, RFC 4291 and RFC 5952 are proven
  to agree with the spec **on stated classes only**, because the standards
  differ elsewhere: host text forms (the converse for IPv6 is tested, not
  proven), reference resolution (a class of non-special bases and path-only
  references), and the component grammar for each setter but `href`. Special
  hosts (the domain parser) are outside RFC 3986.
- Every mutation listed in `mutations.json` is certified as caught by a proof
  that Verus checks. Two are not covered: removing host state step 3.1 (the
  standard's check is redundant with `clazel-idna`'s domain parser, and
  Verus's evaluator does not finish on it), and the `beStrict` argument in
  the instantiated domain parser, whose certificates Verus cannot evaluate.
- Conformance: every row of WPT `url/` `urltestdata.json`, `setters_tests.json`
  and `toascii.json`, and the host rows of `urltestdata.json`, pass through
  the proven code with no expected failures. Differential tests against
  rust-url and `std::net` list the named classes where rust-url disagrees
  with the standard; any other mismatch fails them.

Known gaps: the round trip (serialise then parse returns the URL, so parse
then serialise is idempotent) is proven only for URLs with no credentials, an
opaque host or a domain the domain parser leaves unchanged, a non-"file"
scheme and a list path; it is tested, not proven, for credentials, IP and
empty hosts, opaque paths, "file" URLs and other domains. Idempotence of the
`host` and `href` setters is not proven. Modelling choices are at the top of
`src/url/spec.rs`, `src/host/spec.rs` and `src/api/spec.rs`.

Current proof, mutation and conformance counts are in the
[status table](../../README.md#verification-status).

## Trust

The proofs assume the Rust compiler, Verus, and that the spec matches the
standard, which the conformance tests and the independent transcriptions
support but cannot prove. They also rely on `clazel-idna`, `clazel-percent`
and `clazel-encoding` meeting their contracts, including `clazel-idna`'s
generated Unicode tables. See the
[trusted computing base](../../docs/VERIFICATION.md#trusted-computing-base-what-we-do-not-prove).

## Usage

Not yet published to crates.io (the workspace sets `publish = false`, and
the version is `0.0.0`). Use it as a path dependency:

```toml
[dependencies]
clazel-url = { path = "crates/clazel-url" }
```

```rust
use clazel_url::api::setters::{set_hash, set_port};
use clazel_url::url::parse::basic_url_parser;

fn u(s: &str) -> Vec<u32> {
    s.chars().map(|c| c as u32).collect()
}
fn s(v: &[u32]) -> String {
    v.iter().filter_map(|&c| char::from_u32(c)).collect()
}

fn main() {
    // Parse against a base; `None` is failure.
    let base = basic_url_parser(&u("https://example.com/a/b/c?x"), None).unwrap();
    let mut url = basic_url_parser(&u("../d/./e?q=1#f"), Some(&base)).unwrap();
    assert_eq!(s(&url.serialize(false)), "https://example.com/a/d/e?q=1#f");

    // Setters change the record in place.
    set_port(&mut url, &u("8080"));
    set_hash(&mut url, &u("top"));
    assert_eq!(s(&url.serialize(false)), "https://example.com:8080/a/d/e?q=1#top");

    // Domains are converted with IDNA, and failures are `None`.
    let h = basic_url_parser(&u("HTTP://Bücher.Example:80/"), None).unwrap();
    assert_eq!(s(&h.serialize(false)), "http://xn--bcher-kva.example/");
    assert!(basic_url_parser(&u("http://"), None).is_none());
}
```

## Licence

MIT, as in the repository's [LICENSE](../../LICENSE). See the
[main README](../../README.md) for the project.
