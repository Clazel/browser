# clazel-http

HTTP field syntax for the Clazel browser: the rules every header a server
sends is read with, formally verified with Verus. Part of
[Clazel](../../README.md), a web browser whose parsers of untrusted input
carry machine-checked proofs.

## What it is

An implementation of the field syntax of RFC 9110 "HTTP Semantics" (June
2022), module `field`:

- §5.1 field names, compared case-insensitively; §5.2 and §5.3 the combined
  field value of the lines that share a name (comma SP, in the order
  received), except `Set-Cookie`, which is never combined and is kept as
  separate lines (§5.3's note);
- §5.5 field values (which octets are allowed; whitespace around a value is
  not part of it);
- §5.6.1 lists (`#rule`), split at commas that are not inside a quoted string,
  with the empty elements a recipient must ignore dropped (§5.6.1.2);
- §5.6.2 tokens, §5.6.3 whitespace (OWS, RWS, BWS), §5.6.4 quoted strings and
  quoted pairs (reading and writing), §5.6.6 parameters;
- §8.6 `Content-Length` (`1*DIGIT`, and the list of one repeated value, as
  `42, 42`), with a value above `u64::MAX` reported as too large;
- `Transfer-Encoding` (RFC 9112 §6.1, with §10.1.4's `transfer-coding` and
  `transfer-parameter`) and `Connection` (§7.6.1) as lists.

Strings are bytes: `&[u8]` and `Vec<u8>`.

Not built yet: message framing (RFC 9112 start line, field lines, chunked
coding, message body length), which is Phase 3 item 3.2, and the conformance
tests against other HTTP parsers (item 3.3). The crate therefore stays at
tier 0 (target 2) until both exist: `tests/conformance*.rs` is a
requirement of tier 2 (see [docs/VERIFICATION.md](../../docs/VERIFICATION.md)),
and what is proven below is about `field/` alone.

## Verification

Target tier 2; declared tier 0 until 3.2 and 3.3. The code in `field/` is
proven, in Verus, to equal an executable specification transcribed from the
RFC, over all inputs. Verus also proves that none of it panics, overflows or
indexes out of bounds. The current counts are in the
[status table](../../README.md#verification-status).

- **Proven:** every executable function meets its contract
  (`src/field/contract.rs`) against the spec (`src/field/spec.rs`, with the
  RFC's grammar quoted at each rule). The loops are proven equal to the spec's
  recursion step by step; `Content-Length` is proven never to overflow.
- **Lemmas** (`src/field/lemmas.rs`): a token contains no delimiter (and a
  tchar is "any VCHAR, except delimiters"); unquoting what `quote` wrote gives
  the value back, and quoting what a canonical quoted string unquotes to
  gives the string back; a combined value splits back into its field lines
  when none of them contains a comma (or a quote); `Content-Length` with
  repeated identical values equals the single value; `Set-Cookie` is never
  combined.
- **Examples** (`src/field/examples.rs`): RFC 9110's own examples (§5.2,
  §5.5, §5.6.1.2, §8.3.1's parameters, §8.6) and a case at each rule's
  boundary, evaluated on the spec by Verus.
- **Independent transcription** (`src/field/independent.rs`): written from the
  WHATWG Fetch Standard §2.2 (header names and values, "collect an HTTP
  quoted string", "get, decode, and split"), with MIME Sniffing's token code
  points, and proven equal where the standards agree: header names equal
  `field-name`s for every byte sequence; removing HTTP tab or space is removing
  OWS; Fetch's "get, decode, and split" gives the same pieces as the spec's
  splitter on every byte sequence (and, with the empty pieces dropped, the RFC's
  list elements); Fetch's quoted-string reader agrees with every RFC
  quoted string. Where they differ, the lemmas say so: Fetch keeps empty list
  elements, its *normalize* also removes CR and LF, it accepts header values
  with control bytes other than NUL, CR and LF, and its quoted-string reader
  accepts unterminated strings and any byte. The same agent wrote both
  transcriptions, so this is weaker evidence than a second author's.
- **Mutations:** every deliberate break of the spec listed in
  `mutations.json` (one or more per grammar rule) is certified as caught by a
  checked proof.
- **Conformance:** none yet (item 3.3).
- **Modelling choices** (listed at the top of `src/field/spec.rs`): a list is
  split at commas outside quoted strings and each piece is then checked
  against the element's grammar; "the same decimal value" in §8.6 is read as
  the same digits (`42, 042` is rejected, which §8.6 allows); a transfer
  coding's parameters use §10.1.4's production, not §5.6.6's; a quoted
  parameter value is kept unquoted.

## Trust

The proofs assume the Rust compiler, Verus and its solver, the `vstd`
library, and that the spec transcribes the RFC correctly. The independent
transcription and the examples support that last point but cannot prove it,
and the conformance tests that would support it further are not written. The
full list is in
[docs/VERIFICATION.md](../../docs/VERIFICATION.md#trusted-computing-base-what-we-do-not-prove).

## Usage

Not yet published to crates.io (`publish = false` for now). Use it as a path
dependency:

```toml
[dependencies]
clazel-http = { path = "crates/clazel-http" }
```

```rust
use clazel_http::field::content_length::parse_content_length;
use clazel_http::field::list::list_elements;
use clazel_http::field::params::parse_transfer_encoding;
use clazel_http::field::quoted::parse_quoted_string;

// A list drops empty elements and keeps commas inside quoted strings.
assert_eq!(
    list_elements(b"foo , ,\"a,b\",bar,"),
    vec![b"foo".to_vec(), b"\"a,b\"".to_vec(), b"bar".to_vec()]
);

// A quoted string, unquoted, and where it ends.
assert_eq!(parse_quoted_string(b"\"a\\\"b\" rest"), Some((b"a\"b".to_vec(), 6)));

// Content-Length: one number, a repeated one, or an error.
assert_eq!(parse_content_length(b"42, 42"), Ok(42));
assert!(parse_content_length(b"42, 43").is_err());

// Transfer-Encoding is a list of codings with parameters.
let codings = parse_transfer_encoding(b"gzip, chunked").unwrap_or_default();
assert_eq!(codings.len(), 2);
```

## Licence

MIT, as in the repository's [LICENSE](../../LICENSE). See the
[main README](../../README.md) for the project.
