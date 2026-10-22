# clazel-base64

Forgiving base64 decode and encode, formally verified with Verus. Part of
[Clazel](../../README.md), a web browser built from the bottom up by AI using
formal verification instead of trust.

## What it is

An implementation of the WHATWG Infra Standard, section 7 "Forgiving base64":
the "forgiving-base64 decode" and "forgiving-base64 encode" algorithms (the
latter applies RFC 4648 section 4). Strings are sequences of Unicode code
points held as `u32`, so the encoder's output is exactly what the decoder
accepts.

Not included: the JavaScript `atob`/`btoa` bindings, the `data:` URL layer,
and URL-safe base64 (RFC 4648 section 5), which the standard does not use.

## Verification

Tier 2: the implementation is proven functionally correct against an
executable specification, with Verus. Verus also proves that it never
panics, overflows or indexes out of bounds. See the
[tiers](../../docs/VERIFICATION.md#tiers).

- `decode` and `encode` are proven equal to a step-by-step transcription of
  the standard (`src/spec.rs`, with the standard's step numbers).
- Decoding inverts encoding, and the other lemmas in `src/lemmas.rs` hold
  (for example, step 9's 12-or-18-bit assertion, and a closed-form statement
  of when decoding fails).
- A second transcription from RFC 4648 (`src/independent.rs`) is proven equal
  to the encoder on every input, and to the decoder on "canonical" strings
  (padded, no whitespace, zero pad bits), which are proven to be exactly the
  encoder's output. The decoder's equivalence is therefore restricted to
  that class.
- Every mutation of the spec listed in `mutations.json` is certified as
  caught by a proof that Verus checks.
- Conformance: every row of WPT `fetch/data-urls/resources/base64.json`
  passes, and a differential test against the `base64` crate agrees.

Modelling choices (listed at the top of `src/spec.rs`): decode step 2 removes
two trailing `=` when there are two, which WPT requires (reading it as one
would make `ab==` fail); the standard's bit buffer is modelled as a number
and a bit count. No known gaps beyond the restriction above.

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
clazel-base64 = { path = "crates/clazel-base64" }
```

```rust
use clazel_base64::{decode::decode, encode::encode};

fn main() {
    // Strings are code points as `u32`.
    let text: Vec<u32> = encode(b"Hello, web");
    let text: String = text.iter().filter_map(|&c| char::from_u32(c)).collect();
    assert_eq!(text, "SGVsbG8sIHdlYg==");

    // Decoding is forgiving: ASCII whitespace is ignored and padding is optional.
    let input: Vec<u32> = " SGVs bG8s\nIHdlYg ".chars().map(|c| c as u32).collect();
    assert_eq!(decode(&input).as_deref(), Some(&b"Hello, web"[..]));

    // Failure is `None`.
    assert_eq!(decode(&['a' as u32]), None);
}
```

## Licence

MIT, as in the repository's [LICENSE](../../LICENSE). See the
[main README](../../README.md) for the project.
