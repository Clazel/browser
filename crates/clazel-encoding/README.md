# clazel-encoding

UTF-8 decoding and encoding, formally verified with Verus. Part of
[Clazel](../../README.md), a web browser built from the bottom up by AI using
formal verification instead of trust.

## What it is

An implementation of the UTF-8 parts of the WHATWG Encoding Standard: the
UTF-8 decoder (section 8.1.1) and encoder (section 8.1.2), through the hooks
of section 6: "UTF-8 decode", "UTF-8 decode without BOM", "UTF-8 decode
without BOM or fail" and "UTF-8 encode". Decoders return Unicode scalar
values as `u32` (the type the other Clazel crates use for strings).

Not included: every other encoding (legacy encodings such as Shift_JIS and
windows-1252 arrive with HTML in a later phase), streaming and decoder state
across chunks, the `TextDecoder` API, and the encoder's "html" error mode
(UTF-8's encoder cannot return an error, so the mode is never read).

## Verification

Tier 2: the implementation is proven functionally correct against an
executable specification, with Verus. Verus also proves that it never
panics, overflows or indexes out of bounds. See the
[tiers](../../docs/VERIFICATION.md#tiers).

- `decode_without_bom`, `decode`, `decode_without_bom_or_fail` and `encode`
  are proven equal to a step-by-step transcription of the standard
  (`src/utf8/spec.rs`).
- Two independent transcriptions are proven equal to the spec on every
  input. The decoder's (`independent.rs`) is from the Unicode Standard
  chapter 3: Table 3-7, substitution of maximal subparts (section 3.9.6) and
  C10 for the fail variant. The encoder's (`independent_encode.rs`) is from
  Table 3-6. The one step Unicode does not define, what a decoder does with
  a BOM, is transcribed from Encoding section 6 again, so it is independent
  in transcription only.
- Decoding inverts encoding for both the replacing and the failing decoder.
- Every mutation listed in `mutations.json` is certified as caught by a proof
  that Verus checks.
- Conformance: WPT `encoding/` UTF-8 decode cases (and the encode cases,
  run as decode cases reversed), plus a differential test against
  `str::from_utf8_lossy`, `str::from_utf8` and `encoding_rs`: exhaustive for
  inputs of up to 3 bytes, boundary-byte combinations for 4 bytes, and
  random and corrupted longer inputs. Not exhaustive for 4 bytes or more.

Modelling choices (listed at the top of `src/utf8/spec.rs`): I/O queues are
a sequence plus a read position; "restore" is not advancing the position;
`encode` takes scalar values as `u32` and requires that they are scalar
values (no surrogates, none above U+10FFFF), so its proof covers only those
inputs. The standard's "peek" reads from index 1, which is read here as
index 0 (see [docs/ERRATA.md](../../docs/ERRATA.md); reported upstream).

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
clazel-encoding = { path = "crates/clazel-encoding" }
```

```rust
use clazel_encoding::utf8::{
    decode::{decode, decode_without_bom_or_fail},
    encode::encode,
};

fn main() {
    // Strips a leading BOM and replaces each error with U+FFFD.
    assert_eq!(decode(b"\xEF\xBB\xBFa\xFFb"), vec![0x61, 0xFFFD, 0x62]);

    // The fatal variant returns `None` on the first error.
    assert_eq!(decode_without_bom_or_fail(b"a\xFF"), None);

    // Encoding takes scalar values.
    assert_eq!(encode(&[0x61, 0xE9, 0x1F600]), "aé😀".as_bytes());
}
```

## Licence

MIT, as in the repository's [LICENSE](../../LICENSE). See the
[main README](../../README.md) for the project.
