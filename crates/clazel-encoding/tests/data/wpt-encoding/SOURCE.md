# WPT `encoding/`, UTF-8 decode cases

Upstream: https://github.com/web-platform-tests/wpt/tree/4ad507b28db0a636f528def9161d109fe11b93a3/encoding
Commit: 4ad507b28db0a636f528def9161d109fe11b93a3
License: BSD-3-Clause (`LICENSE.md`, copied from the root of the WPT repository)

The `.js` files are copied byte for byte from `encoding/` at that commit;
`LICENSE.md` from the repository root. To update, copy the same files from a
newer commit, change the commit above, and run `cargo xtask testdata`.

`xtask/src/testdata/wpt_encoding.rs` converts them into
`tests/generated/wpt_encoding.rs`, read by `tests/conformance_utf8.rs`. It
reads only literals in fixed places and fails if one moves, so an update
that reshapes a file cannot silently drop cases.

What is converted:

| File | Cases |
|------|-------|
| `textdecoder-fatal.any.js` | `bad` (UTF-8 rows): fatal decode must fail |
| `textdecoder-fatal-streaming.any.js` | "non-streaming cases" (UTF-8 row): fatal fails, replacement gives U+FFFD |
| `textdecoder-mistakes.any.js` | `invalid8`: replacement decode |
| `textdecoder-byte-order-marks.any.js` | UTF-8 row, with and without its BOM |
| `textdecoder-ignorebom.any.js` | UTF-8 row, with `ignoreBOM` true and by default |
| `api-basics.any.js` | "Encode/decode round trip: utf-8", decode half |
| `api-surrogates-utf8.any.js` | `badStrings`: the `expected` bytes decode to `decoded` |
| every file above | one-line `assert_equals(new TextDecoder().decode(<literal bytes>), <string literal>)` with no label or the `utf-8` label (`textdecoder-eof.any.js` has these) |

Not converted, and why:

- Streaming (`{stream: true}`) and decoder reuse (sticky BOM and fatal
  state in `textdecoder-mistakes.any.js`, `textdecoder-eof.any.js`'s second
  test, `textdecoder-streaming.any.js`): these test the `TextDecoder` API's
  state across calls. The crate implements the Encoding Standard's
  whole-input hooks, which have no streaming state.
- "Mismatching BOM should not be ignored" in
  `textdecoder-byte-order-marks.any.js`: asserts only inequality, which the
  differential test in `conformance_utf8.rs` covers more strongly.
- Other encodings (UTF-16, legacy), the encoder (`TextEncoder`,
  `encodeInto`), labels and IDL: not UTF-8 decode. The encoder's cases
  belong to item 1.4.
- `eof-utf-8-*.html`, `bom-handling.html`, `resources/two-boms-utf-8.html`:
  reftests and documents that need an HTML engine.
