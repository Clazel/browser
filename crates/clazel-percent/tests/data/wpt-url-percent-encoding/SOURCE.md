# WPT `url/percent-encoding.window.js`

Upstream: https://github.com/web-platform-tests/wpt/tree/d928657a0858e62b66a3724b3249e2b6e6c773a3/url
Commit: d928657a0858e62b66a3724b3249e2b6e6c773a3
License: BSD-3-Clause (`LICENSE.md`, copied from the root of the WPT repository)

Files, copied byte for byte from that commit:

| Here | Upstream |
|------|----------|
| `percent-encoding.json` | `url/resources/percent-encoding.json` (last changed in `efb889eb4c9ca0b4e3ebd8ab308646b7483a8f54`) |
| `percent-encoding.window.js` | `url/percent-encoding.window.js` |
| `percent-encoding.py` | `url/resources/percent-encoding.py` |
| `LICENSE.md` | `LICENSE.md` |

To update, copy the same files from a newer commit, change the commit above,
and run `cargo xtask testdata`.

`xtask/src/testdata/wpt_url_percent.rs` converts the JSON into
`tests/generated/wpt_url_percent_encoding.rs`, read by
`tests/conformance_percent.rs`: one case per (input, encoding) pair, named
as the test names it. The `.js` and `.py` files are vendored because they
say what the JSON means (the query of a special URL in that encoding, and the
fragment in UTF-8); the converter fails if the lines that say so change.

Every case's fragment check is run. Query checks for encodings other than
UTF-8 are expected failures, listed by name in `conformance_percent.rs`:
"percent-encode after encoding" is implemented for UTF-8 only, and the other
encoders arrive with HTML (docs/phases/phase-1.md).
