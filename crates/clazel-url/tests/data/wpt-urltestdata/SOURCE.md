# WPT `url/`: every row of `urltestdata.json`

Upstream: https://github.com/web-platform-tests/wpt/tree/d928657a0858e62b66a3724b3249e2b6e6c773a3/url
Commit: d928657a0858e62b66a3724b3249e2b6e6c773a3
License: BSD-3-Clause (`LICENSE.md`, copied from the root of the WPT repository)

Files, copied byte for byte from that commit (the same commit as
`../wpt-url-hosts/`):

| Here | Upstream |
|------|----------|
| `urltestdata.json` | `url/resources/urltestdata.json` |
| `url-constructor.any.js` | `url/url-constructor.any.js` |
| `LICENSE.md` | `LICENSE.md` |

To update, copy the same files from a newer commit, change the commit above,
and run `cargo xtask testdata`.

`xtask/src/testdata/wpt_urltestdata.rs` converts the JSON into
`tests/generated/wpt_urltestdata.rs`, read by `tests/conformance_url.rs`.
`url-constructor.any.js` is vendored because it says what a row means:
`new URL(input, base)` (so base is parsed first, and a base that fails to
parse makes the row a failure), then `href`, `protocol`, `username`,
`password`, `host`, `hostname`, `port`, `pathname`, `search` and `hash`
are compared; the converter fails if the lines that say so change.

**Converted:** every row (896), all of them run through the proven basic
URL parser and serializer. The ten getters are URL API (§6.1) one-liners
over the URL record, computed by the test.

**Not compared:** the `searchParams` field of the 9 rows that have one
(`URLSearchParams` serialization, application/x-www-form-urlencoded,
which is not part of the URL parser); `origin` (§4.7, not transcribed).
The rows are still run and every other field is compared.

`urltestdata-javascript-only.json`, which `url-constructor.any.js` also
loads, is not vendored: its rows test JavaScript string handling (lone
surrogates) before the parser runs, and the parser takes scalar values.
