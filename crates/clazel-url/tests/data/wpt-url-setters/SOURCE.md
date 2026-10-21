# WPT `url/`: every case of `setters_tests.json`

Upstream: https://github.com/web-platform-tests/wpt/tree/d928657a0858e62b66a3724b3249e2b6e6c773a3/url
Commit: d928657a0858e62b66a3724b3249e2b6e6c773a3
License: BSD-3-Clause (`LICENSE.md`, copied from the root of the WPT repository)

Files, copied byte for byte from that commit (the same commit as
`../wpt-urltestdata/` and `../wpt-url-hosts/`):

| Here | Upstream |
|------|----------|
| `setters_tests.json` | `url/resources/setters_tests.json` |
| `url-setters.any.js` | `url/url-setters.any.js` |
| `LICENSE.md` | `LICENSE.md` |

To update, copy the same files from a newer commit, change the commit above,
and run `cargo xtask testdata`.

`xtask/src/testdata/wpt_url_setters.rs` converts the JSON into
`tests/generated/wpt_url_setters.rs`, read by `tests/conformance_setters.rs`.
`url-setters.any.js` is vendored because it says what a case means:
`new URL(href)`, then `url[setter] = new_value`, then each getter named
in `expected` compared with its value; the converter fails if the lines
that say so change. The cases are ordered by setter name, then as in the
file.

**Converted:** every case (278), all of them run through the proven
basic URL parser (for `new URL(href)`) and the proven setters. The
getters are URL API (§6.1) one-liners over the URL record, computed by
the test.

`url-setters-a-area.window.js` and `url-setters-stripping.any.js`, which
run the same or similar cases through `<a>`/`<area>` elements and
stripping rules of the HTML Standard, are not vendored.
