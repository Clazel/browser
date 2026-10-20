# WPT `url/` IDNA tests: IdnaTestV2.json and toascii.json

Upstream: https://github.com/web-platform-tests/wpt/tree/10dd48f8bc0c18d6b695c83dfa230880385dbf79/url
Commit: 10dd48f8bc0c18d6b695c83dfa230880385dbf79
License: BSD-3-Clause (`LICENSE.md`, copied from the root of the WPT repository)

Copied byte for byte at that commit: `url/resources/IdnaTestV2.json` and
`url/resources/toascii.json` (the data), and `url/IdnaTestV2.any.js` and
`url/toascii.window.js` (the tests that run them, which the converter
checks still run the data the way the table assumes). IdnaTestV2.json was
last regenerated for Unicode 18.0.0 (WPT `13748c36`), the version of
`data/unicode-18.0.0/`. To update, copy the files from a newer commit,
change the commit above, and run `cargo xtask testdata`.

`xtask/src/testdata/wpt_idna.rs` converts them into
`tests/generated/wpt_url_idna.rs`, read by `tests/conformance_uts46.rs`.

How the rows map onto the domain parser: both tests parse
`https://<input>/x` and compare the URL's host with the output, or expect
failure for `null`. The converter feeds the input to the URL Standard's
"domain parser" with beStrict false directly, which is what the host
parser does for a special URL once it has percent-decoded the host, and
refuses any row where the URL layer could change the result (tab or
newline, `/ ? # \ @ : [`, a percent-encoded byte, or a host ending in a
number); no current row is refused. Lone surrogates in the JSON (two rows)
become U+FFFD, as `new URL()`'s USVString conversion does.

Not converted: the one IdnaTestV2.json row with empty input, which the
test itself skips ("cannot test empty string input through new URL()").
toascii.window.js also runs each row through `<a>`, `<area>` and the
`host`/`hostname` setters; those add the URL setters (item 1.11), so only
the `new URL()` expectation is used.
