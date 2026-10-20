# WPT `mimesniff/mime-types/`, MIME type parsing cases

Upstream: https://github.com/web-platform-tests/wpt/tree/d928657a0858e62b66a3724b3249e2b6e6c773a3/mimesniff/mime-types
Commit: d928657a0858e62b66a3724b3249e2b6e6c773a3
License: BSD-3-Clause (`LICENSE.md`, copied from the root of the WPT repository)

`mime-types.json` and `generated-mime-types.json` are copied byte for byte
from `mimesniff/mime-types/resources/` at that commit; `LICENSE.md` from
the repository root. (`generated-mime-types.json` is the output of
`generated-mime-types.py` in the same directory, committed upstream.) To
update, copy the same files from a newer commit, change the commit above,
and run `cargo xtask testdata`.

`xtask/src/testdata/wpt_mime_types.rs` converts them into
`tests/generated/wpt_mime_types.rs`, read by
`tests/conformance_mime_types.rs`: every case's `input` must parse (MIME
Sniffing §4.4) and serialize (§4.5) to its `output`, or fail when `output`
is `null`. WPT's `parsing.any.js` runs the same pairs through `Blob`,
`File`, `Request` and `Response`.

Not converted, and why:

- `navigable`, `encoding` and `minimizedMIMEType` in `mime-types.json`:
  they test HTML navigation, the Encoding Standard's label lookup, and
  "minimize a supported MIME type", none of which this crate implements.
- `parsing.any.js` and `charset-parameter.window.js`: test harness code
  and a test of HTML's charset handling, not data.
- `mimesniff/sniffing/` and the other directories: resource sniffing
  (MIME Sniffing §7), which this crate does not implement yet.
