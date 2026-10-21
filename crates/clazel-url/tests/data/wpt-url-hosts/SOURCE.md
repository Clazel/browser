# WPT `url/`: host parsing rows of `urltestdata.json` and `toascii.json`

Upstream: https://github.com/web-platform-tests/wpt/tree/d928657a0858e62b66a3724b3249e2b6e6c773a3/url
Commit: d928657a0858e62b66a3724b3249e2b6e6c773a3
License: BSD-3-Clause (`LICENSE.md`, copied from the root of the WPT repository)

Files, copied byte for byte from that commit:

| Here | Upstream |
|------|----------|
| `urltestdata.json` | `url/resources/urltestdata.json` |
| `url-constructor.any.js` | `url/url-constructor.any.js` |
| `toascii.json` | `url/resources/toascii.json` |
| `toascii.window.js` | `url/toascii.window.js` |
| `LICENSE.md` | `LICENSE.md` |

To update, copy the same files from a newer commit, change the commit above,
and run `cargo xtask testdata`.

`xtask/src/testdata/wpt_url_hosts.rs` converts the JSON into
`tests/generated/wpt_url_hosts.rs`, read by `tests/conformance_hosts.rs`.
The `.js` files are vendored because they say what the JSON means (a URL's
`hostname` is its serialized host; a `toascii.json` input is the host of
`https://<input>/x`); the converter fails if the lines that say so change.

**Not converted yet:** rows where something other than the host parser
decides the outcome, because the URL parser that would run them is item
1.10. The converter keeps a `urltestdata.json` row only when its input is
an absolute `scheme://authority...` URL (lowercase scheme, not `file`) with
no credentials, no port, no tab or newline and no leading or trailing C0
control or space, and, for a special scheme, a non-empty authority; and a
`toascii.json` row only when the input contains none of `/ ? # \ @` and no
port. The generated file's header gives the counts. The rest arrive with
item 1.10.

**Expected failures:** none. Rows whose domain (host parser step 5) is not
ASCII go through `clazel-idna`'s domain parser (UTS #46 ToASCII, URL §3.3)
via `host_parser_full`.
