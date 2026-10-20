# WPT `mimesniff/media/` and `mimesniff/sniffing/`, resource sniffing

Upstream: https://github.com/web-platform-tests/wpt/tree/d928657a0858e62b66a3724b3249e2b6e6c773a3/mimesniff
Commit: d928657a0858e62b66a3724b3249e2b6e6c773a3
License: BSD-3-Clause (`LICENSE.md`, copied from the root of the WPT repository)

Copied byte for byte from that commit (the directory is flat here; no two
names collide):

- from `mimesniff/media/`: `media-sniff.window.js`;
- from `mimesniff/media/resources/`: `flac.flac`, `mp3-raw.mp3`,
  `mp3-with-id3.mp3`, `mp4.mp4`, `ogg.ogg`, `wav.wav`, `webm.webm`;
- from `mimesniff/sniffing/`: `mislabeled-binary-resource.tentative.window.js`,
  `html.window.js`;
- from `mimesniff/sniffing/resources/`: `binary-data.bin`,
  `html-content.html`, `png-image.png` and their `.headers` files;
- from `mimesniff/sniffing/support/`: `atom.html`, `rss.html`;
- `LICENSE.md` from the repository root.

To update, copy the same files from a newer commit, change the commit
above, and run `cargo xtask testdata`.

These tests run in a browser, so they hold no expected-output tables.
`xtask/src/testdata/wpt_mimesniff.rs` converts the resources, with the
Content-Type each test serves them with, into
`tests/generated/wpt_mimesniff.rs`; `tests/conformance_sniffing.rs` says,
per WPT test, what it asserts and checks that through the exec code:

- `media-sniff.window.js`: every vector must play with every listed
  Content-Type. The standard's part of that is §6.2 (the audio or video
  type pattern matching algorithm, which §8.6 runs whatever the
  Content-Type): it must recognise each vector as its format, and with no
  Content-Type, §7 must too. `flac.flac` is the exception: the standard
  has no FLAC signature, so §6.2 returns undefined for it. That is a gap in
  the standard, not in this crate, and the test records it.
- `mislabeled-binary-resource.tentative.window.js`: resources served as
  `text/plain` (so the check-for-apache-bug flag is set, §5.1) must come
  out as `text/plain` or `application/octet-stream`, never HTML or an
  image: binary data and the PNG as `application/octet-stream`, the HTML
  as `text/plain`.
- `html.window.js`: `atom.html` and `rss.html`, served as `text/html`, stay
  `text/html` (§7 step 1).

Not converted, and why:

- `test-file.zip` (in `mislabeled-binary-resource.tentative.window.js`): it
  is served with `Content-Encoding: gzip`, so the browser sniffs the
  decoded body; this crate has no gzip decoder (CLAUDE.md rule 8).
- `html-comment.tentative.window.js` and `support/html-comment`: a
  tentative test expecting `<!--` followed by a non-space byte to be sniffed
  as HTML. At the pinned standard, the `<!--` row requires a
  tag-terminating byte after it, so §7.1 gives `text/plain`. It tests a
  proposed change, not the standard.
- `media/resources/make-vectors.sh`: the script that made the vectors.
- `mimesniff/mime-types/`: vendored separately in `tests/data/wpt-mime-types/`.
