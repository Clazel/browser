# Spec errata found while formalizing

Places where a web standard, read literally, says something other than what
it evidently means. Each entry records what we specified instead.

## Encoding §3 "peek" reads from index 1, not 0

- **Spec:** Encoding Standard, Living Standard last updated 19 October 2026
  (commit `dd7943441a861a60a073bffa55869d91cb6a8288`),
  <https://encoding.spec.whatwg.org/#i-o-queue-peek>
- **Text:** "For each n in the range 1 to number, inclusive: If ioQueue[n] is
  end-of-queue, break. Otherwise, append ioQueue[n] to prefix."
- **Problem:** Infra lists are zero-based ("a zero-based index into a list").
  Read literally, peeking 3 items returns `ioQueue[1..=3]` and skips the
  first item. "UTF-8 decode" step 2 would then test bytes 1–3 for the BOM
  instead of bytes 0–2.
- **We specify:** the first `number` items (`ioQueue[0..number]`). See
  `starts_with_bom` in `crates/clazel-encoding/src/utf8/spec.rs`.
- **Reported upstream:** [whatwg/encoding#367](https://github.com/whatwg/encoding/issues/367),
  19 October 2026.

## Fetch "collect an HTTP quoted string" step 7 takes one code point too many

- **Spec:** Fetch Standard, Living Standard last updated 19 October 2026
  (commit `59afe349913d56898c947576216f1c2579308be7`),
  <https://fetch.spec.whatwg.org/#collect-an-http-quoted-string>
- **Text:** "Return the code points from positionStart to position,
  inclusive, within input."
- **Problem:** after the loop, position points just past the closing
  U+0022 ("), or past the end of input. Read literally, "inclusive" adds the
  code point after the closing quote (or one that does not exist). The
  standard's own example table contradicts that: input `"Hello" World`
  gives `"Hello"` with final position 7, and input `"\` gives `"\` with
  final position 2, past the end of the two-code-point input.
- **We specify:** the code points from positionStart up to, but not
  including, position. See `collect_an_http_quoted_string` in
  `crates/clazel-mime/src/mime_type/spec.rs`. (Parse a MIME type only calls
  it with extract-value true, which does not reach this step.)
- **Reported upstream:** not yet.
