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
