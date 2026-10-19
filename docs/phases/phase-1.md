# Phase 1: Verified primitives, detailed plan

**Goal:** the byte-level parsers every later phase stands on, each at Tier 2:
UTF-8, percent-encoding, base64, MIME types and sniffing, and the WHATWG URL
parser. They are small enough to prove completely, and the URL parser is the
first large state machine, so this phase is where the Phase 0 machinery meets
real volume.

## Exit criteria

Phase 1 is done when all of these hold on macOS arm64 and Linux x86-64:

1. Every crate below is at **tier 2**, accepted by `cargo xtask check` (so
   every mutation is a certified `killed`, and each crate has conformance
   tests and a proven-equivalent independent transcription).
2. The WPT `url/` data files (`urltestdata.json`, `setters_tests.json`,
   `toascii.json`, `IdnaTestV2.json`, `percent-encoding.json`) pass through
   the proven implementation, vendored at a pinned upstream commit. Any
   expected failure is listed by name with its reason, and counted in the
   README table.
3. `scripts/verify.sh` exits 0, with the README table showing WPT pass rates.

## Crates

| Crate | Standard | Contents |
|-------|----------|----------|
| `clazel-encoding` | Encoding §8.1, §6 | UTF-8 decode (3 hooks) and encode |
| `clazel-percent` | URL §1.3 | percent-encode/decode, the encode sets |
| `clazel-base64` | Infra §4.x forgiving-base64 | decode and encode |
| `clazel-mime` | MIME Sniffing §4, §7 | parse/serialize a MIME type; sniffing |
| `clazel-idna` | UTS #46, RFC 3492 | punycode, domain to ASCII / to Unicode |
| `clazel-url` | URL §3, §4 | host parser, basic URL parser, serializers, setters |

Each is `tier = 0, target-tier = 2` until it earns more. Legacy encodings
(Shift_JIS, windows-1252, …) are **not** in this phase: the URL parser's
query encoding is modelled as UTF-8 only, and that is listed as a modelling
choice in its spec header. They arrive with HTML in Phase 4.

## Work items

Ordered by dependency. Size: S is under a day, M a few days, L a week or more.
Each item follows CLAUDE.md rule 3: spec and contracts in one commit, then the
implementation and proof.

### 1.0 Test-data plumbing (S)

Conformance tests read vendored JSON, but browser crates may not depend on
a JSON parser (rule 8). So `cargo xtask testdata` converts each vendored
file under `tests/data/` into a Rust source file of plain tables
(`tests/generated/*.rs`), committed, and `verify` fails if a generated file
differs from what the converter produces. Each vendored suite gets a
`SOURCE.md`: upstream URL, commit, license.

Differential tests against other engines need those engines as
dev-dependencies (`encoding_rs`, used by Firefox). Dev-only packages never
ship, so they get a fourth allowlist class, `test`: reachable from browser
crates only through `[dev-dependencies]`. `deps.rs` must check the edge kind.

### 1.1 UTF-8 decoder: implementation and proof (M)

**As built:** the contract promised `Vec<char>`, but no safe `u32` to `char`
conversion has a vstd specification, and providing one needs
`assume_specification`, which expands to `unsafe` code (rules 1 and 4). The
contract now outputs scalar values as `u32` (`lemma_hooks_scalar` proves
they all are), committed on its own before the implementation. Four
mutations that used to survive now break the refinement proof; they are
`killed-incidentally` until 1.2 certifies them.

Contracts are already committed (`utf8/contract.rs`). Write
`decode`, `decode_without_bom` and `decode_without_bom_or_fail` as one loop
over `&[u8]` that mirrors `process_queue`, with the loop invariant "the
output so far, followed by `process_queue` from the current state, equals
the spec's result". This proves panic-freedom too (Verus checks overflow and
bounds). Miri runs the unit tests.

### 1.2 UTF-8: independent transcription (M)

`utf8/independent.rs`: Unicode Standard, Chapter 3, Table 3-7 (well-formed
byte sequences) and §3.9 "U+FFFD substitution of maximal subparts", written
without reading `spec.rs`, and a lemma that it equals `utf8_decode_without_bom`
for every input. This is what kills the mutations that survive today
(overlong forms, dropped restore, dropped U+FFFD, the ASCII range, BOM):
each gets a certificate that evaluates both on a concrete input.

### 1.3 UTF-8: conformance (S)

`tests/conformance_utf8.rs`: WPT `encoding/` UTF-8 decode cases, and a
differential test against `String::from_utf8_lossy` and `encoding_rs` over
exhaustive inputs up to 4 bytes plus random longer inputs.

### 1.4 UTF-8 encode (S)

Encoding §8.1.2 encoder handler and "UTF-8 encode", same pattern: spec,
contract, implementation, independent transcription (Unicode §3.9 D92),
mutations, round-trip lemma (`decode(encode(s)) == s` for scalar values).
After 1.1–1.4: **raise `clazel-encoding` to tier 2.**

### 1.5 Percent-encoding (M)

URL §1.3: percent-encode, percent-decode (bytes and string), the five
encode sets, "percent-encode after encoding" with UTF-8, and "UTF-8 percent
encode". Independent: RFC 3986 §2.1 for decode. Conformance: WPT
`percent-encoding.json` (UTF-8 rows only; others are expected failures
until legacy encodings exist). Lemma: decode inverts encode.

### 1.6 Forgiving base64 (S)

Infra "forgiving-base64 decode" and "forgiving-base64 encode".
Independent: RFC 4648 §4. Conformance: WPT `fetch/data-urls/base64.any.js`
table (vendored as data). Lemma: decode inverts encode.

### 1.7 MIME types (M)

MIME Sniffing §4.4 parse a MIME type, §4.5 serialize, and §4.6 the
predicates the URL and fetch layers need. Conformance: WPT
`mimesniff/mime-types/resources/*.json`. Then §7 "determine the computed
MIME type" with the pattern-matching algorithm (§4.x pattern tables are
data; the matcher is proven against its spec). Independent: RFC 9110 §8.3.1
grammar for the parse step.

### 1.8 IDNA (L)

Needed by the host parser ("domain to ASCII"). RFC 3492 punycode first
(small, exact arithmetic, overflow handling is the risk). Then UTS #46
processing with the mapping and validity tables generated by `xtask` from
vendored Unicode data files (pinned version, checksummed), plus Bidi and
CONTEXTJ rules. Proof scope: the algorithm is proven against its spec
*relative to the tables*; the tables themselves are checked by regenerating
them in `verify`. Conformance: WPT `IdnaTestV2.json` and `toascii.json`.
Risk: Verus performance on large constant tables. Fallback: a table-lookup
function with a proven contract over a sorted range array.

### 1.9 Host parsing (M)

URL §3.5: host parser, IPv4 parser (with its number parser), IPv6 parser,
opaque-host parser, and §3.6 host serializers. Independent: RFC 3986 §3.2.2
and RFC 4291 §2.2 for IPv6 text forms. Lemma: serialize then parse is the
identity on hosts.

### 1.10 Basic URL parser (L)

URL §4.4, the state machine, transcribed one state per spec function with
the standard's state names, plus the URL record (§4.1) and serializer
(§4.5). This is the largest spec in the phase; split commits by state
group (scheme, authority, path, query/fragment). Lemmas: the parser is
total; serialize-then-parse is idempotent (the standard asserts this in
§4.5). Independent: RFC 3986 Appendix B / §5.2 resolution, proven
equivalent on the input class where the two standards agree (stated
precisely; the WHATWG parser intentionally differs elsewhere).
Conformance: `urltestdata.json`.

### 1.11 URL API setters (M)

URL §6.1 setters reuse the parser with a state override. Conformance:
`setters_tests.json`. **Exit criterion 2 is met here.**

### 1.12 WPT pass rates in the README table (S)

Phase 0 deferred this column. Each conformance test reports pass / total
per suite; `xtask report` adds a "Conformance" column.

## Order of work

```
1.0 test plumbing ──┬─> 1.3 UTF-8 conformance
1.1 UTF-8 impl ─────┼─> 1.2 independent ─> 1.4 encode ─> encoding at tier 2
                    ├─> 1.5 percent ─┐
                    ├─> 1.6 base64   ├─> 1.9 hosts ─> 1.10 URL parser ─> 1.11 setters
                    ├─> 1.7 MIME     │
                    └─> 1.8 IDNA ────┘
1.12 README column (after 1.3)
```

## Status

| Item | State |
|------|-------|
| 1.0 Test-data plumbing | not started |
| 1.1 UTF-8 decoder implementation and proof | done: 25 verified, 0 errors; contract changed to `u32` output (below) |
| 1.2–1.12 | not started |

## Risks

- **Verus at scale.** The URL state machine has ~20 states and a mutable
  record. If one monolithic `process_queue`-style recursion is too slow to
  verify, split it into one proven step function per state.
- **Independence.** Two AI transcriptions can share a misreading
  (VERIFICATION.md). That is why every independent transcription here comes
  from a *different* standard (Unicode, RFCs) where one exists.
- **WHATWG vs RFC differences.** Equivalence with an RFC only holds on
  part of the input space. The lemma must state that part exactly; a
  vague restriction would make it meaningless.
