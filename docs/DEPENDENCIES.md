# Dependencies

Every third-party package in the resolved dependency graph (`Cargo.lock`)
needs a row in the allowlist below (see CLAUDE.md rule 8). `cargo xtask check`
enforces it:

1. Every resolved third-party package has a row with its **exact** version,
   and comes from crates.io. Git and path dependencies outside the workspace
   are rejected.
2. Every row is used. Stale rows fail, so the table never lists more than
   is really there.
3. The class matches how the package is reached:
   - `shipped`: may be reached directly from browser crates (every
     workspace crate except tooling). Allowed only for crypto (verified
     libraries), OS and windowing bindings, and GPU access.
   - `proof`: reached from browser crates only through `vstd`. This is
     Verus's proof library and its macro chain; ghost code is erased from
     normal builds.
   - `test`: reached from browser crates only through their
     `[dev-dependencies]`, so it is compiled into test binaries and never
     into the browser. Used for differential testing against other engines.
     The checker follows the edge kind in `cargo metadata`: a package that a
     browser crate also reaches through `[dependencies]` or
     `[build-dependencies]` fails, whatever its row says.
   - `tooling`: must be unreachable from browser crates. Used by `xtask`,
     which never ships.

A package used in more than one way takes the strictest class that covers
all of them, in the order `shipped`, `proof`, `test`, `tooling` (e.g. one
used by both proof and tooling code is `proof`).

Dev-dependencies of browser crates are pinned to an exact version
(`=x.y.z`) like everything else.

Changing a row is a reviewable act. Adding one means saying why below.

<!-- BEGIN ALLOWLIST: checked by `cargo xtask check` -->
| Package | Version | Class | Why |
|---------|---------|-------|-----|
| vstd | 0.0.0-2026-10-04-0306 | proof | Verus standard library (`Seq`, `spec fn`s). Pinned to the installed Verus release. |
| verus_builtin | 0.0.0-2026-09-16-0054 | proof | Verus built-in items, required by `vstd`. |
| verus_builtin_macros | 0.0.0-2026-09-20-0158 | proof | The `verus!` macro (proc-macro). |
| verus_state_machines_macros | 0.0.0-2026-09-06-0133 | proof | Verus state-machine macros (proc-macro), required by `vstd`. |
| verus_syn | 0.0.0-2026-09-06-0133 | proof | Verus's fork of `syn`, used by its macros. |
| verus_prettyplease | 0.0.0-2026-09-06-0133 | proof | Verus macro output formatting. |
| syn | 2.0.119 | proof | Rust parser, used by Verus's macros. |
| synstructure | 0.13.2 | proof | Derive helper, used by Verus's macros. |
| convert_case | 0.4.0 | proof | Identifier case conversion, used by Verus's macros. |
| indexmap | 2.14.2 | proof | Ordered map, used by Verus's macros. |
| hashbrown | 0.17.1 | proof | Hash table, used by `indexmap`. |
| equivalent | 1.0.3 | proof | Key comparison trait, used by `indexmap`. |
| proc-macro2 | 1.0.107 | proof | Token streams for Verus's macros. Also used by `xtask` (with `span-locations`) to lex source files. |
| quote | 1.0.47 | proof | Token generation for Verus's macros. Also locked under `serde_derive` (tooling). |
| unicode-ident | 1.0.27 | proof | Identifier rules for `proc-macro2`. |
| encoding_rs | 0.8.35 | test | Firefox's Encoding Standard implementation: the reference engine in `clazel-encoding`'s differential test (`tests/conformance_utf8.rs`). Pinned to 0.8.35, whose only dependency is `cfg-if`; later releases add five more. |
| base64 | 0.22.1 | test | RFC 4648 base64 implementation (rust-base64): the reference engine in `clazel-base64`'s differential test (`tests/conformance_base64.rs`). No dependencies. |
| mime | 0.3.17 | test | hyperium's media type parser (used by `hyper` and `reqwest`): the reference engine in `clazel-mime`'s differential test (`tests/conformance_mime_types.rs`). No dependencies. |
| infer | 0.19.0 | test | A file-type detector by magic numbers (bojand/infer), written without the WHATWG standard: the reference in `clazel-mime`'s sniffing differential test (`tests/conformance_sniffing.rs`). Used without default features, so it has no dependencies (`cfb` is optional). |
| cfg-if | 1.0.5 | test | `#[cfg]` helper macro, required by `encoding_rs`. |
| percent-encoding | 2.3.2 | test | rust-url's percent-encoding (used by the `url` crate and Servo): a reference engine in `clazel-percent`'s differential test (`tests/conformance_percent.rs`). No dependencies. |
| form_urlencoded | 1.2.2 | test | rust-url's `application/x-www-form-urlencoded` serializer: the reference for that percent-encode set in the same test. Its only dependency is `percent-encoding`. |
| url | 2.5.8 | test | rust-url, the WHATWG URL parser used by Servo: the reference engine in `clazel-url`'s differential test (`tests/conformance_url.rs`). Used without default features, so its `std` feature (which names `serde` as a weak dependency) is off; its dependencies (`form_urlencoded`, `idna`, `percent-encoding`) are already listed. |
| idna | 1.1.0 | test | rust-url's IDNA implementation (used by the `url` crate, Servo and Firefox): the reference engine in `clazel-idna`'s Punycode and UTS #46 differential tests (`tests/conformance_punycode.rs`, `tests/conformance_uts46.rs`). |
| idna_adapter | 1.1.0 | test | `idna`'s Unicode back end, pinned to 1.1.0, the unicode-rs one (the 1.2 releases pull in ICU4X, about twenty crates). |
| idna_mapping | 1.1.0 | test | UTS #46 mapping data for `idna_adapter` 1.1.0. |
| unicode-joining-type | 1.0.0 | test | Joining_Type data, required by `idna_mapping`. No dependencies. |
| unicode-bidi | 0.3.18 | test | Bidi_Class data, required by `idna_adapter` 1.1.0. |
| unicode-normalization | 0.1.26 | test | NFC, required by `idna_adapter` 1.1.0. |
| tinyvec | 1.13.3 | test | Small-vector type, required by `unicode-normalization`. |
| smallvec | 1.16.3 | test | Small-vector type, required by `idna`. No dependencies. |
| utf8_iter | 1.0.4 | test | UTF-8 iteration, required by `idna`. No dependencies. |
| minicbor | 2.3.1 | test | A small CBOR codec (no_std): the reference engine in `clazel-ipc`'s differential test (`tests/conformance_cbor.rs`). Chosen over `ciborium` (which pulls `serde`, `half` and two more). Used without default features (only `alloc`), so it has no dependencies. It accepts non-shortest arguments, which the test accounts for. |
| serde_json | 1.0.154 | tooling | `xtask` parses `cargo metadata` output. |
| serde_core | 1.0.229 | tooling | Required by `serde_json`. |
| itoa | 1.0.18 | tooling | Integer formatting, required by `serde_json`. |
| memchr | 2.8.3 | tooling | Byte search, required by `serde_json`. |
| zmij | 1.0.23 | tooling | Float formatting, required by `serde_json`. |
| serde | 1.0.229 | tooling | Locked but never compiled: `serde_json` names it under the always-false `cfg(any())` to pin versions. |
| serde_derive | 1.0.229 | tooling | Locked but never compiled: `serde_core` names it under `cfg(any())`. |
| syn | 3.0.9 | tooling | Locked but never compiled: dependency of `serde_derive`. |
<!-- END ALLOWLIST -->

There are no `shipped` packages yet: everything that runs in the browser is
our own code. The `test` packages are compiled only into test binaries.
