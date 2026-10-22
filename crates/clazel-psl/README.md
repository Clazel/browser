# clazel-psl

The Public Suffix List for the Clazel browser: "public suffix" and
"registrable domain" of a host, and the cookie root. Part of
[Clazel](../../README.md), a web browser whose parsers of untrusted input
carry machine-checked proofs.

## What it is

- **Public suffix and registrable domain:** URL Standard §3.2 ("obtain the
  public suffix of a host", "obtain the registrable domain of a host"), which
  call the algorithm in the "Formal algorithm" section of the Public Suffix
  List's "Format" page (publicsuffix.org). Plain, wildcard and exception
  rules; the default rule `*`; a trailing dot is kept. A domain with an empty
  label has no public suffix (the algorithm does not define it; this is a
  modelling choice).
- **Cookie root:** our own definition, because no standard names it: the
  shortest suffix of a domain, in labels, that is not a public suffix, or the
  domain itself if every suffix is one; for an IP address, the address. Two
  hosts can share a cookie exactly when they have the same cookie root, which
  is why it, and not the registrable domain, is the cookie isolation
  boundary (a cookie set for `amazonaws.com` reaches
  `bucket.s3.us-east-2.amazonaws.com`, whose registrable domain is itself
  because `s3.us-east-2.amazonaws.com` is a rule). See
  [`clazel-cookie`](../clazel-cookie/README.md).
- **The list:** `public_suffix_list.dat` from `publicsuffix/list` at commit
  `5dd321ff` (20 October 2026), with the ICANN and private sections both
  used and not distinguished, as browsers treat them alike for cookies. The
  file, the list's own `tests.txt` and its licence are vendored byte for byte
  under `data/publicsuffix-5dd321ff/`; `SOURCE.md` there gives the SHA-256 of
  each, and `cargo xtask check` fails if one differs.

Out of scope: fetching or updating the list at run time, and parsing host
strings (that is `clazel-url`; this crate takes a host record or a canonical
domain as code points).

## Regenerating the tables

`src/data.rs` is generated from the vendored list by `cargo xtask tables`
(`xtask/src/psl.rs`), which rejects a list the proofs would not cover
(empty labels, a misplaced `*`, upper case, duplicates, or two exception
rules that could match one domain). `cargo xtask check` fails if the
committed file is stale. To move to a newer list, vendor the three files and
a `SOURCE.md` with their SHA-256 under a new `data/publicsuffix-<commit>/`,
point `DATA_DIR` in `xtask/src/psl.rs` and the `include_str!` paths in
`tests/` at it, and run `cargo xtask tables`. The proofs are relative to the
tables, so run the full verification afterwards; do not assume it still passes.

## Verification

Tier 2: the executable code is proven, in Verus, to equal an executable
specification of the standard, here for the list the tables hold. Current
numbers are in the [status table](../../README.md#verification-status).

- **Proven:** the executable lookups equal the spec (`spec.rs`, which
  transcribes the algorithm over any list of rules). The scan checks every
  rule rather than bisecting, because Verus cannot see that the tables are
  sorted and the spec is "match against all rules". Lemmas include
  `lemma_root_of_suffix`: for a domain and a suffix of it that is not a public
  suffix, the cookie root is the same, which the cookie isolation lemmas
  use.
- **Independent transcription:** `independent.rs` is the "Formal algorithm"
  transcribed by a separate session that had not read `spec.rs`, and is
  proven equal to it for every domain and every list with `rules_wf`
  (`equivalence_proof.rs`); `wf_table.rs` proves `rules_wf` for the generated
  tables, so nothing about them is assumed. The transcriber's fetch of the
  wiki page returned a paraphrase, so the quoted steps there are its
  wording, not the page's.
- **Mutations:** every deliberately broken spec is rejected by a checked
  certificate (`mutations.json`).
- **Conformance:** the list's own `checkPublicSuffix` cases (`tests.txt`,
  inputs canonicalised by the proven host parser), and a differential
  against the `publicsuffix` crate (2.3.0) loaded with the same list, over
  every ASCII rule and labels above it. Rules with non-ASCII labels are
  stored as A-labels, so the differential covers the ASCII rules only.
- **Modelling choices** (listed at the top of `src/spec.rs`): the prevailing
  rule is chosen in one pass over the rules in list order, with ties going to
  the earlier rule, which the generator makes irrelevant for the real list;
  empty labels give null; the trailing dot is set aside and restored.

## Trust

The proofs assume the Rust compiler, Verus and its solver, and that the specs
transcribe the standards correctly. The generator in `xtask` that turns the
list into tables is part of the trusted base too, though a stale or
malformed table is caught by the checks above. The full list is in
[docs/VERIFICATION.md](../../docs/VERIFICATION.md).

## Usage

Not yet published to crates.io (`publish = false` for now); it also depends
on the workspace crate `clazel-url`, whose host record it uses.

```rust
use clazel_psl::exec::{cookie_root_exec, registrable_domain_exec};
use clazel_url::host::parse::host_parser_full;
use clazel_url::host::record::ParsedHost;

fn code_points(s: &str) -> Vec<u32> {
    s.chars().map(u32::from).collect()
}

// Hosts come from the URL host parser; domains are code points.
let host = host_parser_full(&code_points("www.example.co.uk"), false).expect("a domain");
assert_eq!(registrable_domain_exec(&host), Some(code_points("example.co.uk")));

// The registrable domain of a bucket host is itself, but its cookie root is
// the shortest suffix that is not a public suffix: `amazonaws.com`.
let bucket = host_parser_full(&code_points("bucket.s3.us-east-2.amazonaws.com"), false).expect("a domain");
assert_eq!(registrable_domain_exec(&bucket), Some(code_points("bucket.s3.us-east-2.amazonaws.com")));
assert!(matches!(cookie_root_exec(&bucket), ParsedHost::Domain(d) if d == code_points("amazonaws.com")));
```

## Licence

The code is MIT, as in the repository's [LICENSE](../../LICENSE). The
vendored list under `data/` and the tables generated from it are the Public
Suffix List, under the Mozilla Public License 2.0 (`data/*/LICENSE`). See the
[main README](../../README.md) for the project.
