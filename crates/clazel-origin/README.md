# clazel-origin

Origins and sites for the Clazel browser, and the origin of a URL. Part of
[Clazel](../../README.md), a web browser whose parsers of untrusted input
carry machine-checked proofs.

## What it is

- **Origins and sites:** HTML Standard §7.1.1 (origin, effective domain,
  ASCII serialization of an origin, same origin, same origin-domain) and
  §7.1.1.1 (site, obtain a site, same site, serialization of a site,
  schemelessly same site). An origin is opaque or a tuple of scheme, host,
  port and domain. Registrable domains come from [`clazel-psl`](../clazel-psl/README.md).
- **Origin of a URL:** URL Standard §4.7 "origin": the special schemes give a
  tuple origin, the `blob:` case parses the URL's path, and `file:` and
  everything else give a new opaque origin.
- **Spec only, no executable version:** HTML §7.1.1.2 "is a registrable
  domain suffix of or is equal to". Its only caller is the `document.domain`
  setter, which is later work.

Out of scope: the blob URL store (the URL record has no blob URL entry, so
that step of §4.7 never applies), and the URL parser itself, which is
`clazel-url`.

## Verification

Tier 2: the executable code is proven, in Verus, to equal an executable
specification of the standards, over all inputs. Current numbers are in the
[status table](../../README.md#verification-status).

- **Proven:** same origin, same origin-domain, serialization, obtain a site,
  same site, schemelessly same site and `url_origin_exec` (with the real URL
  parser) equal the spec. The spec is stated over any Public Suffix List; the
  executable code is proven for the generated list. Same origin is an
  equivalence on tuple origins and implies same site.
- **Independent transcription:** `independent.rs` is RFC 6454 §4, §5 and §6.2.
  `independent_equivalence.rs` proves same origin and serialization equal to
  it, but only on a stated class: opaque origins, and tuple origins with a
  null domain whose port is null exactly when it is the scheme's default (the
  URL parser produces only these). Default ports are a modelling choice,
  because the RFC leaves them to the scheme. HTML's site definitions have no
  second source; their evidence is the conformance rows below.
- **Mutations:** every deliberately broken spec is rejected by a checked
  certificate (`mutations.json`). None covers the `blob:` test or its path
  parse, since Verus cannot evaluate that quantifier; the conformance rows
  cover them.
- **Conformance:** the HTML standard's example tables for same origin and same
  site (the `wildlife.museum` rows are not run, because that is not a rule of
  the real list); every row of WPT `urltestdata.json` that has an `origin`;
  and a differential against rust-url's `Url::origin()`, where a few inputs
  differ and are counted as expected failures (rust-url's IDNA rejects some,
  and it differs from the standard on `blob:` URLs with some inner schemes).
  Passing counts are in the table.
- **Modelling choices** (listed at the top of `src/spec.rs`): an opaque origin
  carries an id the caller allocates; `file:` URLs get a fresh opaque origin,
  so they are never same origin with anything, themselves included; a `blob:`
  path that is not a scalar value string counts as a failed parse (parsed URLs
  never reach that case).

## Trust

The proofs assume the Rust compiler, Verus and its solver, that the specs
transcribe the standards correctly, and the generated Public Suffix List
tables of `clazel-psl`. The full list is in
[docs/VERIFICATION.md](../../docs/VERIFICATION.md).

## Usage

Not yet published to crates.io (`publish = false` for now); it depends on the
workspace crates `clazel-url`, `clazel-psl` and `clazel-encoding`.

```rust
use clazel_origin::exec::{
    same_origin_exec, same_site_exec, serialization_of_origin_exec, url_origin_exec,
};
use clazel_url::url::parse::basic_url_parser;

fn code_points(s: &str) -> Vec<u32> {
    s.chars().map(u32::from).collect()
}

let origin_of = |url: &str, fresh: u64| {
    let parsed = basic_url_parser(&code_points(url), None).expect("a URL");
    url_origin_exec(&parsed, fresh)
};

let a = origin_of("https://www.example.com/a", 1);
let b = origin_of("https://api.example.com/b", 2);
assert_eq!(serialization_of_origin_exec(&a), code_points("https://www.example.com"));
assert!(!same_origin_exec(&a, &b));
assert!(same_site_exec(&a, &b));

// `fresh` is the id of "a new opaque origin"; the caller allocates distinct ids.
let f1 = origin_of("file:///etc/hosts", 3);
let f2 = origin_of("file:///etc/hosts", 4);
assert!(!same_origin_exec(&f1, &f2));
assert_eq!(serialization_of_origin_exec(&f1), code_points("null"));
```

## Licence

MIT, as in the repository's [LICENSE](../../LICENSE). See the
[main README](../../README.md) for the project.
