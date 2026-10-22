# clazel-cookie

HTTP cookies for the Clazel browser, from RFC 6265bis. Part of
[Clazel](../../README.md), a web browser whose parsers of untrusted input
carry machine-checked proofs.

**Status: tier 0 (target tier 2).** The parts below marked "built" have
proofs; cookie storage and retrieval (Phase 2 item 2.9) are being implemented
now, so the crate as a whole is not yet at its target tier. See
[Verification](#verification).

## What it is

Everything is pinned to draft-ietf-httpbis-rfc6265bis-22 (1 December 2025,
not yet an RFC).

- **Built:** §5.1.1 cookie dates; §5.1.2 canonicalized host names; §5.1.3
  domain matching; §5.1.4 default-path and path-match; §5.4 name prefixes
  (`__Secure-`, `__Host-`); §5.5 the 400-day lifetime limit; and §5.6 the
  Set-Cookie parser with §5.6.1 to §5.6.7 (Expires, Max-Age, Domain, Path,
  Secure, HttpOnly, SameSite).
- **In progress (item 2.9):** §5.2 same-site requests, §5.7 the storage model
  and §5.8 the retrieval model. Their specification and contracts are
  written (`src/storage/`), including two isolation decisions below; the
  executable code, its proofs and its evidence are not.
- **Out of scope:** HTTP `Set-Cookie` and `Cookie` headers (they arrive with
  Fetch in Phase 3), persistence to disk, partitioned cookies (CHIPS) and
  third-party cookie blocking, which are not in 6265bis.

### The isolation boundary

Two decisions in the storage spec, because the kernel's cookie
non-interference theorem is false without them:

- **The cookie root, not the registrable domain, is the boundary.** A cookie
  set with `Domain=amazonaws.com` is sent to a host such as
  `bucket.s3.us-east-2.amazonaws.com`, whose registrable domain is itself.
  Two hosts can share a cookie exactly when they have the same cookie root
  (defined in [`clazel-psl`](../clazel-psl/README.md)).
- **Eviction is per cookie root, with no global limit** (180 per root). A
  global limit would let one site evict another's cookies by setting many of
  its own. The RFC leaves the policy to the user agent, so this is a choice,
  not an erratum. Expired cookies are evicted globally, which depends only on
  time.

## Verification

Tier 0 today: safe Rust with tests, because the tier describes the whole
crate and storage and retrieval are not built. The target is tier 2, where the
code is proven in Verus to equal an executable specification of the standard.
Current numbers are in the
[status table](../../README.md#verification-status).

- **Proven for the built parts:** every executable function of dates,
  host canonicalization, matching and Set-Cookie parsing equals its spec.
  Lemmas include that domain-match and path-match are preorders and
  path-match is a prefix order, that the default-path path-matches its URL, and
  that no expiry exceeds now plus the limit. `matching/independent.rs`
  (RFC 6265 §5.1.3 and §5.1.4) is proven equal to the spec on every input.
  `date/independent.rs` (RFC 9110 §5.6.7 HTTP-date) and
  `set_cookie/independent.rs` (the §4.1.1 `set-cookie-string` grammar) are
  proven to agree with the parsers on stated classes of input, with the
  exceptions listed in those files.
- **Mutations:** the built parts have certified mutations
  (`mutations.json`); storage has none yet.
- **Conformance:** the 70 `http-state` cookie-date cases
  (`tests/conformance_dates.rs`) and worked examples written by us
  (`tests/set_cookie_examples.rs`, not counted as conformance).
- **Not done:** the storage and retrieval implementation and proofs; the
  statements storage will prove (`lemma_store_within_root`,
  `lemma_retrieve_within_root`, `lemma_store_frame`, `lemma_retrieve_frame`,
  `lemma_store_bounds`) are recorded in the spec, not proven; no WPT
  `cookies/` data, `http-state` parser corpus or `cookie_store` differential
  yet; no Set-Cookie conformance data.
- **Modelling choices** (listed in the spec headers): hosts are the URL host
  parser's output, not bare IDNA2008, so labels follow UTS #46 as browsers
  do; **instants are seconds since 1601-01-01T00:00:00Z**; strings are
  octets; the lifetime limit is fixed at 400 days; the request URL and request
  context are abstract records, not parsed URLs. §5.6.1 steps 3 and 4 and
  §5.7 step 10 are read by their evident intent, see
  [docs/ERRATA.md](../../docs/ERRATA.md).

## Trust

The proofs assume the Rust compiler, Verus and its solver, that the specs
transcribe the draft correctly, and the Public Suffix List tables of
`clazel-psl`. The full list is in
[docs/VERIFICATION.md](../../docs/VERIFICATION.md).

## Usage

Not yet published to crates.io (`publish = false` for now); it depends on the
workspace crates `clazel-url`, `clazel-psl` and `clazel-origin`. The API below
is the built part; there is no storage API yet.

```rust
use clazel_cookie::date::exec::parse_a_cookie_date;
use clazel_cookie::matching::exec::{default_path, domain_matches, path_matches};
use clazel_cookie::set_cookie::exec::{AttributeExec, parse_a_set_cookie_string};

// Time is an input: seconds since 1601-01-01T00:00:00Z.
let date = parse_a_cookie_date(b"Sun, 06 Nov 1994 08:49:37 GMT").expect("a date");
assert_eq!((date.year, date.month, date.day_of_month), (1994, 11, 6));

let now = 1_000;
let cookie = parse_a_set_cookie_string(b"id=42; Path=/app; Secure; Max-Age=10", b"/index", now)
    .expect("a cookie");
assert_eq!((cookie.name.as_slice(), cookie.value.as_slice()), (&b"id"[..], &b"42"[..]));
assert!(cookie.attributes.iter().any(|a| matches!(a, AttributeExec::MaxAge(t) if *t == now + 10)));

assert!(domain_matches(b"www.example.com", true, b"example.com"));
assert!(path_matches(b"/app/page", b"/app"));
assert_eq!(default_path(b"/a/b/c"), b"/a/b".to_vec());
```

## Licence

MIT, as in the repository's [LICENSE](../../LICENSE). See the
[main README](../../README.md) for the project.
