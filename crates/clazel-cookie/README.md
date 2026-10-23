# clazel-cookie

HTTP cookies for the Clazel browser, from RFC 6265bis. Part of
[Clazel](../../README.md), a web browser whose parsers of untrusted input
carry machine-checked proofs.

**Status: tier 2.** Every part below is proven in Verus to equal a
transcription of the draft. See [Verification](#verification).

## What it is

Everything is pinned to draft-ietf-httpbis-rfc6265bis-22 (1 December 2025,
not yet an RFC).

- §5.1.1 cookie dates; §5.1.2 canonicalized host names; §5.1.3 domain
  matching; §5.1.4 default-path and path-match; §5.4 name prefixes
  (`__Secure-`, `__Host-`); §5.5 the 400-day lifetime limit; and §5.6 the
  Set-Cookie parser with §5.6.1 to §5.6.7 (Expires, Max-Age, Domain, Path,
  Secure, HttpOnly, SameSite).
- §5.2 same-site requests (over an abstract request context), §5.7 the
  storage model and §5.8 the retrieval model (`src/storage/`), with the jar
  as a sequence of cookie records and the current time as an input. In
  Phase 2 the only caller is `document.cookie`, through the non-HTTP API.
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

Tier 2: the code is proven in Verus to equal an executable specification of
the standard. Current numbers are in the
[status table](../../README.md#verification-status).

- **Proven:** every executable function of dates, host canonicalization,
  matching, Set-Cookie parsing, storage and retrieval equals its spec.
  Lemmas include that domain-match and path-match are preorders and
  path-match is a prefix order, that the default-path path-matches its URL, and
  that no expiry exceeds now plus the limit. `matching/independent.rs`
  (RFC 6265 §5.1.3 and §5.1.4) is proven equal to the spec on every input.
  `date/independent.rs` (RFC 9110 §5.6.7 HTTP-date) and
  `set_cookie/independent.rs` (the §4.1.1 `set-cookie-string` grammar) are
  proven to agree with the parsers on stated classes of input, with the
  exceptions listed in those files.
- **Isolation lemmas** (`src/storage/isolation.rs`), which the browser
  kernel's cookie non-interference theorem rests on: a stored cookie's
  domain has the request host's cookie root (`lemma_store_within_root`);
  storing for one root leaves every other root's cookies unchanged
  (`lemma_store_frame`); storage keeps the per-root limit and unique keys
  (`lemma_store_bounds`); and retrieval returns only, and changes only,
  cookies of the request host's root (`lemma_retrieve_within_root`,
  `lemma_retrieve_frame`). The retrieval lemmas need every cookie's domain
  to be non-empty: a cookie with the empty domain would domain-match any
  host ending in a dot (`example_empty_domain_breaks_retrieve_within_root`
  shows it). Storage never creates one, and a lemma shows storing keeps
  the invariant, so a caller holding the jar must keep it too.
- `storage/independent.rs` (RFC 6265 §5.3 and §5.4) is proven equal to
  storage and retrieval on a stated class: cookies without SameSite, name
  prefixes or the secure-overwrite rule, on host names.
- **Mutations:** every mutation in `mutations.json` is certified, including
  global eviction, a dropped public-suffix check, a skipped HttpOnly check
  for the non-HTTP API and a widened domain-match. **Gap:** mutations inside
  the storage algorithm's cookie creation (§5.7 steps 2 to 8 and 11 to 23,
  among them the storage-side HttpOnly check) have no certificate, because
  three of its helpers are quantifiers Verus cannot evaluate on concrete
  inputs. Those steps are covered by the proofs and the conformance suites
  only.
- **Conformance:** WPT `cookies/` (the fixed-data cases, with one expected
  failure that belongs to the HTTP layer), the `http-state` parser corpus
  (expected failures listed by name with reasons), the 70 `http-state`
  cookie-date cases, and a differential against the `cookie_store` crate on
  random set and get sequences. WPT tests that need a server, redirects or
  frames are listed in `tests/data/wpt-cookies/SOURCE.md`; they arrive with
  Phase 3.
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
workspace crates `clazel-url`, `clazel-psl` and `clazel-origin`. Storage and
retrieval are `storage::exec::store_a_set_cookie_string_exec` and
`storage::exec::retrieve_a_cookie_string_exec`, over a jar of
`CookieRecord`s with the request URL and context as records; the example
below shows the parsing and matching parts.

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
