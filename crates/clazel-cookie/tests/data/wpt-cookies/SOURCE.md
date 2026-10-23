# WPT `cookies/`: the fixed-data cookie tests

Upstream: https://github.com/web-platform-tests/wpt/tree/d928657a0858e62b66a3724b3249e2b6e6c773a3/cookies
Commit: d928657a0858e62b66a3724b3249e2b6e6c773a3
License: BSD-3-Clause (`LICENSE.md`, copied from the root of the WPT repository)

Files, copied byte for byte from that commit (the same commit as
`../../../clazel-url/tests/data/wpt-urltestdata/`):

| Here | Upstream |
|------|----------|
| `cookie-test.js` | `cookies/resources/cookie-test.js` |
| `name.html` | `cookies/name/name.html` |
| `value.html` | `cookies/value/value.html` |
| `expires.html` | `cookies/attributes/expires.html` |
| `max-age.html` | `cookies/attributes/max-age.html` |
| `invalid.html` | `cookies/attributes/invalid.html` |
| `path.html` | `cookies/attributes/path.html` |
| `secure.https.html` | `cookies/attributes/secure.https.html` |
| `charset.html` | `cookies/encoding/charset.html` |
| `name-and-value.html` | `cookies/size/name-and-value.html` |
| `LICENSE.md` | `LICENSE.md` |

To update, copy the same files from a newer commit, change the commit
above, and run `cargo xtask testdata`.

`xtask/src/testdata/wpt_cookies.rs` converts each page's table of
`{cookie, expected, name, defaultPath}` into `tests/generated/wpt_cookies.rs`
(a small reader for the expressions the tables use, including
`cookieStringWithNameAndValueLengths` and `"a".repeat(n)`), read by
`tests/conformance_wpt_cookies.rs`. The converter fails if a page no longer
contains the loop that runs its table, or `cookie-test.js` no longer sets
and reads cookies as the test assumes. A case is run as the pages run it:
`httpCookieTest` sets the cookie(s) as `Set-Cookie` header values of a
response from `/cookies/resources/cookie.py` (path
`/cookies/resources/cookie.py`, so the default-path is `/cookies/resources`)
and reads `document.cookie` in `/cookies/resources/echo-cookie.html` (when
`defaultPath` is true) or in the page; `domCookieTest` assigns
`document.cookie` in the page and reads it there. The origin is
`http://web-platform.test:8000` (`https://web-platform.test:8443` for
`*.https.html`), the page is a top-level document, and the clock is fixed at
23 October 2026. Each case starts with an empty cookie jar.

**Converted:** 178 cases (counted in the generated file) from the nine pages
above, plus the 18 names of `name.html`'s second loop (included in the
178). One case (`value.html`, a line feed in a header value) is an expected
failure, with its reason, in the test.

**Not converted, and why** (everything else under `cookies/`):

- Tests that need an HTTP server for more than a `Set-Cookie` header
  value: `attributes/attributes-ctl.sub.html`, `name/name-ctl.html` and
  `value/value-ctl.html` (control characters sent through the HTTP layer,
  which is Phase 3), `attributes/path-redirect.html` and
  `attributes/resources/domain-child.sub.html` (redirects),
  `ordering/` (redirects), `size/attributes.www.sub.html` (a `www`
  subdomain and attribute sizes through the HTTP layer), `domain/` (the
  `.sub.headers` files: `{{host}}` substitutions, and subdomain hosts),
  `attributes/domain.sub.html`, `attributes/secure-non-secure.html`,
  `attributes/resources/` (frames of other origins), `secure/` (`ws:` and
  `wss:` connections), `path/*.window.js` and `value/value-overwrite.https.window.js`,
  `attributes/httponly-overwrite.https.window.js` (cookie store API,
  service workers, `fetch` credentials), `prefix/` (`.headers`
  files, `__host.header*`: `Set-Cookie` through server-side header files),
  and the top-level `cookies/*.html` files (frames, navigation).
- Tests that need a browser feature outside cookies: `samesite/`,
  `schemeful-same-site/`, `third-party-cookies/`, `partitioned-cookies/`,
  `origin-bound-cookies/`, `samesite-none-secure/` (Fetch request contexts,
  Phase 3; partitioned cookies and third-party blocking are not in RFC
  6265bis), `encoding/` has no other file.
- `attributes/expires.html` is converted for its table only; its last
  `domCookieTest` call (a non-ASCII time zone name) is a single call, not a
  table row, and is not run.
