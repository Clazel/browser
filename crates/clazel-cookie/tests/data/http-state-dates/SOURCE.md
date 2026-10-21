# `http-state` cookie-date parsing cases

Upstream: https://github.com/abarth/http-state/tree/155e45c6168e6de2eb727193010fd12e3c789185/tests/data/dates
Commit: 155e45c6168e6de2eb727193010fd12e3c789185
License: BSD-3-Clause for `bsd-examples.json` (the Chromium Authors' header, copied into `LICENSE.md`); `examples.json` carries no license header (the repository states that contributions are IETF Contributions under the IETF's note well)

`examples.json` and `bsd-examples.json` are copied byte for byte from
`tests/data/dates/` at that commit (the most recent commit of the
repository when they were vendored, 21 October 2026). To update, copy the
same files from a newer commit, change the commit above, and run
`cargo xtask testdata`.

`xtask/src/testdata/http_state_dates.rs` converts them into
`tests/generated/http_state_dates.rs`, read by
`tests/conformance_dates.rs`: every `test` string must parse with the
RFC 6265bis §5.1.1 algorithm to the date in `expected` (whose weekday is
also checked against the parsed date), or fail when `expected` is `null`.

Not vendored, and why: the rest of `http-state` (`tests/data/parser/`, the
Set-Cookie and Cookie test cases) exercises the storage model and the
retrieval model, which are item 2.9 and need a cookie jar. WPT `cookies/`
is the same: every test sets a cookie and reads it back.
