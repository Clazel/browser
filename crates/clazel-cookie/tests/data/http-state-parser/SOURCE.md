# `http-state` cookie parser corpus

Upstream: https://github.com/abarth/http-state/tree/155e45c6168e6de2eb727193010fd12e3c789185/tests/data
Commit: 155e45c6168e6de2eb727193010fd12e3c789185
License: BSD-3-Clause for the Chromium-derived rows (`chromium*` and `disabled-chromium*`; the Chromium Authors' header, copied into `LICENSE.md`); the other rows carry no license header (the repository states that contributions are IETF Contributions under the IETF's note well, and the `mozilla*` rows were written after Mozilla's cookie tests, with no license of their own upstream)

`parser.json` is copied byte for byte from `tests/data/parser.json` at that
commit (the most recent commit of the repository when it was vendored, 22
October 2026). It is the repository's own collection (made by
`tools/test_data_to_json/test_data_to_json.py`) of the 222 pairs of files in
`tests/data/parser/`: `NNNN-test`, the response headers the test server
sends (`Set-Cookie` lines, and for the 64 tests that have one a `Location`),
and `NNNN-expected`, the `Cookie` header the client must send next. The raw
pairs are not vendored: `cargo xtask testdata` takes a fixed list of files
per suite, and 444 file names are not a list. The JSON has the same content
(checked when it was vendored: for every row the `Set-Cookie` values, the
presence of a `Location`, and the `Cookie` header agree with the pair, apart
from the `DISABLED_*` rows, whose files are named in lower case upstream).
To update, copy the same file from a newer commit, change the commit above,
and run `cargo xtask testdata`.

`xtask/src/testdata/http_state_parser.rs` converts it into
`tests/generated/http_state_parser.rs`, read by
`tests/conformance_http_state.rs`: every row (222) is run through the proven
`store_a_set_cookie_string_exec` for each `received` value, with the
request `http://home.example.org:8888/cookie-parser?<test>`, and then
`retrieve_a_cookie_string_exec` for the request the row's `sent-to` (or
`/cookie-parser-result?<test>`) names, as an HTTP request. The URLs are
parsed with the proven URL parser. The corpus was written for RFC 6265 and
the browsers of 2010, so the test fixes the clock at 1 January 2010. Rows
where RFC 6265bis draft 22 deliberately differs from RFC 6265 are listed in
the test as expected failures, each with its reason; none is counted as a
pass.
