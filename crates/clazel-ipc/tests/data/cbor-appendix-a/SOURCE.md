Upstream: https://github.com/cbor/test-vectors/blob/aba89b653e484bc8573c22f3ff35641d79dfd8c1/appendix_a.json
Commit: aba89b653e484bc8573c22f3ff35641d79dfd8c1
License: none stated (the repository has no LICENSE file; see LICENSE.md)

`appendix_a.json` is copied byte for byte from the root of the `cbor/test-vectors`
repository at that commit (git blob 40d3b56223f1a812e34866f30b314a2dd3e5f64c, 10323 bytes).
It is the only commit that touches the file; the repository has not changed since January 2014.

It holds "all examples in Appendix A of RFC 7049". RFC 8949 Appendix A carries the
same examples, so this is the vector set the plan names for RFC 8949.

`xtask/src/testdata/cbor_appendix_a.rs` converts it into
`tests/generated/cbor_appendix_a.rs`, read by `tests/conformance_cbor.rs`. All 82 rows
are converted. A row is inside the profile only if the JSON says it is built from unsigned
integers, text strings, booleans, byte strings (`h'..'` diagnostic) and arrays of them,
with `roundtrip` true and no tag; the converter decides this from the JSON, never from the
decoder. Every other row must be rejected.
