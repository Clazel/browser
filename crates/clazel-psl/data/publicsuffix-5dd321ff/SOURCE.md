# Public Suffix List, publicsuffix/list at one commit

Commit: 5dd321ffe02039e2431382a095cf80e27ff5eb94 (2026-10-20, "Remove `oya.to` (domain expired & drop-caught) (#3432)")
License: Mozilla Public License 2.0 (`LICENSE`, copied from the same commit; the list's `tests/tests.txt` is dedicated to the public domain by its own header)

Each file is copied byte for byte from https://github.com/publicsuffix/list at the commit above:

- https://raw.githubusercontent.com/publicsuffix/list/5dd321ffe02039e2431382a095cf80e27ff5eb94/public_suffix_list.dat
- https://raw.githubusercontent.com/publicsuffix/list/5dd321ffe02039e2431382a095cf80e27ff5eb94/tests/tests.txt
- https://raw.githubusercontent.com/publicsuffix/list/5dd321ffe02039e2431382a095cf80e27ff5eb94/LICENSE

`cargo xtask check` hashes every file and fails if one differs from the
line below, or if the directory holds anything else:

SHA-256: 9b4827a9e428a0192a9ea0a6b7804a4cc653d5f39a03456d3b17447b86d78de9 public_suffix_list.dat
SHA-256: 61a3a502cf471d1a919d5e43c10e910023b0c4230e1db506f8e2ff0b47d2234e tests.txt

`xtask/src/psl.rs` turns `public_suffix_list.dat` into
`crates/clazel-psl/src/data.rs` (`cargo xtask tables`). `tests.txt` is the
list's own `checkPublicSuffix` suite, run by `tests/conformance_psl.rs`.
The ICANN and PRIVATE sections are both used (browsers treat them alike
for cookies), and the tables do not distinguish them.
