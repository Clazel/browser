# WPT `webstorage/`: the `localStorage` call tests

Upstream: https://github.com/web-platform-tests/wpt/tree/d928657a0858e62b66a3724b3249e2b6e6c773a3/webstorage
Commit: d928657a0858e62b66a3724b3249e2b6e6c773a3
License: BSD-3-Clause (`LICENSE.md`, copied from the root of the WPT repository)

Files, copied byte for byte from that commit (the same commit as
`../../../../clazel-cookie/tests/data/wpt-cookies/` and
`../../../../clazel-url/tests/data/wpt-urltestdata/`):

| Here | Upstream |
|------|----------|
| `storage_clear.window.js` | `webstorage/storage_clear.window.js` |
| `storage_getitem.window.js` | `webstorage/storage_getitem.window.js` |
| `storage_key_empty_string.window.js` | `webstorage/storage_key_empty_string.window.js` |
| `storage_length.window.js` | `webstorage/storage_length.window.js` |
| `storage_removeitem.window.js` | `webstorage/storage_removeitem.window.js` |
| `storage_setitem.window.js` | `webstorage/storage_setitem.window.js` |
| `LICENSE.md` | `LICENSE.md` |

To update, copy the same files from a newer commit, change the commit
above, and run `cargo xtask testdata`.

`xtask/src/testdata/wpt_webstorage.rs` converts the tests into
`tests/generated/wpt_webstorage.rs`, read by
`tests/conformance_wpt_webstorage.rs`. It reads a small JavaScript subset
(the grammar is in the converter's header: `clear`, `setItem`,
`removeItem`, `s[k] = v`, `delete s[k]`, `assert_equals` of `getItem`,
`s[k]` and `s.length`, `k in s`, nested `test` calls) and
**skips** a test that uses anything else, listing it in a `// skipped:` line
of the generated file. A case is run as the page runs it: the test is a
document at `http://web-platform.test:8000/webstorage/<file>`, whose
renderer sends one frame per call, and each assertion is checked against the
reply frame.

**Converted:** see the count in the generated file. Only `localStorage` is
converted: the kernel has no `sessionStorage` (2.10 models `localStorage`
only), so the `sessionStorage` run of every test is not run.

**Not converted, and why:**

- *Not vendored* (the file needs a JavaScript object or event model, not
  storage calls):
  `defineProperty.window.js`, `set.window.js`, `storage_builtins.window.js`,
  `storage_enumerate.window.js`, `storage_functions_not_overwritten.window.js`,
  `storage_in.window.js`, `storage_indexing.window.js`,
  `storage_supported_property_names.window.js` and `symbol-props.window.js`
  (JavaScript property semantics of the `Storage` object: property
  definition, enumeration, built-in names, symbols); `eventTestHarness.js`
  and every `event_*` file (storage events are not modelled, item 2.10);
  `storage_key.window.js` (its tests loop with a nested helper over keys, and
  `key(n)` of a `Storage` has an implementation-defined order); `missing_arguments.window.js`
  (a missing argument is a `TypeError` in the JavaScript binding: an IPC
  message always has all its fields); `storage_string_conversion.window.js`
  (converts functions and objects to strings, the binding's job);
  `storage_set_value_enumerate.window.js` (a loop over a table);
  `storage_local_setitem_quotaexceedederr.window.js` (loops `setItem` until
  the quota is exceeded, which a table cannot say; the kernel's quota has
  Verus proofs instead, `exec::storage`); `storage_local_quota_independent_from_session.window.js`,
  `storage_session_*`, `sessionStorage-*` (`sessionStorage`);
  `storage_local_window_open.window.js`, `storage_local-manual.html`,
  `localstorage-*` (windows, frames and partitioning: other documents and
  browsing contexts); `document-domain.html`; the `resources/` directory.
- *Skipped by the converter*, each listed with its reason in the generated
  file: `storage_setitem.window.js`'s two tests that pass an object whose
  `toString` throws (an object argument is the JavaScript binding's, not an
  IPC message's), and its two loops over generated keys and values
  (`interesting_strs`, a loop over every code unit up to 0xFF, some of them
  lone surrogates, which have no UTF-8 and so cannot be a text string of the
  IPC schema). Every other test of the six files is converted.
