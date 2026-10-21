# Audits of `clazel-sys`

`clazel-sys` is the only crate that contains `unsafe` (CLAUDE.md rule 1,
[VERIFICATION.md](VERIFICATION.md#the-unsafe-exception)). Machine checks
bound what it can do; this log records the second half of "audited": **every
change to the crate is read by an LLM session other than the one that wrote
it**, and the result is recorded here against the exact source.

**Whoever wrote or edited any file of `clazel-sys` never writes its audit
row**, in that session or a continuation of it. This is a rule, not a machine
check: the checker cannot tell who wrote a row, so it can only make sure a
row exists for the current source. It is also not a proof: an audit is a
second opinion from a model. Do not describe the crate as verified.

## What `cargo xtask check` does with this file

It computes the SHA-256 of the crate's source and compares it with the
**latest** row (the last one in the table). It fails if there is no row, if
the hash differs, or if the latest verdict is not `approved`. Every edit to
any file in the crate therefore needs a new row, and an old matching row does
not help once a later row exists.

### The hash

The files hashed are every regular file under `crates/clazel-sys`, except
hidden files and directories (names starting with `.`) and any `target/`
directory, in byte order of their repo-relative path. For each file one line
`<sha256 of the file>  <path>` (two spaces, the format of `shasum -a 256`) is
formed, and the audit hash is the SHA-256 of those lines, each ended by a
newline. From the repository root, by hand:

```sh
find crates/clazel-sys -type f -not -path '*/.*' -not -path '*/target/*' \
  | LC_ALL=C sort | xargs shasum -a 256 | shasum -a 256
```

`cargo xtask check` prints the hash and the files it covers under
"clazel-sys audit". Symbolic links inside the crate are an error.

## How to audit

You are the auditor only if you did not write or edit the code being audited.
If you did, stop: tell the maintainer that another session must audit it.

1. Run `cargo xtask check` and note the hash it prints. Read every file it
   lists, in full, not a diff. Stop if any file is missing from the list that
   should be there.
2. For **each** `unsafe` block, open the man page it cites (`man 2 prctl`,
   `man 2 seccomp`, `man 7 landlock` and the `landlock_*` pages, `man 2
   unshare`, `man 3 sandbox_init`) and the `libc` declaration of the function
   and of every type and constant passed to it (in the pinned `libc` version
   from `docs/DEPENDENCIES.md`). Check:
   - the argument count, types, sizes and signedness match the declaration;
   - every pointer passed is non-null where required, aligned, points to
     initialised memory of the stated size, and outlives the call (a pointer
     taken before the block must not be to a temporary dropped earlier);
   - the structure layout is `libc`'s or `#[repr(C)]` with the kernel's field
     order, and its length argument is computed, not typed;
   - the return value is checked as the man page says (`-1` and `errno`), the
     error is read with nothing in between, and a failure is never reported
     as success;
   - a file descriptor returned is owned exactly once and closed on every
     path (`OwnedFd`), and memory returned by the system is freed exactly
     once (`sandbox_free_error`);
   - the block holds one call, as the checker already requires, and the
     `// SAFETY:` comment states the real reason it is sound, not a restated
     precondition.
3. Check the safe wrapper around each block: that its narrow types make the
   unsound call impossible from safe code (no length that can exceed the
   slice, no string with an interior NUL reaching the call), and that it makes
   no policy decision (it never chooses what to allow).
4. Check what the checker cannot: that nothing in the crate calls a function
   that merely resembles a listed one, that the `cfg` gating matches the
   target of each call, and that tests which call the OS do not weaken the
   test process irreversibly and are skipped under Miri.
5. Add **one row** below, last in the table: date, the hash from step 1,
   which session or tool audited (not who wrote the code), what you audited
   against (man page and `libc` versions, plus what you could not check), and
   a verdict: `approved` or `rejected`. Put findings of any kind in the row or
   in the report; a `rejected` row stays in the log. Never edit or remove an
   earlier row, and never touch a file of `clazel-sys` while auditing: if the
   audit finds a problem, the fix is a change by someone else, which then
   needs its own audit.

<!-- BEGIN AUDITS: checked by `cargo xtask check` -->
| Date | SHA-256 | Auditor | Audited against | Verdict |
|------|---------|---------|-----------------|---------|
<!-- END AUDITS -->
