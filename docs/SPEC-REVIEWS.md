# Spec reviews

A proof only shows that code matches its spec. Whether the spec matches the
web standard is checked by a person. This file records those reviews.

**Only humans add rows.** AI agents may edit spec files but must never add or
change a row here (CLAUDE.md). The checker cannot tell who wrote a row; git
history can, so each review should land in a commit without an AI
co-author.

## What needs review

Every file in a crate named:

- `spec.rs`: transcriptions of standards;
- `contract.rs`: what the implementation is proven to satisfy;
- `axioms.rs`: anything assumed rather than proven;
- `mutations.json`: the judgment, for each mutation, of whether a proven
  theorem is false for it (`killed`) or only the proof script breaks
  (`killed-incidentally`).

## How to review

1. Read the file against the standard it cites, at the commit it cites.
2. Run `cargo xtask check`. Under "spec reviews" it lists every file that
   is unreviewed or stale, with its current SHA-256.
3. Add (or update) one row per file: path, that SHA-256, your name, the
   date, and what you reviewed it against.

A row is **current** while the file's SHA-256 matches. Any edit to the file
makes the review **stale** until someone reviews it again. Unreviewed and
stale files do not fail the build, but they are listed on every run, shown
in the README status table, and they stop a crate from declaring any tier
above 0.

<!-- BEGIN REVIEWS: checked by `cargo xtask check` -->
| File | SHA-256 | Reviewer | Date | Reviewed against |
|------|---------|----------|------|------------------|
<!-- END REVIEWS -->
