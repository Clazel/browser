# Writing a spec

How to transcribe a web standard into a Verus `spec.rs`. The goal is a file a
human can check against the standard **line by line, without knowing Verus
well**, because that check (recorded in [SPEC-REVIEWS.md](SPEC-REVIEWS.md))
is the one thing no proof can replace. The worked example is
`crates/clazel-encoding/src/utf8/spec.rs`.

## Layout of a crate

- `spec.rs`: the transcription. Spec functions only, no exec code, no proofs.
- `contract.rs`: one predicate per exec function, saying what it is proven
  to satisfy, written in terms of `spec.rs`.
- `lemmas.rs`: facts proven about the spec. They are evidence that the
  transcription is right, not part of what the implementation must meet.
- `mutations.json`: deliberate spec bugs and what the proofs do with them
  ([VERIFICATION.md](VERIFICATION.md#proof-mutation-testing)).
- `axioms.rs`: only if unavoidable; every item needs a `// AXIOM:`
  justification.

Contracts are committed before the implementation (CLAUDE.md rule 3).

## Pin the source

The file's header names the standard, its "Last Updated" date and its
commit, for example: *Encoding Standard, last updated 19 October 2026, commit
`dd79434…`*. A review is against that exact text. When the standard
changes, re-transcribe against the new commit and update the header. That
edit makes the old review stale, which is what should happen.

## Transcribe; don't redesign

- **One spec function per algorithm**, named after it ("UTF-8 decode" →
  `utf8_decode`), with a doc comment citing the section and anchor URL.
- **Keep the standard's control flow.** If it says "if A, return error; if
  B, …", write that, in that order, even when a shorter equivalent exists.
  Shorter equivalents are what lemmas are for, not the spec.
- **Number every step.** Each branch carries a `// N.` comment with the
  step number, quoting the step when it is short:
  `// 2. "If byte is end-of-queue, then return finished."`
- **Keep the standard's names.** State variables are struct fields with
  the standard's names (`bytes_needed` for "UTF-8 bytes needed").
- **Folded steps are commented.** If a step is merged into another (for
  example a trailing "return continue" folded into each branch), say so
  where it would have been.

## Modelling choices go at the top

A standard's machinery (I/O queues, "restore to the queue", "wait until")
rarely maps one-to-one onto pure functions. Each place where the spec's
*form* differs from the standard goes in a bulleted list in the file's
header, with the argument that the *meaning* is unchanged. From `utf8/spec.rs`:

- an I/O queue becomes `input: Seq<u8>` plus a read position, with
  end-of-queue at `input.len()`;
- "restore byte to ioQueue" becomes *not advancing* the position, which is
  equivalent because the restored byte is exactly the one just read;
- the output queue becomes a `Seq<u32>`, with end-of-queue implicit.

A reviewer checks these arguments once. After that, the body can be read
against the standard directly.

## When the standard is wrong

If the standard, read literally, says something it clearly does not mean
(the Encoding "peek" off-by-one is the first case):

1. Specify the evident intent, and say why in a comment at that spot.
2. Add an entry to [ERRATA.md](ERRATA.md): the quoted text, why it is
   wrong, what we specify instead, and the spec commit.
3. Do not report it upstream yourself. Filing an issue is public and is
   a human's decision; the entry's "Reported upstream" line records it.

## Make proofs possible

- Recursive spec functions need a `decreases` clause that Verus can check.
  Put recursive calls only in the branches that recurse; a call bound in a
  `let` above a `match` is checked in every branch.
- Use `nat`/`int` for the standard's "numbers", and fixed-width types only
  where the standard does bit operations on bytes or code points.
- Prove at least one property of the spec that the standard states or
  asserts (UTF-8: the decoder only emits scalar values, which §4.1 asserts).
  Then seed `mutations.json` so that a spec bug which breaks that property is
  `killed`, and record honestly which mutations it does not catch.
