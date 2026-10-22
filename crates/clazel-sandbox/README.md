# clazel-sandbox

The sandbox policies for Clazel renderer processes, as plain data. Part of
[Clazel](../../README.md), a web browser whose parsers of untrusted input
carry machine-checked proofs.

This crate **decides what a renderer may do and produces the policy; it does
not apply it.** It has no dependencies, no `unsafe` and makes no system calls.
Applying a policy to a process is a separate step (Phase 2 item 2.15), which
needs the OS calls that only `clazel-sys` is allowed to make.

## What it is

There is no single standard here; each policy follows the OS it targets.

- **Linux seccomp-BPF** (`syscalls`, `seccomp`): a syscall allowlist with the
  reason for each entry (read and write on the inherited socket, `exit_group`,
  memory management, futex; nothing that opens, connects, forks, executes or
  passes descriptors), with numbers for x86-64 and aarch64, and a generator
  for the classic BPF program: check the architecture field first, then one
  comparison per allowed number, otherwise kill the process.
- **Linux Landlock** (`landlock`): a ruleset that handles every filesystem,
  TCP and scope right and allows none, with `for_abi` to drop rights newer
  than the running kernel's Landlock ABI.
- **Linux namespaces** (`namespaces`): user, mount, PID, network and IPC, with
  their `CLONE_NEW*` flags.
- **macOS Seatbelt** (`seatbelt`): an SBPL profile, `(deny default)` plus the
  minimum the Rust runtime needs. SBPL is Apple's undocumented language, so
  there is no standard to cite.
- **A classic-BPF validator and interpreter** (`interp`), written from the
  kernel's `filter.rst` and `seccomp_filter.rst`, used to run generated
  programs.

Out of scope: applying any of it, argument filters (selection is by syscall
number only), other architectures, and sandboxing on other platforms.

## Verification

Tier 1: Kani bounded model checking shows the code never panics, overflows or
indexes out of bounds on any input within the harnesses' stated bounds. It is
not a Verus-proven functional-correctness tier. Current numbers are in the
[status table](../../README.md#verification-status).

- **Harnesses** (`src/proofs.rs`, run by `cargo kani`): the generator never
  panics and produces a valid program, and the program allows exactly the
  list, for symbolic allowlists of 0 to 3 numbers. For the real allowlist, on
  each architecture, the program allows exactly the list for **every** 32-bit
  syscall number, and kills every other architecture value. The validator and
  interpreter never panic on any program of up to two instructions.
- **Tests:** `tests/policies.rs` repeats the sweep over syscall numbers below
  1024 (and wrong architectures and x32 numbers) as plain tests.
  `tests/vendored.rs` re-derives every syscall number and constant from the
  vendored Linux v6.12 headers and documents in `vendor/linux/`, so none is
  from memory.
- **Known gaps:** Kani proves the pointwise generator (`insn_at`), not the
  `Vec` collection in `generate` (CBMC ran out of memory modelling it); a test
  checks the collected program equals the one the harnesses use. The
  interpreter's rejection rules are the conservative reading of `filter.rst`,
  because the kernel's `seccomp.c` is not vendored. The SBPL profile is
  unchecked: only the integration tests of Phase 2 item 2.16, running a real
  sandboxed process, can show it denies what it should.

## Trust

**The cBPF interpreter is trusted**: it models the kernel, so the exhaustive
checks are only as good as it is. That is why this crate targets Tier 1 and
not a Verus spec of BPF. Beyond that, the proofs assume the Rust compiler and
Kani, and that the OS enforces the policy it is given (macOS Seatbelt; Linux
seccomp, Landlock and namespaces), which is in the trusted computing base. The
full list is in [docs/VERIFICATION.md](../../docs/VERIFICATION.md).

## Usage

Not yet published to crates.io (`publish = false` for now). It has no
dependencies.

```rust
use clazel_sandbox::interp::{SeccompData, run, validate};
use clazel_sandbox::seccomp::{SECCOMP_RET_ALLOW, SECCOMP_RET_KILL_PROCESS, renderer_program};
use clazel_sandbox::syscalls::Arch;
use clazel_sandbox::{landlock, namespaces, seatbelt};

// Linux: the seccomp program is data; nothing is applied here.
let program = renderer_program(Arch::X86_64).expect("fits in a cBPF program");
validate(&program).expect("a valid program");
let arch = Arch::X86_64.audit_arch();
assert_eq!(run(&program, &SeccompData::new(0, arch)), Ok(SECCOMP_RET_ALLOW)); // read
assert_eq!(run(&program, &SeccompData::new(2, arch)), Ok(SECCOMP_RET_KILL_PROCESS)); // open

// The other policies are data too.
assert!(landlock::RENDERER.allows_nothing());
let flags = namespaces::renderer_unshare_flags();
assert_ne!(flags & namespaces::CLONE_NEWNET, 0);

// macOS: the SBPL text, to hand to the OS elsewhere.
assert!(seatbelt::renderer_profile().starts_with("(version 1)\n(deny default)\n"));
```

## Licence

The code is MIT, as in the repository's [LICENSE](../../LICENSE). The files
under `vendor/linux/` are verbatim copies from the Linux kernel (v6.12), read
by the tests only and never compiled in: the headers are GPL-2.0 with the
Linux syscall note, the documents GPL-2.0 (`vendor/linux/SOURCE.md`). See the
[main README](../../README.md) for the project.
