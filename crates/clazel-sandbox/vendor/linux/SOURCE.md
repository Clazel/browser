# Vendored Linux kernel files

Verbatim copies from the Linux kernel, tag `v6.12`, commit
`adc218676eef25575469234709c2d87185ca223a` (Linus Torvalds' tree,
`torvalds/linux`). Fetched 2026-10-21 from
`https://raw.githubusercontent.com/torvalds/linux/v6.12/<path>`.
The headers are `GPL-2.0 WITH Linux-syscall-note` (the UAPI exception); the
documents are GPL-2.0. They are read by the tests only (never compiled into
the crate), which check every constant and syscall number in `src/` against
them.

| File | Kernel path | SHA-256 |
|------|-------------|---------|
| `syscall_64.tbl` | `arch/x86/entry/syscalls/syscall_64.tbl` | `980ce3115028c71c5618e7864d262017bde8103bcfe7b413147a14fd312c92ac` |
| `unistd.h` | `include/uapi/asm-generic/unistd.h` (aarch64 uses the generic table) | `aec51e459e2b113bcf8e16c99be09d5384fe3f4fa4a16100dfe0e71dbc0e172a` |
| `audit.h` | `include/uapi/linux/audit.h` (`AUDIT_ARCH_*`) | `a3397fb1b873e6621c1bd299754d02f53a11e8d9ae70def8774e7212a3bf8641` |
| `elf-em.h` | `include/uapi/linux/elf-em.h` (`EM_X86_64`, `EM_AARCH64`) | `e72cca577a97d1fccc7f4e5d37b39b401a527a97f02e589255c247b63cb227d2` |
| `seccomp.h` | `include/uapi/linux/seccomp.h` | `38a129b0b1e0c5cbae3b01bb159810a5cc290d7823d4c386f71d70b16e93d8dd` |
| `filter.h` | `include/uapi/linux/filter.h` | `8b07bc3c8bcaa4b43318c43e588e36258bdc6a80848efce51158a274b664be7b` |
| `bpf_common.h` | `include/uapi/linux/bpf_common.h` | `adc9e87d1a335379ffe3658547635904cae6ccb8b7d1e578d0c25b50aa44db04` |
| `landlock.h` | `include/uapi/linux/landlock.h` | `ea5575c369326da8fef2e62d0a9b528b45f4aa2302f836e995cb6d5c33bacc49` |
| `sched.h` | `include/uapi/linux/sched.h` (`CLONE_NEW*`) | `2081b07cee6adab443e4ba320d0ccb13db4c97bed64f3eefafbfde2f25c833a4` |
| `seccomp_filter.rst` | `Documentation/userspace-api/seccomp_filter.rst` | `cd51ec8cf62f5029614e8c14d43d52ce1b69efbdb73e1f8c7d1c93d646b06ad7` |
| `filter.rst` | `Documentation/networking/filter.rst` | `8e00fae0b10cfade9db8e0b6d99deae61a442eb4650c1a24eb0db21b0b3d4b48` |
| `landlock.rst` | `Documentation/userspace-api/landlock.rst` | `ba6c3a79aea760010b3517dc821eeb42a4a069c0c69042634d10484046864875` |

Not vendored, so not cited as a source: `kernel/seccomp.c`
(`seccomp_check_filter`) and `net/core/filter.c` (`bpf_check_classic`). Where
the interpreter's behaviour depends on them (what a seccomp filter may
contain, division by zero) the source says so, and the choice made is the
conservative one.
