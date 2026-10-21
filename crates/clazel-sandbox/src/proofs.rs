//! Kani harnesses (Tier 1). Compiled only under `cargo kani`.
//!
//! What they establish, with the interpreter in [`crate::interp`] as the model
//! of the kernel:
//!
//! - [`generate`] never panics, and its output validates, for any
//!   architecture value and any allowlist of up to three numbers (the layout
//!   does not depend on the count beyond the loop, and the harness covers
//!   0 to 3 iterations; [`generator_limits`] covers the 255/256 boundary).
//! - For any such allowlist and any syscall number, architecture and
//!   arguments: the generated program returns `SECCOMP_RET_ALLOW` exactly when
//!   the architecture matches and the number is in the list, and
//!   `SECCOMP_RET_KILL_PROCESS` otherwise.
//! - For the real allowlist, on x86-64 and on aarch64: the same, for **every**
//!   32-bit syscall number (so, in particular, every number below 1024), the
//!   right architecture, and for every other architecture value (so, in
//!   particular, the other supported architecture).
//! - The validator and interpreter never panic, on any program of up to two
//!   instructions with any field values, over any data.
//!
//! `#[kani::unwind]` bounds are the loop lengths plus one; Kani reports an
//! unwinding failure rather than a pass if one is too small.

use crate::bpf::SockFilter;
use crate::interp::{SeccompData, run, validate};
use crate::seccomp::{
    GenError, SECCOMP_RET_ALLOW, SECCOMP_RET_KILL_PROCESS, generate, renderer_program,
};
use crate::syscalls::{self, Arch};

/// An allowlist of up to three symbolic numbers, in `buf[..len]`.
fn symbolic_list(buf: &[u32; 3], len: usize) -> &[u32] {
    buf.get(..len).unwrap_or(&[])
}

#[kani::proof]
#[kani::unwind(8)]
fn generator_total_and_valid() {
    let arch: u32 = kani::any();
    let buf: [u32; 3] = kani::any();
    let len: usize = kani::any();
    kani::assume(len <= 3);
    let list = symbolic_list(&buf, len);
    match generate(arch, list) {
        Ok(prog) => {
            assert!(prog.len() == len + 6);
            assert!(validate(&prog).is_ok());
        }
        Err(_) => assert!(false),
    }
}

#[kani::proof]
#[kani::unwind(8)]
fn generated_program_allows_exactly_the_list() {
    let arch: u32 = kani::any();
    let buf: [u32; 3] = kani::any();
    let len: usize = kani::any();
    kani::assume(len <= 3);
    let list = symbolic_list(&buf, len);
    let nr: u32 = kani::any();
    let data_arch: u32 = kani::any();
    let ip: u64 = kani::any();
    let args: [u64; 6] = kani::any();
    let data = SeccompData {
        nr,
        arch: data_arch,
        instruction_pointer: ip,
        args,
    };
    let Ok(prog) = generate(arch, list) else {
        assert!(false);
        return;
    };
    let expected = if data_arch == arch && list.contains(&nr) {
        SECCOMP_RET_ALLOW
    } else {
        SECCOMP_RET_KILL_PROCESS
    };
    assert!(run(&prog, &data) == Ok(expected));
}

#[kani::proof]
#[kani::unwind(260)]
fn generator_limits() {
    let big = [0u32; 256];
    assert!(generate(0, &big) == Err(GenError::TooManySyscalls));
    let max = [0u32; 255];
    match generate(0, &max) {
        Ok(prog) => assert!(validate(&prog).is_ok()),
        Err(_) => assert!(false),
    }
}

/// The real allowlist for `arch`: every syscall number, right architecture.
fn check_real_allowlist(arch: Arch) {
    let Ok(prog) = renderer_program(arch) else {
        assert!(false);
        return;
    };
    assert!(validate(&prog).is_ok());
    let nr: u32 = kani::any();
    let allowed = run(&prog, &SeccompData::new(nr, arch.audit_arch()));
    if syscalls::is_allowed(arch, nr) {
        assert!(allowed == Ok(SECCOMP_RET_ALLOW));
    } else {
        assert!(allowed == Ok(SECCOMP_RET_KILL_PROCESS));
    }
    // Any other architecture value, whatever the syscall number.
    let other: u32 = kani::any();
    kani::assume(other != arch.audit_arch());
    assert!(run(&prog, &SeccompData::new(nr, other)) == Ok(SECCOMP_RET_KILL_PROCESS));
}

#[kani::proof]
#[kani::unwind(40)]
fn real_allowlist_x86_64() {
    check_real_allowlist(Arch::X86_64);
}

#[kani::proof]
#[kani::unwind(40)]
fn real_allowlist_aarch64() {
    check_real_allowlist(Arch::Aarch64);
}

#[kani::proof]
#[kani::unwind(6)]
fn interpreter_never_panics() {
    let insns: [SockFilter; 2] = [
        SockFilter {
            code: kani::any(),
            jt: kani::any(),
            jf: kani::any(),
            k: kani::any(),
        },
        SockFilter {
            code: kani::any(),
            jt: kani::any(),
            jf: kani::any(),
            k: kani::any(),
        },
    ];
    let len: usize = kani::any();
    kani::assume(len <= 2);
    let prog = insns.get(..len).unwrap_or(&[]);
    let data = SeccompData {
        nr: kani::any(),
        arch: kani::any(),
        instruction_pointer: kani::any(),
        args: kani::any(),
    };
    let _ = validate(prog);
    let _ = run(prog, &data);
}
