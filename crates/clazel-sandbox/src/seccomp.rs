//! The seccomp-BPF program generator.
//!
//! Sources (Linux v6.12, vendored under `vendor/linux/`):
//! - `Documentation/userspace-api/seccomp_filter.rst`, "Usage" (the program
//!   runs over `struct seccomp_data`), "Return values" (precedence of
//!   actions) and "Pitfalls" ("Always check the arch value!").
//! - `include/uapi/linux/seccomp.h`: `struct seccomp_data`, `SECCOMP_RET_*`.
//! - `include/uapi/linux/audit.h`: `AUDIT_ARCH_*` (see [`crate::syscalls`]).
//!
//! The program has this shape, for allowlist numbers `n_0 .. n_{N-1}`:
//!
//! ```text
//!  0        ld   [arch]                     ; seccomp_data.arch
//!  1        jeq  AUDIT_ARCH, +1, +0         ; right architecture: skip the kill
//!  2        ret  SECCOMP_RET_KILL_PROCESS   ; wrong architecture
//!  3        ld   [nr]                       ; seccomp_data.nr
//!  4+i      jeq  n_i, (N - i), +0           ; allowed: jump to the final ret
//!  4+N      ret  SECCOMP_RET_KILL_PROCESS   ; not on the list
//!  5+N      ret  SECCOMP_RET_ALLOW
//! ```
//!
//! Modelling choices:
//! - The architecture is checked first, before the syscall number is read
//!   (`seccomp_filter.rst`, "Pitfalls"). Because syscall numbers are
//!   compared for equality over the full 32 bits, an x32 call (number with
//!   bit 30 set) matches nothing on the list and is killed.
//! - Everything not allowed is `SECCOMP_RET_KILL_PROCESS` (the highest
//!   precedence action, so no later filter can soften it) rather than an
//!   errno: a renderer that attempts a forbidden call is compromised or
//!   broken, and should not continue.

use crate::bpf::SockFilter;
use crate::bpf::{BPF_ABS, BPF_JEQ, BPF_JMP, BPF_K, BPF_LD, BPF_MAXINSNS, BPF_RET, BPF_W};
use crate::syscalls::{self, Arch};

/// `SECCOMP_RET_KILL_PROCESS` (`seccomp.h`).
pub const SECCOMP_RET_KILL_PROCESS: u32 = 0x8000_0000;
/// `SECCOMP_RET_KILL_THREAD` (`seccomp.h`).
pub const SECCOMP_RET_KILL_THREAD: u32 = 0x0000_0000;
/// `SECCOMP_RET_TRAP` (`seccomp.h`).
pub const SECCOMP_RET_TRAP: u32 = 0x0003_0000;
/// `SECCOMP_RET_ERRNO` (`seccomp.h`).
pub const SECCOMP_RET_ERRNO: u32 = 0x0005_0000;
/// `SECCOMP_RET_USER_NOTIF` (`seccomp.h`).
pub const SECCOMP_RET_USER_NOTIF: u32 = 0x7fc0_0000;
/// `SECCOMP_RET_TRACE` (`seccomp.h`).
pub const SECCOMP_RET_TRACE: u32 = 0x7ff0_0000;
/// `SECCOMP_RET_LOG` (`seccomp.h`).
pub const SECCOMP_RET_LOG: u32 = 0x7ffc_0000;
/// `SECCOMP_RET_ALLOW` (`seccomp.h`).
pub const SECCOMP_RET_ALLOW: u32 = 0x7fff_0000;
/// `SECCOMP_RET_ACTION_FULL` (`seccomp.h`): the bits that select the action.
pub const SECCOMP_RET_ACTION_FULL: u32 = 0xffff_0000;

/// Byte offset of `seccomp_data.nr` (`struct seccomp_data`, `seccomp.h`).
pub const OFFSET_NR: u32 = 0;
/// Byte offset of `seccomp_data.arch`.
pub const OFFSET_ARCH: u32 = 4;
/// `sizeof(struct seccomp_data)`: `int nr; __u32 arch; __u64 ip; __u64 args[6]`.
pub const SECCOMP_DATA_LEN: u32 = 64;

/// Why a program could not be generated.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum GenError {
    /// A conditional jump offset is 8 bits, so at most 255 syscall numbers
    /// fit in this straight-line layout.
    TooManySyscalls,
}

/// Generate the program that allows exactly the syscalls `numbers` when
/// `seccomp_data.arch` is `audit_arch`, and kills the process otherwise.
pub fn generate(audit_arch: u32, numbers: &[u32]) -> Result<Vec<SockFilter>, GenError> {
    let n = numbers.len();
    // The jump from entry `i` to the final `ret ALLOW` is `n - i` <= n.
    if n > usize::from(u8::MAX) {
        return Err(GenError::TooManySyscalls);
    }
    let ld_w_abs = BPF_LD | BPF_W | BPF_ABS;
    let jeq_k = BPF_JMP | BPF_JEQ | BPF_K;
    let ret_k = BPF_RET | BPF_K;
    let mut prog = Vec::with_capacity(n.saturating_add(6));
    // 0-2: the architecture check comes first.
    prog.push(SockFilter::stmt(ld_w_abs, OFFSET_ARCH));
    prog.push(SockFilter::jump(jeq_k, audit_arch, 1, 0));
    prog.push(SockFilter::stmt(ret_k, SECCOMP_RET_KILL_PROCESS));
    // 3: then the syscall number.
    prog.push(SockFilter::stmt(ld_w_abs, OFFSET_NR));
    // 4+i: one comparison per allowed number.
    for (i, nr) in numbers.iter().enumerate() {
        let to_allow = n
            .checked_sub(i)
            .and_then(|d| u8::try_from(d).ok())
            .ok_or(GenError::TooManySyscalls)?;
        prog.push(SockFilter::jump(jeq_k, *nr, to_allow, 0));
    }
    prog.push(SockFilter::stmt(ret_k, SECCOMP_RET_KILL_PROCESS));
    prog.push(SockFilter::stmt(ret_k, SECCOMP_RET_ALLOW));
    debug_assert!(prog.len() <= BPF_MAXINSNS);
    Ok(prog)
}

/// The renderer's seccomp program for `arch`, from [`syscalls::ALLOWLIST`].
pub fn renderer_program(arch: Arch) -> Result<Vec<SockFilter>, GenError> {
    generate(arch.audit_arch(), &syscalls::numbers(arch))
}
