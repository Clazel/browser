//! A validator and interpreter for classic BPF programs run over
//! `struct seccomp_data`.
//!
//! This models the kernel, so it is part of the trusted computing base: the
//! harnesses show that the generated programs do what the policy says *as
//! this interpreter runs them*, and nothing more.
//!
//! Sources (Linux v6.12, vendored under `vendor/linux/`):
//! - `Documentation/networking/filter.rst`, "BPF engine and instruction set":
//!   the registers A and X (32-bit), the 16-word scratch memory `M[]`, the
//!   instruction tables and addressing modes, and "op:16, jt:8, jf:8, k:32".
//! - `Documentation/userspace-api/seccomp_filter.rst`, "Usage": the program
//!   runs over `struct seccomp_data` and returns an action.
//! - `include/uapi/linux/bpf_common.h`, `filter.h`: opcode values and
//!   `BPF_MAXINSNS`, `BPF_MEMWORDS`.
//!
//! Modelling choices (the documents above do not settle these; the kernel
//! sources that do, `kernel/seccomp.c` `seccomp_check_filter` and
//! `net/core/filter.c` `bpf_check_classic`, are not vendored, so each choice
//! below is the conservative one: reject, or fail the run):
//! - A seccomp filter may use only: `ld`/`ldx` of a word (absolute, immediate,
//!   scratch memory, or length), `st`/`stx`, ALU, jumps, `ret` and `tax`/
//!   `txa`. Byte and half-word loads, indirect loads, `msh` and the socket
//!   extensions (negative offsets) are rejected by [`validate`].
//! - An absolute load must be 4-byte aligned and inside the 64-byte
//!   `seccomp_data`. The data is little-endian (both supported architectures
//!   are), laid out as `nr`, `arch`, `instruction_pointer` (low word first),
//!   then six 64-bit arguments (low word first).
//! - Division or modulus by the constant 0, a shift by a constant of 32 or
//!   more, and a jump or fall-through leaving the program are rejected by
//!   [`validate`]; the same faults through X (or an unvalidated program) make
//!   [`run`] return an error, which callers treat as "not allowed".
//! - Scratch memory starts zeroed. The kernel rejects reading a word before
//!   it is written, so a validated kernel program never observes the
//!   difference.
//! - Jumps are forward only (offsets are unsigned), so a program of `L`
//!   instructions executes at most `L` of them.

use crate::bpf::{
    BPF_A, BPF_ABS, BPF_ADD, BPF_ALU, BPF_AND, BPF_DIV, BPF_IMM, BPF_JA, BPF_JEQ, BPF_JGE, BPF_JGT,
    BPF_JMP, BPF_JSET, BPF_LD, BPF_LDX, BPF_LEN, BPF_LSH, BPF_MAXINSNS, BPF_MEM, BPF_MEMWORDS,
    BPF_MISC, BPF_MOD, BPF_MUL, BPF_NEG, BPF_OR, BPF_RET, BPF_RSH, BPF_ST, BPF_STX, BPF_SUB,
    BPF_TAX, BPF_TXA, BPF_X, BPF_XOR, SockFilter,
};
use crate::seccomp::SECCOMP_DATA_LEN;

/// `struct seccomp_data`, the input a seccomp program runs over.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SeccompData {
    /// The system call number (`int nr`, as 32 bits).
    pub nr: u32,
    /// `AUDIT_ARCH_*`.
    pub arch: u32,
    /// The instruction pointer at the time of the call.
    pub instruction_pointer: u64,
    /// The six arguments.
    pub args: [u64; 6],
}

impl SeccompData {
    /// A call of `nr` under `arch` with zero arguments.
    pub const fn new(nr: u32, arch: u32) -> Self {
        Self {
            nr,
            arch,
            instruction_pointer: 0,
            args: [0; 6],
        }
    }

    /// The 32-bit words of the structure, in memory order.
    fn words(&self) -> [u32; 16] {
        let ip = self.instruction_pointer;
        let [a0, a1, a2, a3, a4, a5] = self.args;
        let lo = |v: u64| u32::try_from(v & 0xffff_ffff).unwrap_or(0);
        let hi = |v: u64| u32::try_from(v >> 32).unwrap_or(0);
        [
            self.nr,
            self.arch,
            lo(ip),
            hi(ip),
            lo(a0),
            hi(a0),
            lo(a1),
            hi(a1),
            lo(a2),
            hi(a2),
            lo(a3),
            hi(a3),
            lo(a4),
            hi(a4),
            lo(a5),
            hi(a5),
        ]
    }

    /// The word at byte offset `off`, if aligned and inside the structure.
    fn word_at(&self, off: u32) -> Option<u32> {
        if !off.is_multiple_of(4) || off >= SECCOMP_DATA_LEN {
            return None;
        }
        let idx = usize::try_from(off / 4).ok()?;
        self.words().get(idx).copied()
    }
}

/// Why a program was rejected or a run failed.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BpfError {
    /// Empty, or longer than `BPF_MAXINSNS`.
    BadLength,
    /// An opcode a seccomp filter may not use (or that does not exist).
    BadOpcode,
    /// A load outside `seccomp_data` or not word aligned.
    BadLoad,
    /// A scratch-memory index of 16 or more.
    BadMemory,
    /// A jump or fall-through leaving the program.
    BadJump,
    /// Division or modulus by zero, or a shift of 32 or more.
    BadArithmetic,
    /// The last instruction is not a `ret`.
    NoReturn,
}

/// A decoded instruction (only those a seccomp filter may use).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Insn {
    LdAbs(u32),
    LdImm(u32),
    LdMem(u32),
    LdLen,
    LdxImm(u32),
    LdxMem(u32),
    LdxLen,
    St(u32),
    Stx(u32),
    /// ALU operation `op` (a `BPF_*` ALU constant), source X or K.
    Alu(u16, bool, u32),
    Neg,
    Ja(u32),
    /// Conditional jump `op`, source X or K, constant, jt, jf.
    Jmp(u16, bool, u32, u8, u8),
    RetK(u32),
    RetA,
    Tax,
    Txa,
}

fn decode(i: &SockFilter) -> Option<Insn> {
    let code = i.code;
    if code > 0xff {
        return None;
    }
    let k = i.k;
    match code & 0x07 {
        BPF_LD => match code & 0xf8 {
            m if m == BPF_ABS => Some(Insn::LdAbs(k)),
            m if m == BPF_IMM => Some(Insn::LdImm(k)),
            m if m == BPF_MEM => Some(Insn::LdMem(k)),
            m if m == BPF_LEN => Some(Insn::LdLen),
            _ => None,
        },
        BPF_LDX => match code & 0xf8 {
            m if m == BPF_IMM => Some(Insn::LdxImm(k)),
            m if m == BPF_MEM => Some(Insn::LdxMem(k)),
            m if m == BPF_LEN => Some(Insn::LdxLen),
            _ => None,
        },
        BPF_ST if code & 0xf8 == 0 => Some(Insn::St(k)),
        BPF_STX if code & 0xf8 == 0 => Some(Insn::Stx(k)),
        BPF_ALU => {
            let op = code & 0xf0;
            let x = code & BPF_X != 0;
            match op {
                BPF_ADD | BPF_SUB | BPF_MUL | BPF_DIV | BPF_OR | BPF_AND | BPF_LSH | BPF_RSH
                | BPF_MOD | BPF_XOR => Some(Insn::Alu(op, x, k)),
                BPF_NEG if !x => Some(Insn::Neg),
                _ => None,
            }
        }
        BPF_JMP => {
            let op = code & 0xf0;
            let x = code & BPF_X != 0;
            match op {
                BPF_JA if !x => Some(Insn::Ja(k)),
                BPF_JEQ | BPF_JGT | BPF_JGE | BPF_JSET => Some(Insn::Jmp(op, x, k, i.jt, i.jf)),
                _ => None,
            }
        }
        BPF_RET => match code & 0xf8 {
            0x00 => Some(Insn::RetK(k)),
            m if m == BPF_A => Some(Insn::RetA),
            _ => None,
        },
        BPF_MISC => match code & 0xf8 {
            m if m == BPF_TAX => Some(Insn::Tax),
            m if m == BPF_TXA => Some(Insn::Txa),
            _ => None,
        },
        _ => None,
    }
}

/// Absolute index of the jump target `pc + 1 + off`, if inside `len`.
fn target(pc: usize, off: u32, len: usize) -> Option<usize> {
    let off = usize::try_from(off).ok()?;
    let t = pc.checked_add(1)?.checked_add(off)?;
    (t < len).then_some(t)
}

/// Check a program the way the kernel's loader would for a seccomp filter
/// (see the modelling choices in the module documentation).
pub fn validate(prog: &[SockFilter]) -> Result<(), BpfError> {
    let len = prog.len();
    if len == 0 || len > BPF_MAXINSNS {
        return Err(BpfError::BadLength);
    }
    for (pc, i) in prog.iter().enumerate() {
        match decode(i).ok_or(BpfError::BadOpcode)? {
            Insn::LdAbs(k) => {
                if !k.is_multiple_of(4) || k >= SECCOMP_DATA_LEN {
                    return Err(BpfError::BadLoad);
                }
            }
            Insn::LdMem(k) | Insn::LdxMem(k) | Insn::St(k) | Insn::Stx(k) => {
                if usize::try_from(k).map_or(true, |k| k >= BPF_MEMWORDS) {
                    return Err(BpfError::BadMemory);
                }
            }
            Insn::Alu(op, false, k) => {
                if (op == BPF_DIV || op == BPF_MOD) && k == 0 {
                    return Err(BpfError::BadArithmetic);
                }
                if (op == BPF_LSH || op == BPF_RSH) && k >= 32 {
                    return Err(BpfError::BadArithmetic);
                }
            }
            Insn::Ja(k) => {
                target(pc, k, len).ok_or(BpfError::BadJump)?;
            }
            Insn::Jmp(_, _, _, jt, jf) => {
                target(pc, u32::from(jt), len).ok_or(BpfError::BadJump)?;
                target(pc, u32::from(jf), len).ok_or(BpfError::BadJump)?;
            }
            Insn::LdImm(_)
            | Insn::LdLen
            | Insn::LdxImm(_)
            | Insn::LdxLen
            | Insn::Alu(_, true, _)
            | Insn::Neg
            | Insn::RetK(_)
            | Insn::RetA
            | Insn::Tax
            | Insn::Txa => {}
        }
    }
    match prog.last().and_then(decode) {
        Some(Insn::RetK(_) | Insn::RetA) => Ok(()),
        _ => Err(BpfError::NoReturn),
    }
}

/// Run `prog` over `data` and return the program's return value (the seccomp
/// action and data). Faults return an error and must be treated as "not
/// allowed".
pub fn run(prog: &[SockFilter], data: &SeccompData) -> Result<u32, BpfError> {
    let mut a: u32 = 0;
    let mut x: u32 = 0;
    let mut mem = [0u32; BPF_MEMWORDS];
    let mut pc: usize = 0;
    // Forward-only jumps: at most `prog.len()` steps.
    for _ in 0..prog.len() {
        let insn = prog.get(pc).and_then(decode).ok_or(BpfError::BadOpcode)?;
        let mut next = pc.checked_add(1).ok_or(BpfError::BadJump)?;
        match insn {
            Insn::LdAbs(k) => a = data.word_at(k).ok_or(BpfError::BadLoad)?,
            Insn::LdImm(k) => a = k,
            Insn::LdMem(k) => a = mem_get(&mem, k)?,
            Insn::LdLen => a = SECCOMP_DATA_LEN,
            Insn::LdxImm(k) => x = k,
            Insn::LdxMem(k) => x = mem_get(&mem, k)?,
            Insn::LdxLen => x = SECCOMP_DATA_LEN,
            Insn::St(k) => mem_set(&mut mem, k, a)?,
            Insn::Stx(k) => mem_set(&mut mem, k, x)?,
            Insn::Alu(op, use_x, k) => {
                let src = if use_x { x } else { k };
                a = alu(op, a, src)?;
            }
            Insn::Neg => a = a.wrapping_neg(),
            Insn::Ja(k) => next = target(pc, k, prog.len()).ok_or(BpfError::BadJump)?,
            Insn::Jmp(op, use_x, k, jt, jf) => {
                let src = if use_x { x } else { k };
                let taken = match op {
                    BPF_JEQ => a == src,
                    BPF_JGT => a > src,
                    BPF_JGE => a >= src,
                    _ => a & src != 0,
                };
                let off = if taken { jt } else { jf };
                next = target(pc, u32::from(off), prog.len()).ok_or(BpfError::BadJump)?;
            }
            Insn::RetK(k) => return Ok(k),
            Insn::RetA => return Ok(a),
            Insn::Tax => x = a,
            Insn::Txa => a = x,
        }
        pc = next;
    }
    Err(BpfError::BadJump)
}

fn mem_get(mem: &[u32; BPF_MEMWORDS], k: u32) -> Result<u32, BpfError> {
    let idx = usize::try_from(k).map_err(|_| BpfError::BadMemory)?;
    mem.get(idx).copied().ok_or(BpfError::BadMemory)
}

fn mem_set(mem: &mut [u32; BPF_MEMWORDS], k: u32, v: u32) -> Result<(), BpfError> {
    let idx = usize::try_from(k).map_err(|_| BpfError::BadMemory)?;
    *mem.get_mut(idx).ok_or(BpfError::BadMemory)? = v;
    Ok(())
}

fn alu(op: u16, a: u32, src: u32) -> Result<u32, BpfError> {
    Ok(match op {
        BPF_ADD => a.wrapping_add(src),
        BPF_SUB => a.wrapping_sub(src),
        BPF_MUL => a.wrapping_mul(src),
        BPF_DIV => a.checked_div(src).ok_or(BpfError::BadArithmetic)?,
        BPF_MOD => a.checked_rem(src).ok_or(BpfError::BadArithmetic)?,
        BPF_OR => a | src,
        BPF_AND => a & src,
        BPF_XOR => a ^ src,
        BPF_LSH => a.checked_shl(src).ok_or(BpfError::BadArithmetic)?,
        BPF_RSH => a.checked_shr(src).ok_or(BpfError::BadArithmetic)?,
        _ => return Err(BpfError::BadOpcode),
    })
}
