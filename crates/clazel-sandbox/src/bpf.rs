//! Classic BPF instruction format and opcodes.
//!
//! Sources (Linux v6.12, vendored under `vendor/linux/`):
//! - `include/uapi/linux/bpf_common.h`: classes, sizes, modes, ALU and jump
//!   operations, sources, `BPF_MAXINSNS`.
//! - `include/uapi/linux/filter.h`: `struct sock_filter`, `BPF_RVAL`/`BPF_A`,
//!   `BPF_MISCOP`/`BPF_TAX`/`BPF_TXA`, `BPF_MEMWORDS`.
//! - `Documentation/networking/filter.rst`, "BPF engine and instruction set":
//!   "op:16, jt:8, jf:8, k:32".
//!
//! `tests/vendored.rs` checks every constant here against those headers.

/// `struct sock_filter`: one instruction (`filter.rst`: "op:16, jt:8, jf:8,
/// k:32").
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SockFilter {
    /// Opcode.
    pub code: u16,
    /// Jump offset if the condition is true.
    pub jt: u8,
    /// Jump offset if the condition is false.
    pub jf: u8,
    /// Operand.
    pub k: u32,
}

impl SockFilter {
    /// `BPF_STMT(code, k)`.
    pub const fn stmt(code: u16, k: u32) -> Self {
        Self {
            code,
            jt: 0,
            jf: 0,
            k,
        }
    }

    /// `BPF_JUMP(code, k, jt, jf)`.
    pub const fn jump(code: u16, k: u32, jt: u8, jf: u8) -> Self {
        Self { code, jt, jf, k }
    }
}

// Instruction classes (bpf_common.h).
/// Load into A.
pub const BPF_LD: u16 = 0x00;
/// Load into X.
pub const BPF_LDX: u16 = 0x01;
/// Store A to scratch memory.
pub const BPF_ST: u16 = 0x02;
/// Store X to scratch memory.
pub const BPF_STX: u16 = 0x03;
/// Arithmetic.
pub const BPF_ALU: u16 = 0x04;
/// Jump.
pub const BPF_JMP: u16 = 0x05;
/// Return.
pub const BPF_RET: u16 = 0x06;
/// Miscellaneous.
pub const BPF_MISC: u16 = 0x07;

// Load sizes (bpf_common.h).
/// 32-bit.
pub const BPF_W: u16 = 0x00;
/// 16-bit.
pub const BPF_H: u16 = 0x08;
/// 8-bit.
pub const BPF_B: u16 = 0x10;

// Load modes (bpf_common.h).
/// Immediate.
pub const BPF_IMM: u16 = 0x00;
/// Absolute offset into the data.
pub const BPF_ABS: u16 = 0x20;
/// Offset X + k into the data.
pub const BPF_IND: u16 = 0x40;
/// Scratch memory.
pub const BPF_MEM: u16 = 0x60;
/// Length of the data.
pub const BPF_LEN: u16 = 0x80;
/// `4 * (data[k] & 0xf)`.
pub const BPF_MSH: u16 = 0xa0;

// ALU operations (bpf_common.h).
/// A + src.
pub const BPF_ADD: u16 = 0x00;
/// A - src.
pub const BPF_SUB: u16 = 0x10;
/// A * src.
pub const BPF_MUL: u16 = 0x20;
/// A / src.
pub const BPF_DIV: u16 = 0x30;
/// A | src.
pub const BPF_OR: u16 = 0x40;
/// A & src.
pub const BPF_AND: u16 = 0x50;
/// A << src.
pub const BPF_LSH: u16 = 0x60;
/// A >> src.
pub const BPF_RSH: u16 = 0x70;
/// -A.
pub const BPF_NEG: u16 = 0x80;
/// A % src.
pub const BPF_MOD: u16 = 0x90;
/// A ^ src.
pub const BPF_XOR: u16 = 0xa0;

// Jump operations (bpf_common.h).
/// Unconditional.
pub const BPF_JA: u16 = 0x00;
/// A == src.
pub const BPF_JEQ: u16 = 0x10;
/// A > src (unsigned).
pub const BPF_JGT: u16 = 0x20;
/// A >= src (unsigned).
pub const BPF_JGE: u16 = 0x30;
/// A & src != 0.
pub const BPF_JSET: u16 = 0x40;

// Sources (bpf_common.h) and return values (filter.h).
/// The operand is the constant `k`.
pub const BPF_K: u16 = 0x00;
/// The operand is the X register.
pub const BPF_X: u16 = 0x08;
/// Return the accumulator (filter.h `BPF_A`).
pub const BPF_A: u16 = 0x10;

// Miscellaneous operations (filter.h).
/// X = A.
pub const BPF_TAX: u16 = 0x00;
/// A = X.
pub const BPF_TXA: u16 = 0x80;

/// Longest program the kernel accepts (bpf_common.h `BPF_MAXINSNS`).
pub const BPF_MAXINSNS: usize = 4096;
/// Words of scratch memory (filter.h `BPF_MEMWORDS`).
pub const BPF_MEMWORDS: usize = 16;
