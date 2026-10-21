//! The Landlock ruleset: no filesystem access at all.
//!
//! Sources (Linux v6.12, vendored under `vendor/linux/`):
//! - `include/uapi/linux/landlock.h`: the `LANDLOCK_ACCESS_FS_*`,
//!   `LANDLOCK_ACCESS_NET_*` and `LANDLOCK_SCOPE_*` bits.
//! - `Documentation/userspace-api/landlock.rst`, "Landlock ABI versions" and
//!   the sections "File renaming and linking (ABI < 2)", "File truncation
//!   (ABI < 3)", "TCP bind and connect (ABI < 4)", "Device IOCTL (ABI < 5)",
//!   "Abstract UNIX socket (ABI < 6)" and "Signal (ABI < 6)": which right
//!   appeared in which ABI.
//!
//! A Landlock ruleset *handles* a set of access rights and then *allows*
//! some of them beneath chosen paths. Anything handled and not allowed is
//! denied. This policy handles every right of every ABI and adds no rule, so
//! the sandboxed process has no filesystem access (and no TCP bind or
//! connect, abstract-socket connect or signal to another domain).
//!
//! Modelling choice: handling a right the running kernel does not know makes
//! `landlock_create_ruleset` fail with `EINVAL`, so the applier (item 2.15)
//! asks the kernel for its ABI version and calls [`Ruleset::for_abi`], which
//! drops the rights newer than that ABI. A kernel older than ABI 1, or one
//! with Landlock disabled, gives no filesystem protection from this module;
//! the namespaces and seccomp program are the other layers.

/// `LANDLOCK_ACCESS_FS_EXECUTE`.
pub const ACCESS_FS_EXECUTE: u64 = 1 << 0;
/// `LANDLOCK_ACCESS_FS_WRITE_FILE`.
pub const ACCESS_FS_WRITE_FILE: u64 = 1 << 1;
/// `LANDLOCK_ACCESS_FS_READ_FILE`.
pub const ACCESS_FS_READ_FILE: u64 = 1 << 2;
/// `LANDLOCK_ACCESS_FS_READ_DIR`.
pub const ACCESS_FS_READ_DIR: u64 = 1 << 3;
/// `LANDLOCK_ACCESS_FS_REMOVE_DIR`.
pub const ACCESS_FS_REMOVE_DIR: u64 = 1 << 4;
/// `LANDLOCK_ACCESS_FS_REMOVE_FILE`.
pub const ACCESS_FS_REMOVE_FILE: u64 = 1 << 5;
/// `LANDLOCK_ACCESS_FS_MAKE_CHAR`.
pub const ACCESS_FS_MAKE_CHAR: u64 = 1 << 6;
/// `LANDLOCK_ACCESS_FS_MAKE_DIR`.
pub const ACCESS_FS_MAKE_DIR: u64 = 1 << 7;
/// `LANDLOCK_ACCESS_FS_MAKE_REG`.
pub const ACCESS_FS_MAKE_REG: u64 = 1 << 8;
/// `LANDLOCK_ACCESS_FS_MAKE_SOCK`.
pub const ACCESS_FS_MAKE_SOCK: u64 = 1 << 9;
/// `LANDLOCK_ACCESS_FS_MAKE_FIFO`.
pub const ACCESS_FS_MAKE_FIFO: u64 = 1 << 10;
/// `LANDLOCK_ACCESS_FS_MAKE_BLOCK`.
pub const ACCESS_FS_MAKE_BLOCK: u64 = 1 << 11;
/// `LANDLOCK_ACCESS_FS_MAKE_SYM`.
pub const ACCESS_FS_MAKE_SYM: u64 = 1 << 12;
/// `LANDLOCK_ACCESS_FS_REFER` (ABI 2).
pub const ACCESS_FS_REFER: u64 = 1 << 13;
/// `LANDLOCK_ACCESS_FS_TRUNCATE` (ABI 3).
pub const ACCESS_FS_TRUNCATE: u64 = 1 << 14;
/// `LANDLOCK_ACCESS_FS_IOCTL_DEV` (ABI 5).
pub const ACCESS_FS_IOCTL_DEV: u64 = 1 << 15;
/// `LANDLOCK_ACCESS_NET_BIND_TCP` (ABI 4).
pub const ACCESS_NET_BIND_TCP: u64 = 1 << 0;
/// `LANDLOCK_ACCESS_NET_CONNECT_TCP` (ABI 4).
pub const ACCESS_NET_CONNECT_TCP: u64 = 1 << 1;
/// `LANDLOCK_SCOPE_ABSTRACT_UNIX_SOCKET` (ABI 6).
pub const SCOPE_ABSTRACT_UNIX_SOCKET: u64 = 1 << 0;
/// `LANDLOCK_SCOPE_SIGNAL` (ABI 6).
pub const SCOPE_SIGNAL: u64 = 1 << 1;

/// Every filesystem right of ABI 1 (bits 0 to 12).
pub const FS_ABI_1: u64 = (1 << 13) - 1;
/// Every filesystem right of ABI 2.
pub const FS_ABI_2: u64 = FS_ABI_1 | ACCESS_FS_REFER;
/// Every filesystem right of ABI 3.
pub const FS_ABI_3: u64 = FS_ABI_2 | ACCESS_FS_TRUNCATE;
/// Every filesystem right of ABI 5 (ABI 4 adds none).
pub const FS_ABI_5: u64 = FS_ABI_3 | ACCESS_FS_IOCTL_DEV;
/// Every network right (ABI 4).
pub const NET_ABI_4: u64 = ACCESS_NET_BIND_TCP | ACCESS_NET_CONNECT_TCP;
/// Every scope (ABI 6).
pub const SCOPE_ABI_6: u64 = SCOPE_ABSTRACT_UNIX_SOCKET | SCOPE_SIGNAL;

/// The newest Landlock ABI this module knows (the one of Linux v6.12).
pub const LATEST_ABI: u32 = 6;

/// A rule allowing `allowed_access` beneath `path` (`LANDLOCK_RULE_PATH_BENEATH`).
/// The renderer policy has none; the type exists so that the policy's
/// emptiness is a checked fact about data, not an absence.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PathBeneathRule {
    /// The directory or file the rule applies beneath.
    pub path: &'static str,
    /// The rights allowed there.
    pub allowed_access: u64,
}

/// A Landlock ruleset: what it handles and what it then allows.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Ruleset {
    /// `handled_access_fs`.
    pub handled_access_fs: u64,
    /// `handled_access_net`.
    pub handled_access_net: u64,
    /// `scoped`.
    pub scoped: u64,
    /// Path rules; empty means nothing is allowed.
    pub path_rules: &'static [PathBeneathRule],
}

/// The renderer's ruleset for the newest ABI: everything handled, nothing
/// allowed.
pub const RENDERER: Ruleset = Ruleset {
    handled_access_fs: FS_ABI_5,
    handled_access_net: NET_ABI_4,
    scoped: SCOPE_ABI_6,
    path_rules: &[],
};

impl Ruleset {
    /// The ruleset restricted to the rights `abi` knows, for a kernel that
    /// reports that Landlock ABI version. ABI 0 handles nothing.
    pub const fn for_abi(self, abi: u32) -> Ruleset {
        let fs = match abi {
            0 => 0,
            1 => FS_ABI_1,
            2 => FS_ABI_2,
            3 | 4 => FS_ABI_3,
            _ => FS_ABI_5,
        };
        let net = if abi >= 4 { NET_ABI_4 } else { 0 };
        let scoped = if abi >= 6 { SCOPE_ABI_6 } else { 0 };
        Ruleset {
            handled_access_fs: self.handled_access_fs & fs,
            handled_access_net: self.handled_access_net & net,
            scoped: self.scoped & scoped,
            path_rules: self.path_rules,
        }
    }

    /// No right is allowed anywhere: the process has no filesystem access.
    pub const fn allows_nothing(&self) -> bool {
        self.path_rules.is_empty()
    }
}
