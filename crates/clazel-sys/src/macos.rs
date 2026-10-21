//! macOS: the Seatbelt sandbox (`sandbox_init`).
//!
//! `sandbox_init` is deprecated, but it is what Chromium and Firefox still
//! use, and no replacement exists for a process that is not an App Sandbox
//! application. `libc` does not declare it, so it is declared here.

use std::ffi::{CString, c_char, c_int};
use std::fmt;

// SAFETY: man 3 sandbox_init and <sandbox.h>: `int sandbox_init(const char
// *profile, uint64_t flags, char **errorbuf)` and `void
// sandbox_free_error(char *errorbuf)`. The declarations below match those
// prototypes (`c_char`, `c_int` and `u64` have the C sizes on every macOS
// target), the functions live in libSystem, which Rust's standard library
// links, and neither is `pub` or declared `safe`, so every call needs its own
// `unsafe` block.
unsafe extern "C" {
    fn sandbox_init(profile: *const c_char, flags: u64, errorbuf: *mut *mut c_char) -> c_int;
    fn sandbox_free_error(errorbuf: *mut c_char);
}

/// Why a Seatbelt profile was not applied.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SandboxError {
    /// The profile text contains a NUL byte, so it cannot be a C string.
    InteriorNul,
    /// `sandbox_init` refused the profile (a syntax error, or the process is
    /// already sandboxed in a way that forbids it). The message it returns is
    /// freed, not read: reading it would need a second kind of `unsafe` call.
    Rejected,
}

impl fmt::Display for SandboxError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            SandboxError::InteriorNul => f.write_str("sandbox profile contains a NUL byte"),
            SandboxError::Rejected => f.write_str("sandbox_init rejected the profile"),
        }
    }
}

impl std::error::Error for SandboxError {}

/// `sandbox_init(profile, 0, ..)`: parse `profile`, written in the Seatbelt
/// profile language (SBPL), and confine this process to it, for good. A
/// process cannot leave or loosen a sandbox once it is in one.
pub fn sandbox_init_profile(profile: &str) -> Result<(), SandboxError> {
    let text = CString::new(profile).map_err(|_| SandboxError::InteriorNul)?;
    let text_ptr: *const c_char = text.as_ptr();
    let mut error: *mut c_char = std::ptr::null_mut();
    let error_slot: *mut *mut c_char = &raw mut error;
    // SAFETY: man 3 sandbox_init: `profile` must be a NUL-terminated string
    // and, with `flags` 0, it is SBPL source (SANDBOX_NAMED is not set);
    // `errorbuf` must be writable and receives a heap string on failure. The
    // arguments have the types of the declaration above: `text_ptr` points to
    // the NUL-terminated buffer of `text`, which lives to the end of this
    // function, and `error_slot` points to the live local `error`.
    let rc = unsafe { sandbox_init(text_ptr, 0, error_slot) };
    if rc == 0 {
        return Ok(());
    }
    if !error.is_null() {
        // SAFETY: man 3 sandbox_init: a non-NULL `*errorbuf` set by a failed
        // sandbox_init was allocated by it and must be released with
        // sandbox_free_error, once. `error` was set by that call and is not
        // used again, nor copied anywhere.
        unsafe { sandbox_free_error(error) };
    }
    Err(SandboxError::Rejected)
}

#[cfg(test)]
mod tests {
    use super::{SandboxError, sandbox_init_profile};

    #[test]
    fn a_profile_with_a_nul_never_reaches_the_os() {
        assert_eq!(
            sandbox_init_profile("(version 1)\0(deny default)"),
            Err(SandboxError::InteriorNul)
        );
    }

    // Miri cannot run foreign calls. An unparsable profile is refused before
    // any sandbox is entered, so this does not confine the test process.
    #[test]
    #[cfg_attr(miri, ignore)]
    fn an_unparsable_profile_is_rejected() {
        assert_eq!(
            sandbox_init_profile("(version 1"),
            Err(SandboxError::Rejected)
        );
    }
}
