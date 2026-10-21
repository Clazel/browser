//! The macOS Seatbelt (SBPL) profile: `(deny default)` plus the minimum to
//! run.
//!
//! SBPL is Apple's undocumented Scheme-based profile language; there is no
//! standard to cite and nothing here is checked against a reference. The
//! profile is data, rendered by [`render`] from [`RENDERER`], and the
//! integration tests of item 2.16 (a real sandboxed process trying to open
//! files and sockets) are the only check that it denies what it should and
//! allows what a renderer needs. `tests/policies.rs` checks only the shape:
//! it begins `(version 1)` then `(deny default)`, and no rule mentions a
//! file, network, process-creation or process-execution operation.
//!
//! Modelling choices:
//! - The profile is applied (item 2.15) after the process has started and
//!   holds its socket, so it needs no `process-exec`, no `file-read*` for the
//!   binary or libraries (already mapped) and no `network*` (the inherited
//!   socket is used through its descriptor, which `(deny default)` does not
//!   revoke).
//! - Each rule is "allow `operation` with these filters". The three allowed
//!   operations are the least the Rust runtime and allocator are known to
//!   query; if a renderer needs another, 2.16 will show a denial and the rule
//!   is added here with its reason.

/// One `(allow ...)` rule.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Rule {
    /// The SBPL operation, such as `sysctl-read`.
    pub operation: &'static str,
    /// Filters, each already a complete SBPL form such as `(target self)`.
    pub filters: &'static [&'static str],
    /// Why the renderer needs it.
    pub reason: &'static str,
}

/// The rules after `(deny default)`.
pub const RENDERER: &[Rule] = &[
    Rule {
        operation: "signal",
        filters: &["(target self)"],
        reason: "the Rust runtime may raise a signal on itself (abort on panic)",
    },
    Rule {
        operation: "sysctl-read",
        filters: &["(sysctl-name \"hw.pagesize\" \"hw.ncpu\" \"hw.logicalcpu\")"],
        reason: "the allocator and std::thread::available_parallelism read these",
    },
];

/// Render `rules` as an SBPL profile.
pub fn render(rules: &[Rule]) -> String {
    let mut out = String::from("(version 1)\n(deny default)\n");
    for r in rules {
        out.push_str("(allow ");
        out.push_str(r.operation);
        for f in r.filters {
            out.push(' ');
            out.push_str(f);
        }
        out.push_str(")\n");
    }
    out
}

/// The renderer's profile.
pub fn renderer_profile() -> String {
    render(RENDERER)
}
