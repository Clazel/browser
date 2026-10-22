//! RFC 6265bis cookies: dates (§5.1.1), canonicalized host names (§5.1.2),
//! domain matching (§5.1.3), default-path and path-match (§5.1.4), and the
//! Set-Cookie parser (§5.4 to §5.6), and the storage and retrieval models
//! (§5.2, §5.7, §5.8).
//!
//! Spec: <https://www.ietf.org/archive/id/draft-ietf-httpbis-rfc6265bis-22.txt>
//! (draft-ietf-httpbis-rfc6265bis-22, 1 December 2025; the latest revision
//! on 21 October 2026, not yet an RFC).
//! Tier: see `[package.metadata.clazel]` in `Cargo.toml` and
//! `docs/VERIFICATION.md`.

pub mod ascii;
pub mod date;
pub mod matching;
pub mod set_cookie;
pub mod storage;
pub mod strings;
