//! Hosts (URL §3): the host record, the host, IPv4, IPv6 and opaque-host
//! parsers (§3.5), and the host serializers (§3.6).
//!
//! - [`independent`]: a second transcription, from RFC 3986 §3.2.2, RFC
//!   4291 §2.2 and RFC 5952 §4, and what it and the spec are proven to
//!   agree on.

pub mod independent;
