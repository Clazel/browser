//! Hosts (URL §3): the host record, the host, IPv4, IPv6 and opaque-host
//! parsers (§3.5), and the host serializers (§3.6).
//!
//! - [`spec`]: a step-by-step transcription of the standard (with the URL
//!   §1 and Infra definitions it uses).
//! - [`termination`]: why the spec's loops terminate.
//! - [`contract`]: what the executable functions are proven to satisfy.
//! - [`examples`]: the standard's examples, evaluated on the spec.
//! - [`independent`]: a second transcription, from RFC 3986 §3.2.2, RFC
//!   4291 §2.2 and RFC 5952 §4, and what it and the spec are proven to
//!   agree on.
//!
//! The domain parser (URL §3.3) comes from `clazel-idna` (item 1.8); see
//! [`contract`] for how the host parser is split around it.

pub mod contract;
pub mod domain_examples;
pub mod examples;
pub mod independent;
pub mod ipv4;
pub mod ipv6;
pub mod ipv6_text;
pub mod lemmas;
pub mod parse;
pub mod record;
pub mod serialize;
pub mod spec;
pub mod termination;
