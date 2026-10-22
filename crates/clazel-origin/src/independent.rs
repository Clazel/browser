//! An independent transcription of RFC 6454 (The Web Origin Concept, IETF,
//! December 2011), written from the RFC alone, without reference to this
//! crate's transcription of the HTML Standard:
//! - §4 "Origin": an origin is either a scheme/host/port triple or a
//!   globally unique identifier;
//! - §5 "Comparing Origins";
//! - §6.2 "Serializing Origins" (ASCII serialization).
//!
//! [`super::independent_equivalence`] proves it equal to the spec on the
//! class stated there.
//!
//! Modelling choices:
//! - RFC 6454 §4 says a triple's host is a string and its port a number;
//!   the host here is the URL Standard's host record
//!   (`clazel_url::host::spec::Host`), compared as a whole, and serialized
//!   by the URL Standard's host serializer (the RFC does not say how a host
//!   such as an IPv6 address is written; its own examples are domain names).
//!   The port is a `nat`: the triple always has one.
//! - §6.2 step 5 refers to "the default port for the protocol given by the
//!   scheme part". The RFC does not list them; they are those of the
//!   schemes' own definitions, which are the five the URL Standard calls
//!   special: http 80 (RFC 7230), https 443 (RFC 7230), ftp 21 (RFC 959),
//!   ws 80 and wss 443 (RFC 6455). For another scheme there is no default,
//!   so the port is always written.
//! - A globally unique identifier is a `nat`; two are "the same" when the
//!   numbers are equal (RFC 6454 §5 does not define comparing them beyond
//!   "not the same as" a triple; two identifiers are the same only when they
//!   are the same identifier).
//! - Strings are `Seq<u32>` of code points. The RFC's "base ten" port is
//!   written by [`rfc_decimal`], defined here.

#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// RFC 6454 §4: "An origin is ... either a scheme/host/port triple or a
/// globally unique identifier."
pub enum RfcOrigin {
    /// The triple.
    Triple {
        /// The scheme part.
        scheme: Seq<u32>,
        /// The host part.
        host: clazel_url::host::spec::Host,
        /// The port part.
        port: nat,
    },
    /// A globally unique identifier.
    Unique(nat),
}

/// The default port of the protocol a scheme names (see the modelling
/// choices), if it has one.
pub open spec fn rfc_default_port(scheme: Seq<u32>) -> Option<nat> {
    if scheme == seq![0x68u32, 0x74, 0x74, 0x70] {
        Some(80nat)
    } else if scheme == seq![0x68u32, 0x74, 0x74, 0x70, 0x73] {
        Some(443nat)
    } else if scheme == seq![0x66u32, 0x74, 0x70] {
        Some(21nat)
    } else if scheme == seq![0x77u32, 0x73] {
        Some(80nat)
    } else if scheme == seq![0x77u32, 0x73, 0x73] {
        Some(443nat)
    } else {
        None
    }
}

/// §5: "Two origins are "the same" if, and only if, they are identical.
/// In particular:
/// - If the two origins are scheme/host/port triples, the two origins are
///   the same if, and only if, they have identical schemes, hosts, and
///   ports.
/// - An origin that is not a scheme/host/port triple is not the same as an
///   origin that is a scheme/host/port triple."
/// (Two globally unique identifiers are the same when they are identical.)
pub open spec fn rfc_same_origin(a: RfcOrigin, b: RfcOrigin) -> bool {
    match (a, b) {
        (RfcOrigin::Triple { scheme: sa, host: ha, port: pa }, RfcOrigin::Triple { scheme: sb, host: hb, port: pb }) => sa == sb && ha == hb && pa == pb,
        (RfcOrigin::Unique(x), RfcOrigin::Unique(y)) => x == y,
        _ => false,
    }
}

/// A number in base ten, with no leading zeros ("the given port, in base
/// ten").
pub open spec fn rfc_decimal(n: nat) -> Seq<u32>
    decreases n,
{
    if n < 10 {
        seq![(0x30 + n) as u32]
    } else {
        rfc_decimal(n / 10) + seq![(0x30 + n % 10) as u32]
    }
}

/// §6.2 "ASCII Serialization of an Origin":
/// 1. "If the origin is not a scheme/host/port triple, then return the
///    string null (i.e., the code point sequence U+006E, U+0075, U+006C,
///    U+006C) [and abort these steps]."
/// 2. "Otherwise, let result be the scheme part of the origin triple."
/// 3. "Append the string "://" to result."
/// 4. "Append the host part of the origin triple to result."
/// 5. "If the port part of the origin triple is different from the default
///    port for the protocol given by the scheme part of the triple: append
///    a U+003A COLON code point (":") and the given port, in base ten, to
///    result."
/// 6. "Return result."
pub open spec fn rfc_serialize(o: RfcOrigin) -> Seq<u32> {
    match o {
        // 1.
        RfcOrigin::Unique(_) => seq![0x6Eu32, 0x75, 0x6C, 0x6C],
        RfcOrigin::Triple { scheme, host, port } => {
            // 2.
            let result = scheme;
            // 3.
            let result = result + seq![0x3Au32, 0x2F, 0x2F];
            // 4.
            let result = result + clazel_url::host::spec::host_serializer(host);
            // 5.
            let result = if rfc_default_port(scheme) != Some(port) {
                result + seq![0x3Au32] + rfc_decimal(port)
            } else {
                result
            };
            // 6.
            result
        },
    }
}

} // verus!
