//! The independent transcription of RFC 6454 ([`super::independent`]) is
//! proven equal to the spec ([`super::spec`]) on the class of origins where
//! the two models describe the same thing:
//! - opaque origins (RFC 6454's globally unique identifiers) and tuple
//!   origins whose domain is null (the RFC has no "domain");
//! - tuple origins whose port is, as the URL parser makes it, null exactly
//!   when it is the scheme's default: a port is either null with a scheme
//!   that has a default port, or a number that is not the scheme's default.
//!   (HTML keeps "port: null" for the default; the RFC's triple always has a
//!   number. Origins outside this class, such as `http` with port 80 given
//!   explicitly, are two HTML origins for what the RFC calls one.)
//!
//! On the class, "same origin" (HTML §7.1.1) is RFC 6454 §5 and
//! "serialization of an origin" (HTML §7.1.1) is §6.2.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The origin is in the class (see the module comment).
pub open spec fn in_class(o: Origin) -> bool {
    match o {
        Origin::Opaque(_) => true,
        Origin::Tuple { scheme, port, domain, .. } => domain is None && match port {
            None => super::independent::rfc_default_port(scheme) is Some,
            Some(p) => super::independent::rfc_default_port(scheme) != Some(p),
        },
    }
}

/// The RFC's reading of an origin of the class.
pub open spec fn to_rfc(o: Origin) -> super::independent::RfcOrigin {
    match o {
        Origin::Opaque(n) => super::independent::RfcOrigin::Unique(n),
        Origin::Tuple { scheme, host, port, .. } => super::independent::RfcOrigin::Triple {
            scheme,
            host,
            port: match port {
                Some(p) => p,
                None => super::independent::rfc_default_port(scheme)->Some_0,
            },
        },
    }
}

/// RFC 6454 §5 is HTML's "same origin" on the class.
pub proof fn lemma_same_origin_agrees(a: Origin, b: Origin)
    requires
        in_class(a),
        in_class(b),
    ensures
        same_origin(a, b) == super::independent::rfc_same_origin(to_rfc(a), to_rfc(b)),
{
}

/// The RFC's decimal is the URL Standard's integer serializer.
pub proof fn lemma_decimal_agrees(n: nat)
    ensures
        super::independent::rfc_decimal(n) == clazel_url::host::spec::serialize_integer(n),
    decreases n,
{
    if n >= 10 {
        lemma_decimal_agrees(n / 10);
    }
}

/// RFC 6454 §6.2 is HTML's "serialization of an origin" on the class.
pub proof fn lemma_serialization_agrees(o: Origin)
    requires
        in_class(o),
    ensures
        serialization_of_origin(o) == super::independent::rfc_serialize(to_rfc(o)),
{
    if let Origin::Tuple { port: Some(p), .. } = o {
        lemma_decimal_agrees(p);
    }
}

} // verus!
