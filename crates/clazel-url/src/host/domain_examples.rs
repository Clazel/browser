//! The host parser evaluated with the real domain parser (`clazel-idna`'s URL
//! §3.3 domain parser). A module of its own, like [`super::examples`], so
//! that a mutant that makes Verus evaluate the Unicode tables (which it
//! cannot do across crates) breaks only this module.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The host parser with the real domain parser (`clazel-idna`'s URL §3.3
/// domain parser), evaluated on ASCII domains, for which beStrict false
/// needs no table (steps 5, 7 to 9): "A_B" is the domain "a_b" (U+005F is
/// not forbidden, though UseSTD3ASCIIRules would reject it), "EXAMPLE.COM"
/// is lowercased, "1.2.3.4" is an IPv4 address. Verus cannot evaluate
/// another crate's Unicode tables, so ToASCII itself is not evaluated here;
/// its examples are in `clazel-idna`, and the WPT rows with non-ASCII
/// domains run in `tests/conformance_hosts.rs`.
pub proof fn lemma_domain_examples()
    ensures
        host_parser(seq![0x41u32, 0x5F, 0x42], false, super::contract::url_domain_parser()) == Some(Host::Domain(seq![0x61u32, 0x5F, 0x62])),
        host_parser(seq![0x45u32, 0x58, 0x41, 0x4D, 0x50, 0x4C, 0x45, 0x2E, 0x43, 0x4F, 0x4D], false, super::contract::url_domain_parser()) == Some(Host::Domain(seq![0x65u32, 0x78, 0x61, 0x6D, 0x70, 0x6C, 0x65, 0x2E, 0x63, 0x6F, 0x6D])),
        host_parser(seq![0x31u32, 0x2E, 0x32, 0x2E, 0x33, 0x2E, 0x34], false, super::contract::url_domain_parser()) == Some(Host::Ipv4(0x0102_0304nat)),
{
    assert(host_parser(seq![0x41u32, 0x5F, 0x42], false, super::contract::url_domain_parser()) == Some(Host::Domain(seq![0x61u32, 0x5F, 0x62]))) by (compute_only);
    assert(host_parser(seq![0x45u32, 0x58, 0x41, 0x4D, 0x50, 0x4C, 0x45, 0x2E, 0x43, 0x4F, 0x4D], false, super::contract::url_domain_parser()) == Some(Host::Domain(seq![0x65u32, 0x78, 0x61, 0x6D, 0x70, 0x6C, 0x65, 0x2E, 0x63, 0x6F, 0x6D]))) by (compute_only);
    assert(host_parser(seq![0x31u32, 0x2E, 0x32, 0x2E, 0x33, 0x2E, 0x34], false, super::contract::url_domain_parser()) == Some(Host::Ipv4(0x0102_0304nat))) by (compute_only);
}

} // verus!
