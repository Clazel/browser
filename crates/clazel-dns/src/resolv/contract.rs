//! Contract the executable resolv.conf parser must be proven to meet.

use super::super::spec::Addr;
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Contract for `nameservers(&[u8]) -> Vec<Addr>`: the addresses of the
/// `nameserver` lines, in file order.
pub open spec fn nameservers_ensures(input: Seq<u8>, output: Seq<Addr>) -> bool {
    output == nameservers(input)
}

} // verus!
