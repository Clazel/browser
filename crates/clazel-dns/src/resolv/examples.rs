//! The grammar's examples, evaluated on the spec: what the `nameserver`
//! lines of a resolv.conf give, and what makes a line give nothing.
//!
//! This is a module of its own because Verus evaluates every `by
//! (compute_only)` assertion of a module it verifies (see `examples.rs`).

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// one line with LF: `'nameserver 8.8.8.8\n'`.
pub proof fn lemma_resolv_example_0()
    ensures
        nameservers(seq![110u8, 97, 109, 101, 115, 101, 114, 118, 101, 114, 32, 56, 46, 56, 46, 56, 46, 56, 10]) == seq![crate::spec::Addr::V4(134744072)],
{
    assert(nameservers(seq![110u8, 97, 109, 101, 115, 101, 114, 118, 101, 114, 32, 56, 46, 56, 46, 56, 46, 56, 10]) == seq![crate::spec::Addr::V4(134744072)]) by (compute_only);
}

/// no final line feed: `'nameserver 1.2.3.4'`.
pub proof fn lemma_resolv_example_1()
    ensures
        nameservers(seq![110u8, 97, 109, 101, 115, 101, 114, 118, 101, 114, 32, 49, 46, 50, 46, 51, 46, 52]) == seq![crate::spec::Addr::V4(16909060)],
{
    assert(nameservers(seq![110u8, 97, 109, 101, 115, 101, 114, 118, 101, 114, 32, 49, 46, 50, 46, 51, 46, 52]) == seq![crate::spec::Addr::V4(16909060)]) by (compute_only);
}

/// two servers, a comment and another keyword: `'# generated\nsearch example.com\nnameserver 1.1.1.1\nnameserver 9.9.9.9\n'`.
pub proof fn lemma_resolv_example_2()
    ensures
        nameservers(seq![35u8, 32, 103, 101, 110, 101, 114, 97, 116, 101, 100, 10, 115, 101, 97, 114, 99, 104, 32, 101, 120, 97, 109, 112, 108, 101, 46, 99, 111, 109, 10, 110, 97, 109, 101, 115, 101, 114, 118, 101, 114, 32, 49, 46, 49, 46, 49, 46, 49, 10, 110, 97, 109, 101, 115, 101, 114, 118, 101, 114, 32, 57, 46, 57, 46, 57, 46, 57, 10]) == seq![crate::spec::Addr::V4(16843009), crate::spec::Addr::V4(151587081)],
{
    assert(nameservers(seq![35u8, 32, 103, 101, 110, 101, 114, 97, 116, 101, 100, 10, 115, 101, 97, 114, 99, 104, 32, 101, 120, 97, 109, 112, 108, 101, 46, 99, 111, 109, 10, 110, 97, 109, 101, 115, 101, 114, 118, 101, 114, 32, 49, 46, 49, 46, 49, 46, 49, 10, 110, 97, 109, 101, 115, 101, 114, 118, 101, 114, 32, 57, 46, 57, 46, 57, 46, 57, 10]) == seq![crate::spec::Addr::V4(16843009), crate::spec::Addr::V4(151587081)]) by (compute_only);
}

/// CR LF line ends: `'nameserver 10.0.0.1\r\nnameserver 10.0.0.2\r\n'`.
pub proof fn lemma_resolv_example_3()
    ensures
        nameservers(seq![110u8, 97, 109, 101, 115, 101, 114, 118, 101, 114, 32, 49, 48, 46, 48, 46, 48, 46, 49, 13, 10, 110, 97, 109, 101, 115, 101, 114, 118, 101, 114, 32, 49, 48, 46, 48, 46, 48, 46, 50, 13, 10]) == seq![crate::spec::Addr::V4(167772161), crate::spec::Addr::V4(167772162)],
{
    assert(nameservers(seq![110u8, 97, 109, 101, 115, 101, 114, 118, 101, 114, 32, 49, 48, 46, 48, 46, 48, 46, 49, 13, 10, 110, 97, 109, 101, 115, 101, 114, 118, 101, 114, 32, 49, 48, 46, 48, 46, 48, 46, 50, 13, 10]) == seq![crate::spec::Addr::V4(167772161), crate::spec::Addr::V4(167772162)]) by (compute_only);
}

/// leading white space, a tab, and a trailing comment: `'  \tnameserver\t192.168.1.1  # router\n'`.
pub proof fn lemma_resolv_example_4()
    ensures
        nameservers(seq![32u8, 32, 9, 110, 97, 109, 101, 115, 101, 114, 118, 101, 114, 9, 49, 57, 50, 46, 49, 54, 56, 46, 49, 46, 49, 32, 32, 35, 32, 114, 111, 117, 116, 101, 114, 10]) == seq![crate::spec::Addr::V4(3232235777)],
{
    assert(nameservers(seq![32u8, 32, 9, 110, 97, 109, 101, 115, 101, 114, 118, 101, 114, 9, 49, 57, 50, 46, 49, 54, 56, 46, 49, 46, 49, 32, 32, 35, 32, 114, 111, 117, 116, 101, 114, 10]) == seq![crate::spec::Addr::V4(3232235777)]) by (compute_only);
}

/// IPv6: `'nameserver ::1\n'`.
pub proof fn lemma_resolv_example_5()
    ensures
        nameservers(seq![110u8, 97, 109, 101, 115, 101, 114, 118, 101, 114, 32, 58, 58, 49, 10]) == seq![crate::spec::Addr::V6(1)],
{
    assert(nameservers(seq![110u8, 97, 109, 101, 115, 101, 114, 118, 101, 114, 32, 58, 58, 49, 10]) == seq![crate::spec::Addr::V6(1)]) by (compute_only);
}

/// IPv6, full form: `'nameserver 2001:db8::8888\n'`.
pub proof fn lemma_resolv_example_6()
    ensures
        nameservers(seq![110u8, 97, 109, 101, 115, 101, 114, 118, 101, 114, 32, 50, 48, 48, 49, 58, 100, 98, 56, 58, 58, 56, 56, 56, 56, 10]) == seq![crate::spec::Addr::V6(42540766411282592856903984951653861512)],
{
    assert(nameservers(seq![110u8, 97, 109, 101, 115, 101, 114, 118, 101, 114, 32, 50, 48, 48, 49, 58, 100, 98, 56, 58, 58, 56, 56, 56, 56, 10]) == seq![crate::spec::Addr::V6(42540766411282592856903984951653861512)]) by (compute_only);
}

/// no address: `'nameserver\n'`.
pub proof fn lemma_resolv_example_7()
    ensures
        nameservers(seq![110u8, 97, 109, 101, 115, 101, 114, 118, 101, 114, 10]) == seq![],
{
    assert(nameservers(seq![110u8, 97, 109, 101, 115, 101, 114, 118, 101, 114, 10]) == seq![]) by (compute_only);
}

/// keyword is case sensitive: `'Nameserver 1.2.3.4\nNAMESERVER 1.2.3.4\n'`.
pub proof fn lemma_resolv_example_8()
    ensures
        nameservers(seq![78u8, 97, 109, 101, 115, 101, 114, 118, 101, 114, 32, 49, 46, 50, 46, 51, 46, 52, 10, 78, 65, 77, 69, 83, 69, 82, 86, 69, 82, 32, 49, 46, 50, 46, 51, 46, 52, 10]) == seq![],
{
    assert(nameservers(seq![78u8, 97, 109, 101, 115, 101, 114, 118, 101, 114, 32, 49, 46, 50, 46, 51, 46, 52, 10, 78, 65, 77, 69, 83, 69, 82, 86, 69, 82, 32, 49, 46, 50, 46, 51, 46, 52, 10]) == seq![]) by (compute_only);
}

/// keyword must be a whole token: `'nameserver1 1.2.3.4\nnameservers 1.2.3.4\n'`.
pub proof fn lemma_resolv_example_9()
    ensures
        nameservers(seq![110u8, 97, 109, 101, 115, 101, 114, 118, 101, 114, 49, 32, 49, 46, 50, 46, 51, 46, 52, 10, 110, 97, 109, 101, 115, 101, 114, 118, 101, 114, 115, 32, 49, 46, 50, 46, 51, 46, 52, 10]) == seq![],
{
    assert(nameservers(seq![110u8, 97, 109, 101, 115, 101, 114, 118, 101, 114, 49, 32, 49, 46, 50, 46, 51, 46, 52, 10, 110, 97, 109, 101, 115, 101, 114, 118, 101, 114, 115, 32, 49, 46, 50, 46, 51, 46, 52, 10]) == seq![]) by (compute_only);
}

/// address must be strict dotted decimal: `'nameserver 1.2.3\nnameserver 1.2.3.4.5\nnameserver 01.2.3.4\nnameserver 256.1.1.1\nnameserver 1.2.3.\nnameserver 1.2..4\nnameserver 0x7f.0.0.1\nnameserver 1\nnameserver 1.2.3.4a\nnameserver 1.2.3.0004\n'`.
pub proof fn lemma_resolv_example_10()
    ensures
        nameservers(seq![110u8, 97, 109, 101, 115, 101, 114, 118, 101, 114, 32, 49, 46, 50, 46, 51, 10, 110, 97, 109, 101, 115, 101, 114, 118, 101, 114, 32, 49, 46, 50, 46, 51, 46, 52, 46, 53, 10, 110, 97, 109, 101, 115, 101, 114, 118, 101, 114, 32, 48, 49, 46, 50, 46, 51, 46, 52, 10, 110, 97, 109, 101, 115, 101, 114, 118, 101, 114, 32, 50, 53, 54, 46, 49, 46, 49, 46, 49, 10, 110, 97, 109, 101, 115, 101, 114, 118, 101, 114, 32, 49, 46, 50, 46, 51, 46, 10, 110, 97, 109, 101, 115, 101, 114, 118, 101, 114, 32, 49, 46, 50, 46, 46, 52, 10, 110, 97, 109, 101, 115, 101, 114, 118, 101, 114, 32, 48, 120, 55, 102, 46, 48, 46, 48, 46, 49, 10, 110, 97, 109, 101, 115, 101, 114, 118, 101, 114, 32, 49, 10, 110, 97, 109, 101, 115, 101, 114, 118, 101, 114, 32, 49, 46, 50, 46, 51, 46, 52, 97, 10, 110, 97, 109, 101, 115, 101, 114, 118, 101, 114, 32, 49, 46, 50, 46, 51, 46, 48, 48, 48, 52, 10]) == seq![],
{
    assert(nameservers(seq![110u8, 97, 109, 101, 115, 101, 114, 118, 101, 114, 32, 49, 46, 50, 46, 51, 10, 110, 97, 109, 101, 115, 101, 114, 118, 101, 114, 32, 49, 46, 50, 46, 51, 46, 52, 46, 53, 10, 110, 97, 109, 101, 115, 101, 114, 118, 101, 114, 32, 48, 49, 46, 50, 46, 51, 46, 52, 10, 110, 97, 109, 101, 115, 101, 114, 118, 101, 114, 32, 50, 53, 54, 46, 49, 46, 49, 46, 49, 10, 110, 97, 109, 101, 115, 101, 114, 118, 101, 114, 32, 49, 46, 50, 46, 51, 46, 10, 110, 97, 109, 101, 115, 101, 114, 118, 101, 114, 32, 49, 46, 50, 46, 46, 52, 10, 110, 97, 109, 101, 115, 101, 114, 118, 101, 114, 32, 48, 120, 55, 102, 46, 48, 46, 48, 46, 49, 10, 110, 97, 109, 101, 115, 101, 114, 118, 101, 114, 32, 49, 10, 110, 97, 109, 101, 115, 101, 114, 118, 101, 114, 32, 49, 46, 50, 46, 51, 46, 52, 97, 10, 110, 97, 109, 101, 115, 101, 114, 118, 101, 114, 32, 49, 46, 50, 46, 51, 46, 48, 48, 48, 52, 10]) == seq![]) by (compute_only);
}

/// zero parts are fine: `'nameserver 0.0.0.0\nnameserver 255.255.255.255\nnameserver 10.0.10.0\n'`.
pub proof fn lemma_resolv_example_11()
    ensures
        nameservers(seq![110u8, 97, 109, 101, 115, 101, 114, 118, 101, 114, 32, 48, 46, 48, 46, 48, 46, 48, 10, 110, 97, 109, 101, 115, 101, 114, 118, 101, 114, 32, 50, 53, 53, 46, 50, 53, 53, 46, 50, 53, 53, 46, 50, 53, 53, 10, 110, 97, 109, 101, 115, 101, 114, 118, 101, 114, 32, 49, 48, 46, 48, 46, 49, 48, 46, 48, 10]) == seq![crate::spec::Addr::V4(0), crate::spec::Addr::V4(4294967295), crate::spec::Addr::V4(167774720)],
{
    assert(nameservers(seq![110u8, 97, 109, 101, 115, 101, 114, 118, 101, 114, 32, 48, 46, 48, 46, 48, 46, 48, 10, 110, 97, 109, 101, 115, 101, 114, 118, 101, 114, 32, 50, 53, 53, 46, 50, 53, 53, 46, 50, 53, 53, 46, 50, 53, 53, 10, 110, 97, 109, 101, 115, 101, 114, 118, 101, 114, 32, 49, 48, 46, 48, 46, 49, 48, 46, 48, 10]) == seq![crate::spec::Addr::V4(0), crate::spec::Addr::V4(4294967295), crate::spec::Addr::V4(167774720)]) by (compute_only);
}

/// a zone identifier is not accepted: `'nameserver fe80::1%eth0\n'`.
pub proof fn lemma_resolv_example_12()
    ensures
        nameservers(seq![110u8, 97, 109, 101, 115, 101, 114, 118, 101, 114, 32, 102, 101, 56, 48, 58, 58, 49, 37, 101, 116, 104, 48, 10]) == seq![],
{
    assert(nameservers(seq![110u8, 97, 109, 101, 115, 101, 114, 118, 101, 114, 32, 102, 101, 56, 48, 58, 58, 49, 37, 101, 116, 104, 48, 10]) == seq![]) by (compute_only);
}

/// not an address: `'nameserver example.com\nnameserver [::1]\nnameserver ::g\n'`.
pub proof fn lemma_resolv_example_13()
    ensures
        nameservers(seq![110u8, 97, 109, 101, 115, 101, 114, 118, 101, 114, 32, 101, 120, 97, 109, 112, 108, 101, 46, 99, 111, 109, 10, 110, 97, 109, 101, 115, 101, 114, 118, 101, 114, 32, 91, 58, 58, 49, 93, 10, 110, 97, 109, 101, 115, 101, 114, 118, 101, 114, 32, 58, 58, 103, 10]) == seq![],
{
    assert(nameservers(seq![110u8, 97, 109, 101, 115, 101, 114, 118, 101, 114, 32, 101, 120, 97, 109, 112, 108, 101, 46, 99, 111, 109, 10, 110, 97, 109, 101, 115, 101, 114, 118, 101, 114, 32, 91, 58, 58, 49, 93, 10, 110, 97, 109, 101, 115, 101, 114, 118, 101, 114, 32, 58, 58, 103, 10]) == seq![]) by (compute_only);
}

/// the first token only: `'nameserver 1.2.3.4 5.6.7.8\n'`.
pub proof fn lemma_resolv_example_14()
    ensures
        nameservers(seq![110u8, 97, 109, 101, 115, 101, 114, 118, 101, 114, 32, 49, 46, 50, 46, 51, 46, 52, 32, 53, 46, 54, 46, 55, 46, 56, 10]) == seq![crate::spec::Addr::V4(16909060)],
{
    assert(nameservers(seq![110u8, 97, 109, 101, 115, 101, 114, 118, 101, 114, 32, 49, 46, 50, 46, 51, 46, 52, 32, 53, 46, 54, 46, 55, 46, 56, 10]) == seq![crate::spec::Addr::V4(16909060)]) by (compute_only);
}

/// an empty file and blank lines: `'\n\n  \n'`.
pub proof fn lemma_resolv_example_15()
    ensures
        nameservers(seq![10u8, 10, 32, 32, 10]) == seq![],
{
    assert(nameservers(seq![10u8, 10, 32, 32, 10]) == seq![]) by (compute_only);
}

} // verus!
