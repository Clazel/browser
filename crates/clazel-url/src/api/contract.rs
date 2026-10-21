//! Contracts the executable URL API setters must be proven to meet. Each
//! exec setter's `ensures` clause is exactly one of these predicates (and
//! its `requires`, where it has one), so reviewing these and
//! [`super::spec`] is enough to know what the implementation guarantees.
//!
//! An exec setter is a function on the exec URL record, `ParsedUrl`, that
//! changes it in place: `set_X(url: &mut ParsedUrl, value: &[u32])`. Its
//! contract relates the URL before (`url`) and after (`output`). The
//! domain parser is `clazel-idna`'s
//! ([`crate::url::contract::url_domain_parser`]), as for the basic URL
//! parser.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Precondition of every exec setter: the given value is a USVString, a
/// scalar value string.
pub open spec fn setter_requires(value: Seq<u32>) -> bool {
    clazel_encoding::utf8::spec::all_scalar_values(value)
}

/// Contract for `set_href(&mut ParsedUrl, &[u32]) -> bool`: `ok` is false
/// exactly when the setter throws a TypeError, and then the URL is
/// unchanged.
pub open spec fn href_setter_ensures(url: crate::url::spec::Url, value: Seq<u32>, ok: bool, output: crate::url::spec::Url) -> bool {
    match href_setter(url, value, crate::url::contract::url_domain_parser()) {
        None => !ok && output == url,
        Some(u) => ok && output == u,
    }
}

/// Contract for `set_protocol(&mut ParsedUrl, &[u32])`.
pub open spec fn protocol_setter_ensures(url: crate::url::spec::Url, value: Seq<u32>, output: crate::url::spec::Url) -> bool {
    output == protocol_setter(url, value, crate::url::contract::url_domain_parser())
}

/// Contract for `set_username(&mut ParsedUrl, &[u32])`.
pub open spec fn username_setter_ensures(url: crate::url::spec::Url, value: Seq<u32>, output: crate::url::spec::Url) -> bool {
    output == username_setter(url, value)
}

/// Contract for `set_password(&mut ParsedUrl, &[u32])`.
pub open spec fn password_setter_ensures(url: crate::url::spec::Url, value: Seq<u32>, output: crate::url::spec::Url) -> bool {
    output == password_setter(url, value)
}

/// Contract for `set_host(&mut ParsedUrl, &[u32])`.
pub open spec fn host_setter_ensures(url: crate::url::spec::Url, value: Seq<u32>, output: crate::url::spec::Url) -> bool {
    output == host_setter(url, value, crate::url::contract::url_domain_parser())
}

/// Contract for `set_hostname(&mut ParsedUrl, &[u32])`.
pub open spec fn hostname_setter_ensures(url: crate::url::spec::Url, value: Seq<u32>, output: crate::url::spec::Url) -> bool {
    output == hostname_setter(url, value, crate::url::contract::url_domain_parser())
}

/// Contract for `set_port(&mut ParsedUrl, &[u32])`.
pub open spec fn port_setter_ensures(url: crate::url::spec::Url, value: Seq<u32>, output: crate::url::spec::Url) -> bool {
    output == port_setter(url, value, crate::url::contract::url_domain_parser())
}

/// Contract for `set_pathname(&mut ParsedUrl, &[u32])`.
pub open spec fn pathname_setter_ensures(url: crate::url::spec::Url, value: Seq<u32>, output: crate::url::spec::Url) -> bool {
    output == pathname_setter(url, value, crate::url::contract::url_domain_parser())
}

/// Contract for `set_search(&mut ParsedUrl, &[u32])`.
pub open spec fn search_setter_ensures(url: crate::url::spec::Url, value: Seq<u32>, output: crate::url::spec::Url) -> bool {
    output == search_setter(url, value, crate::url::contract::url_domain_parser())
}

/// Contract for `set_hash(&mut ParsedUrl, &[u32])`.
pub open spec fn hash_setter_ensures(url: crate::url::spec::Url, value: Seq<u32>, output: crate::url::spec::Url) -> bool {
    output == hash_setter(url, value, crate::url::contract::url_domain_parser())
}

} // verus!
