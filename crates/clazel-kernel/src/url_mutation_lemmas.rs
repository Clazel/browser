//! Lemmas the kill certificates of `mutations.json` for [`crate::urls`]
//! instantiate (item 2.13): what the three real URL functions are, phrased
//! so that a concrete instance can be evaluated by Verus's `compute_only`.
//!
//! They are about the unguarded pieces (`*_scalar`), with the domain parser
//! a parameter: Verus cannot evaluate `clazel-idna`'s Unicode tables, and
//! `all_scalar_values` is a quantifier. The certificates evaluate them with
//! [`ml_idp`], a domain parser that returns its domain (the same as
//! `clazel-idna`'s on a lowercase ASCII one, and the one `clazel-url`'s
//! examples use); the lemmas hold for every domain parser.

#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// A domain parser that returns its input.
pub open spec fn ml_idp() -> clazel_url::host::spec::DomainParser {
    |d: Seq<u32>, b: bool| Some(d)
}

/// `file:///a/b`.
pub open spec fn ml_base() -> Seq<u32> {
    seq![0x66u32, 0x69, 0x6C, 0x65, 0x3A, 0x2F, 0x2F, 0x2F, 0x61, 0x2F, 0x62]
}

/// `c#f`, a relative reference with a fragment.
pub open spec fn ml_rel() -> Seq<u32> {
    seq![0x63u32, 0x23, 0x66]
}

/// `file:///a?q`, a URL with a path and a query.
pub open spec fn ml_with_query() -> Seq<u32> {
    seq![0x66u32, 0x69, 0x6C, 0x65, 0x3A, 0x2F, 0x2F, 0x2F, 0x61, 0x3F, 0x71]
}

/// `data:,`, a URL with an opaque origin.
pub open spec fn ml_data() -> Seq<u32> {
    seq![0x64u32, 0x61, 0x74, 0x61, 0x3A, 0x2C]
}

/// The URL `input` parses to against the URL `base` parses to (when both
/// parse).
pub open spec fn ml_resolved(dp: clazel_url::host::spec::DomainParser, base: Seq<u32>, input: Seq<u32>) -> clazel_url::url::spec::Url {
    clazel_url::url::spec::basic_url_parser(input, Some(crate::urls::parse_absolute(dp, base)->Some_0), dp)->Some_0
}

/// `resolve` is the serialization of `input` parsed against the parse of
/// `base`, when both parse.
pub proof fn ml_resolve_composition(dp: clazel_url::host::spec::DomainParser, base: Seq<u32>, input: Seq<u32>)
    requires
        crate::urls::parse_absolute(dp, base) is Some,
        clazel_url::url::spec::basic_url_parser(input, Some(crate::urls::parse_absolute(dp, base)->Some_0), dp) is Some,
    ensures
        crate::urls::resolve_scalar(dp, base, input) == Some(clazel_url::url::spec::url_serializer(ml_resolved(dp, base, input), false)),
{
}

/// `resolve` fails if `base` does not parse.
pub proof fn ml_resolve_base_failure(dp: clazel_url::host::spec::DomainParser, base: Seq<u32>, input: Seq<u32>)
    requires
        crate::urls::parse_absolute(dp, base) is None,
    ensures
        crate::urls::resolve_scalar(dp, base, input) is None,
{
}

/// `path_of` is the octets of the parsed URL's path serialization.
pub proof fn ml_path_of_parsed(dp: clazel_url::host::spec::DomainParser, input: Seq<u32>)
    requires
        crate::urls::parse_absolute(dp, input) is Some,
    ensures
        crate::urls::path_of_scalar(dp, input) == clazel_cookie::matching::spec::narrow(clazel_url::url::spec::url_path_serializer(crate::urls::parse_absolute(dp, input)->Some_0.path)),
{
}

/// `origin_of` is the origin of the parsed URL.
pub proof fn ml_origin_of_parsed(dp: clazel_url::host::spec::DomainParser, input: Seq<u32>)
    requires
        crate::urls::parse_absolute(dp, input) is Some,
    ensures
        crate::urls::origin_of_scalar(dp, input) == Some(clazel_origin::spec::url_origin(crate::urls::parse_absolute(dp, input)->Some_0, dp, crate::urls::fresh_opaque_id())),
{
}

/// `origin_of` fails if the string does not parse.
pub proof fn ml_origin_of_failure(dp: clazel_url::host::spec::DomainParser, input: Seq<u32>)
    requires
        crate::urls::parse_absolute(dp, input) is None,
    ensures
        crate::urls::origin_of_scalar(dp, input) is None,
{
}

/// A parsed URL whose scheme gives neither a tuple origin nor a blob path has
/// an opaque origin.
pub proof fn ml_origin_of_opaque(dp: clazel_url::host::spec::DomainParser, input: Seq<u32>)
    requires
        crate::urls::parse_absolute(dp, input) is Some,
        crate::urls::parse_absolute(dp, input)->Some_0.scheme != clazel_origin::spec::blob_str(),
        !clazel_origin::spec::has_tuple_origin_scheme(crate::urls::parse_absolute(dp, input)->Some_0.scheme),
    ensures
        crate::urls::origin_of_scalar(dp, input) is Some,
        crate::urls::origin_of_scalar(dp, input)->Some_0 is Opaque,
{
}

} // verus!
