//! Executable-style specification of origins and sites (HTML §7.1.1) and of
//! the origin of a URL (URL §4.7). Nothing here runs; it defines what
//! "correct" means. Every definition cites its source, and each `// N.`
//! comment is the step number in the cited algorithm.
//!
//! Sources (each pinned; a review is against exactly this text):
//! - HTML Standard, Living Standard, last updated 20 October 2026,
//!   <https://html.spec.whatwg.org/multipage/browsers.html#origin>: §7.1.1
//!   "Origins" (origin, effective domain, serialization of an origin, same
//!   origin, same origin-domain), §7.1.1.1 "Sites" (scheme-and-host, site,
//!   obtain a site, same site for sites, serialization of a site,
//!   schemelessly same site, same site for origins) and §7.1.1.2 "is a
//!   registrable domain suffix of or is equal to". The multipage page
//!   carries no commit hash; the date is its pin.
//! - URL Standard, Living Standard, `url.bs` at commit
//!   `845bafca22fb0c5a42c4bf384a9bdea525a2f10d` (19 October 2026), §4.7
//!   "origin" of a URL, and §3.2 "registrable domain" (from `clazel-psl`).
//!
//! Modelling choices:
//! - An opaque origin is `Origin::Opaque(id)`, `id` a `nat`: "An internal
//!   value, with no serialization it can be recreated from [...] for which
//!   the only meaningful operation is testing for equality." Two opaque
//!   origins are "the same opaque origin" exactly when their ids are equal.
//!   Each "a new opaque origin" in URL §4.7 is the id the caller passes as
//!   `fresh`; the caller (the kernel) allocates distinct ids, and nothing
//!   here constrains that.
//! - A tuple origin is `Origin::Tuple`: scheme, host (`clazel-url`'s
//!   `Host`), port (null or below 2^16) and domain (null or a host).
//! - A host's registrable domain is `clazel-psl`'s, over any list of rules
//!   `rules`, so the theorems hold for every list; the tables list is
//!   `clazel_psl::table::psl_rules()`. A registrable domain is a domain, so
//!   it becomes the host `Host::Domain(..)` in "obtain a site".
//! - "Hosts are equal" (HTML on `host`s, URL §3.1) is equality of the host
//!   values: two domains are equal when their strings are, two IP addresses
//!   when their integers are, and a domain never equals an IP address.
//! - URL §4.7 step "blob URL entry": the URL record of `clazel-url` has no
//!   blob URL entry (its header lists this), so the entry is always null and
//!   the first step never applies. There is no blob URL store in Phase 2.
//! - URL §4.7 `file:`: "left as an exercise to the reader. When in doubt,
//!   return a new opaque origin." We return a new opaque origin, so `file:`
//!   URLs are never same origin with anything, themselves included.
//! - The basic URL parser requires a scalar value string. A URL record the
//!   parser produced has a path of scalar values, but the spec cannot use
//!   that without a lemma about the 18 000-line parser, so a blob URL whose
//!   path serialization is not a scalar value string is treated like a
//!   failed parse (a new opaque origin). Parsed URLs never reach that case.
//! - "Is a registrable domain suffix of or is equal to" is transcribed with
//!   the host parser's result as an argument (`parsed`), as `clazel-url`'s
//!   host parser takes the domain parser, so it does not depend on the URL
//!   parser. It has no executable version: its only caller is the
//!   `document.domain` setter, which is Phase 7.

#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// HTML §7.1.1: "An origin is one of the following: An opaque origin [...]
/// A tuple origin".
pub enum Origin {
    /// An opaque origin, identified by the `nat` the kernel allocated.
    Opaque(nat),
    /// "A tuple consisting of: A scheme (an ASCII string). A host (a host).
    /// A port (null or a 16-bit unsigned integer). A domain (null or a
    /// host). Null unless stated otherwise."
    Tuple {
        /// The scheme.
        scheme: Seq<u32>,
        /// The host.
        host: clazel_url::host::spec::Host,
        /// The port.
        port: Option<nat>,
        /// The domain.
        domain: Option<clazel_url::host::spec::Host>,
    },
}

/// HTML §7.1.1.1: "A site is an opaque origin or a scheme-and-host", where
/// "A scheme-and-host is a tuple of a scheme (an ASCII string) and a host
/// (a host)."
pub enum Site {
    /// An opaque origin.
    Opaque(nat),
    /// A scheme-and-host.
    SchemeAndHost(Seq<u32>, clazel_url::host::spec::Host),
}

/// A tuple origin with a null domain.
pub open spec fn tuple_origin(scheme: Seq<u32>, host: clazel_url::host::spec::Host, port: Option<nat>) -> Origin {
    Origin::Tuple { scheme, host, port, domain: None }
}

/// HTML §7.1.1 "effective domain": "1. If origin is an opaque origin, then
/// return null. 2. If origin's domain is non-null, then return origin's
/// domain. 3. Return origin's host."
pub open spec fn effective_domain(origin: Origin) -> Option<clazel_url::host::spec::Host> {
    match origin {
        // 1.
        Origin::Opaque(_) => None,
        Origin::Tuple { host, domain, .. } => match domain {
            // 2.
            Some(d) => Some(d),
            // 3.
            None => Some(host),
        },
    }
}

/// HTML §7.1.1 "serialization of an origin".
pub open spec fn serialization_of_origin(origin: Origin) -> Seq<u32> {
    match origin {
        // 1. "If origin is an opaque origin, then return "null"."
        Origin::Opaque(_) => seq![0x6Eu32, 0x75, 0x6C, 0x6C],
        Origin::Tuple { scheme, host, port, .. } => {
            // 2. "Otherwise, let result be origin's scheme."
            // 3. "Append "://" to result."
            let result = scheme + seq![0x3Au32, 0x2F, 0x2F];
            // 4. "Append origin's host, serialized, to result."
            let result = result + clazel_url::host::spec::host_serializer(host);
            // 5. "If origin's port is non-null, append a U+003A COLON
            //    character (:), and origin's port, serialized, to result."
            let result = match port {
                Some(p) => result + seq![0x3Au32] + clazel_url::host::spec::serialize_integer(p),
                None => result,
            };
            // 6. "Return result."
            result
        },
    }
}

/// HTML §7.1.1 "same origin": "1. If A and B are the same opaque origin,
/// then return true. 2. If A and B are both tuple origins, their schemes
/// and ports are identical, and their hosts are equal, then return true.
/// 3. Return false."
pub open spec fn same_origin(a: Origin, b: Origin) -> bool {
    match (a, b) {
        // 1.
        (Origin::Opaque(x), Origin::Opaque(y)) => x == y,
        // 2.
        (Origin::Tuple { scheme: sa, host: ha, port: pa, .. }, Origin::Tuple { scheme: sb, host: hb, port: pb, .. }) => {
            sa == sb && pa == pb && ha == hb
        },
        // 3.
        _ => false,
    }
}

/// HTML §7.1.1 "same origin-domain": "1. If A and B are the same opaque
/// origin, then return true. 2. If A and B are both tuple origins: 2.1. If
/// A and B's schemes are identical, and their domains are identical and
/// non-null, then return true. 2.2. Otherwise, if A and B are same origin
/// and their domains are both null, return true. 3. Return false."
pub open spec fn same_origin_domain(a: Origin, b: Origin) -> bool {
    match (a, b) {
        // 1.
        (Origin::Opaque(x), Origin::Opaque(y)) => x == y,
        // 2.
        (Origin::Tuple { scheme: sa, domain: da, .. }, Origin::Tuple { scheme: sb, domain: db, .. }) => {
            // 2.1.
            if sa == sb && da == db && da is Some {
                true
            } else {
                // 2.2.
                same_origin(a, b) && da is None && db is None
            }
        },
        // 3.
        _ => false,
    }
}

/// HTML §7.1.1.1 "obtain a site", over the Public Suffix List `rules`.
pub open spec fn obtain_a_site(rules: Seq<clazel_psl::spec::Rule>, origin: Origin) -> Site {
    match origin {
        // 1. "If origin is an opaque origin, then return origin."
        Origin::Opaque(id) => Site::Opaque(id),
        Origin::Tuple { scheme, host, .. } => match clazel_psl::spec::registrable_domain(rules, host) {
            // 2. "If origin's host's registrable domain is null, then
            //    return (origin's scheme, origin's host)."
            None => Site::SchemeAndHost(scheme, host),
            // 3. "Return (origin's scheme, origin's host's registrable
            //    domain)."
            Some(rd) => Site::SchemeAndHost(scheme, clazel_url::host::spec::Host::Domain(rd)),
        },
    }
}

/// HTML §7.1.1.1 "same site" for two sites: "1. If A and B are the same
/// opaque origin, then return true. 2. If A or B is an opaque origin, then
/// return false. 3. If A's and B's scheme values are different, then return
/// false. 4. If A's and B's host values are not equal, then return false.
/// 5. Return true."
pub open spec fn same_site_sites(a: Site, b: Site) -> bool {
    match (a, b) {
        // 1.
        (Site::Opaque(x), Site::Opaque(y)) => x == y,
        // 2.
        (Site::Opaque(_), _) => false,
        (_, Site::Opaque(_)) => false,
        (Site::SchemeAndHost(sa, ha), Site::SchemeAndHost(sb, hb)) => {
            // 3. and 4.
            // 5.
            sa == sb && ha == hb
        },
    }
}

/// HTML §7.1.1.1 "serialization of a site".
pub open spec fn serialization_of_site(site: Site) -> Seq<u32> {
    match site {
        // 1. "If site is an opaque origin, then return "null"."
        Site::Opaque(_) => seq![0x6Eu32, 0x75, 0x6C, 0x6C],
        // 2. "Let result be site[0]." 3. "Append "://" to result."
        // 4. "Append site[1], serialized, to result." 5. "Return result."
        Site::SchemeAndHost(scheme, host) => {
            scheme + seq![0x3Au32, 0x2F, 0x2F] + clazel_url::host::spec::host_serializer(host)
        },
    }
}

/// HTML §7.1.1.1 "schemelessly same site" for two origins.
pub open spec fn schemelessly_same_site(rules: Seq<clazel_psl::spec::Rule>, a: Origin, b: Origin) -> bool {
    match (a, b) {
        // 1. "If A and B are the same opaque origin, then return true."
        (Origin::Opaque(x), Origin::Opaque(y)) => x == y,
        // 2. "If A and B are both tuple origins:"
        (Origin::Tuple { host: host_a, .. }, Origin::Tuple { host: host_b, .. }) => {
            let ra = clazel_psl::spec::registrable_domain(rules, host_a);
            let rb = clazel_psl::spec::registrable_domain(rules, host_b);
            // 2.2. "If hostA equals hostB and hostA's registrable domain is
            //      null, then return true."
            if host_a == host_b && ra is None {
                true
            } else {
                // 2.3. "If hostA's registrable domain equals hostB's
                //      registrable domain and is non-null, then return true."
                // 3. "Return false."
                ra == rb && ra is Some
            }
        },
        // 3.
        _ => false,
    }
}

/// HTML §7.1.1.1 "same site" for two origins: "1. Let siteA be the result of
/// obtaining a site given A. 2. Let siteB [...] given B. 3. If siteA is
/// same site with siteB, then return true. 4. Return false."
pub open spec fn same_site(rules: Seq<clazel_psl::spec::Rule>, a: Origin, b: Origin) -> bool {
    same_site_sites(obtain_a_site(rules, a), obtain_a_site(rules, b))
}

/// `suffix`, prefixed by U+002E (.), matches the end of `s`.
pub open spec fn dot_prefixed_matches_end(suffix: Seq<u32>, s: Seq<u32>) -> bool {
    s.len() >= suffix.len() + 1 && s.skip((s.len() - suffix.len() - 1) as int) == seq![0x2Eu32] + suffix
}

/// HTML §7.1.1.2 "is a registrable domain suffix of or is equal to", for
/// `host_suffix_string_is_empty` (whether hostSuffixString is the empty
/// string), `parsed` (the result of parsing it, `None` for failure) and
/// `original_host`.
pub open spec fn is_registrable_domain_suffix_of_or_equal_to(
    rules: Seq<clazel_psl::spec::Rule>,
    host_suffix_string_is_empty: bool,
    parsed: Option<clazel_url::host::spec::Host>,
    original_host: clazel_url::host::spec::Host,
) -> bool {
    // 1. "If hostSuffixString is the empty string, then return false."
    if host_suffix_string_is_empty {
        false
    } else {
        match parsed {
            // 2. and 3. "If hostSuffix is failure, then return false."
            None => false,
            Some(host_suffix) => if host_suffix != original_host {
                // 4. "If hostSuffix does not equal originalHost:"
                match (host_suffix, original_host) {
                    (clazel_url::host::spec::Host::Domain(hs), clazel_url::host::spec::Host::Domain(oh)) => {
                        // 4.2. "If hostSuffix, prefixed by U+002E (.), does
                        //      not match the end of originalHost, then
                        //      return false."
                        if !dot_prefixed_matches_end(hs, oh) {
                            false
                        } else {
                            // 4.3. "If any of the following are true:
                            //      hostSuffix equals hostSuffix's public
                            //      suffix; or hostSuffix, prefixed by
                            //      U+002E (.), matches the end of
                            //      originalHost's public suffix, then return
                            //      false."
                            let ps_suffix = clazel_psl::spec::public_suffix_of_domain(rules, hs);
                            let ps_original = clazel_psl::spec::public_suffix_of_domain(rules, oh);
                            if ps_suffix == Some(hs) || (ps_original matches Some(p) && dot_prefixed_matches_end(hs, p)) {
                                false
                            } else {
                                // 4.4. "Assert: originalHost's public
                                //      suffix, prefixed by U+002E (.),
                                //      matches the end of hostSuffix."
                                // 5. "Return true."
                                true
                            }
                        }
                    },
                    // 4.1. "If hostSuffix or originalHost is not a domain,
                    //      then return false."
                    _ => false,
                }
            } else {
                // 5. "Return true."
                true
            },
        }
    }
}

// ---------------------------------------------------------------------
// URL §4.7 the origin of a URL.
// ---------------------------------------------------------------------

/// "ftp", "http", "https", "ws" and "wss": the schemes that give a tuple
/// origin (URL §4.7).
pub open spec fn has_tuple_origin_scheme(s: Seq<u32>) -> bool {
    s == clazel_url::url::spec::ftp_str() || s == clazel_url::url::spec::http_str() || s == clazel_url::url::spec::https_str()
        || s == clazel_url::url::spec::ws_str() || s == clazel_url::url::spec::wss_str()
}

/// "`blob`".
pub open spec fn blob_str() -> Seq<u32> {
    seq![0x62u32, 0x6C, 0x6F, 0x62]
}

/// URL §4.7 "origin" of a URL whose scheme is not "blob", with `fresh` the
/// id of "a new opaque origin". A tuple origin needs a host: a special URL
/// other than `file:` always has one, and for one that has none (a URL
/// record the parser would not produce) the origin is new and opaque.
pub open spec fn url_origin_not_blob(url: clazel_url::url::spec::Url, fresh: nat) -> Origin {
    if has_tuple_origin_scheme(url.scheme) {
        match url.host {
            // "Return the tuple origin (url's scheme, url's host, url's
            // port, null)."
            Some(host) => Origin::Tuple { scheme: url.scheme, host, port: url.port, domain: None },
            None => Origin::Opaque(fresh),
        }
    } else {
        // "file": "left as an exercise to the reader. When in doubt, return
        // a new opaque origin." "Otherwise: Return a new opaque origin."
        Origin::Opaque(fresh)
    }
}

/// URL §4.7 "origin" of a URL, with `domain_parser` the URL §3.3 domain
/// parser the basic URL parser runs and `fresh` the id of "a new opaque
/// origin".
pub open spec fn url_origin(url: clazel_url::url::spec::Url, domain_parser: clazel_url::host::spec::DomainParser, fresh: nat) -> Origin {
    if url.scheme == blob_str() {
        // 1. "If url's blob URL entry is non-null, then return [...]" (never:
        //    see the modelling choices).
        // 2. "Let pathURL be the result of parsing the result of URL path
        //    serializing url."
        let path = clazel_url::url::spec::url_path_serializer(url.path);
        if !clazel_encoding::utf8::spec::all_scalar_values(path) {
            Origin::Opaque(fresh)
        } else {
            match clazel_url::url::spec::basic_url_parser(path, None, domain_parser) {
                // 3. "If pathURL is failure, then return a new opaque
                //    origin."
                None => Origin::Opaque(fresh),
                Some(path_url) => {
                    // 4. "If pathURL's scheme is "http", "https", or "file",
                    //    then return pathURL's origin."
                    if path_url.scheme == clazel_url::url::spec::http_str() || path_url.scheme == clazel_url::url::spec::https_str()
                        || path_url.scheme == clazel_url::url::spec::file_str() {
                        url_origin_not_blob(path_url, fresh)
                    } else {
                        // 5. "Return a new opaque origin."
                        Origin::Opaque(fresh)
                    }
                },
            }
        }
    } else {
        url_origin_not_blob(url, fresh)
    }
}

} // verus!
