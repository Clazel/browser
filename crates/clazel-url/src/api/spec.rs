//! Executable-style specification of the URL API setters, transcribed from
//! the WHATWG URL Standard §6.1 "URL class": the setter steps of `href`,
//! `protocol`, `username`, `password`, `host`, `hostname`, `port`,
//! `pathname`, `search` and `hash`. Nothing here runs; it defines what
//! "correct" means. Every definition cites the standard, and each `// N.`
//! comment is the step number in the cited setter.
//!
//! Sources (each pinned; a review is against exactly this text):
//! - URL Standard, Living Standard, `url.bs` at commit
//!   `845bafca22fb0c5a42c4bf384a9bdea525a2f10d` (19 October 2026),
//!   <https://url.spec.whatwg.org/>: §6.1 (the setters). The same commit
//!   as the basic URL parser ([`crate::url::spec`], item 1.10), which
//!   transcribes what the setters call: the basic URL parser with a state
//!   override (§4.4), "cannot have a username/password/port" (§4.2), and
//!   "set the username" and "set the password" (§4.4).
//!
//! **The domain parser is a parameter**, as in [`crate::url::spec`]: the
//! setters that run the basic URL parser take it, every theorem holds for
//! every domain parser unless it says otherwise, and the exec setters are
//! proven equal to these with `clazel-idna`'s.
//!
//! Not transcribed here: the getters (one-liners over the URL record,
//! computed by the conformance test as in item 1.10), the constructor,
//! `parse`, `canParse`, `origin`, `toJSON`, and `searchParams` with the
//! `URLSearchParams` class (§6.2) and `application/x-www-form-urlencoded`
//! (§5), which Phase 1 does not include.
//!
//! Modelling choices (each one is a deliberate, reviewable deviation in form,
//! never in meaning):
//! - **The setters belong to the `URL` class; here they are functions on
//!   the URL record.** A `URL` object "has an associated URL" (a URL
//!   record) and a query object. Each setter is a spec function from
//!   this's URL and the given value to this's URL after the setter steps.
//!   "This's URL" is the `url` argument, and "set this's URL to X" or a
//!   change to one of its components is the result.
//! - **The query object is not modelled.** Its list is `URLSearchParams`
//!   state (§6.2), out of scope; it never changes this's URL. Each step
//!   that only changes it (href setter steps 4 to 6, search setter steps 2
//!   and 6) is a comment saying so.
//! - **"Throw a TypeError"** (href setter step 2) is `None`: the setter
//!   stops and this's URL is unchanged. Every other setter returns a URL.
//! - "The given value" is a USVString, which is a scalar value string: a
//!   `Seq<u32>` (the contracts require scalar values).
//! - "Basic URL parse X with this's URL as url and S as state override" is
//!   [`crate::url::spec::basic_url_parse_in_place`], which gives this's
//!   URL as the parser leaves it, also when the parser returns failure
//!   (see [`crate::url::spec`]'s header): the setters ignore what it
//!   returns. No setter passes a base.

#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The `href` setter (<https://url.spec.whatwg.org/#dom-url-href>).
/// `None` is "throw a TypeError" (this's URL is unchanged).
pub open spec fn href_setter(url: crate::url::spec::Url, value: Seq<u32>, domain_parser: crate::host::spec::DomainParser) -> Option<crate::url::spec::Url> {
    // 1. "Let parsedURL be the result of running the basic URL parser on
    //    the given value."
    match crate::url::spec::basic_url_parser(value, None, domain_parser) {
        // 2. "If parsedURL is failure, then throw a TypeError."
        None => None,
        // 3. "Set this's URL to parsedURL."
        // 4. "Empty this's query object's list." (query object only)
        // 5. "Let query be this's URL's query."
        // 6. "If query is non-null, then set this's query object's list to
        //    the result of parsing query." (query object only)
        Some(parsed_url) => Some(parsed_url),
    }
}

/// The `protocol` setter (<https://url.spec.whatwg.org/#dom-url-protocol>):
/// "basic URL parse the given value, followed by U+003A (:), with this's
/// URL as url and scheme start state as state override."
pub open spec fn protocol_setter(url: crate::url::spec::Url, value: Seq<u32>, domain_parser: crate::host::spec::DomainParser) -> crate::url::spec::Url {
    crate::url::spec::basic_url_parse_in_place(value.push(0x3Au32), url, crate::url::spec::State::SchemeStart, domain_parser)
}

/// The `username` setter (<https://url.spec.whatwg.org/#dom-url-username>).
pub open spec fn username_setter(url: crate::url::spec::Url, value: Seq<u32>) -> crate::url::spec::Url {
    if crate::url::spec::cannot_have_username_password_port(url) {
        // 1. "If this's URL cannot have a username/password/port, then
        //    return."
        url
    } else {
        // 2. "Set the username given this's URL and the given value."
        crate::url::spec::set_the_username(url, value)
    }
}

/// The `password` setter (<https://url.spec.whatwg.org/#dom-url-password>).
pub open spec fn password_setter(url: crate::url::spec::Url, value: Seq<u32>) -> crate::url::spec::Url {
    if crate::url::spec::cannot_have_username_password_port(url) {
        // 1. "If this's URL cannot have a username/password/port, then
        //    return."
        url
    } else {
        // 2. "Set the password given this's URL and the given value."
        crate::url::spec::set_the_password(url, value)
    }
}

/// The `host` setter (<https://url.spec.whatwg.org/#dom-url-host>).
pub open spec fn host_setter(url: crate::url::spec::Url, value: Seq<u32>, domain_parser: crate::host::spec::DomainParser) -> crate::url::spec::Url {
    if crate::url::spec::has_opaque_path(url) {
        // 1. "If this's URL has an opaque path, then return."
        url
    } else {
        // 2. "Basic URL parse the given value with this's URL as url and
        //    host state as state override."
        crate::url::spec::basic_url_parse_in_place(value, url, crate::url::spec::State::Host, domain_parser)
    }
}

/// The `hostname` setter (<https://url.spec.whatwg.org/#dom-url-hostname>).
pub open spec fn hostname_setter(url: crate::url::spec::Url, value: Seq<u32>, domain_parser: crate::host::spec::DomainParser) -> crate::url::spec::Url {
    if crate::url::spec::has_opaque_path(url) {
        // 1. "If this's URL has an opaque path, then return."
        url
    } else {
        // 2. "Basic URL parse the given value with this's URL as url and
        //    hostname state as state override."
        crate::url::spec::basic_url_parse_in_place(value, url, crate::url::spec::State::Hostname, domain_parser)
    }
}

/// The `port` setter (<https://url.spec.whatwg.org/#dom-url-port>).
pub open spec fn port_setter(url: crate::url::spec::Url, value: Seq<u32>, domain_parser: crate::host::spec::DomainParser) -> crate::url::spec::Url {
    if crate::url::spec::cannot_have_username_password_port(url) {
        // 1. "If this's URL cannot have a username/password/port, then
        //    return."
        url
    } else if value.len() == 0 {
        // 2. "If the given value is the empty string, then set this's URL's
        //    port to null."
        crate::url::spec::Url { port: None, ..url }
    } else {
        // 3. "Otherwise, basic URL parse the given value with this's URL as
        //    url and port state as state override."
        crate::url::spec::basic_url_parse_in_place(value, url, crate::url::spec::State::Port, domain_parser)
    }
}

/// The `pathname` setter (<https://url.spec.whatwg.org/#dom-url-pathname>).
pub open spec fn pathname_setter(url: crate::url::spec::Url, value: Seq<u32>, domain_parser: crate::host::spec::DomainParser) -> crate::url::spec::Url {
    if crate::url::spec::has_opaque_path(url) {
        // 1. "If this's URL has an opaque path, then return."
        url
    } else {
        // 2. "Empty this's URL's path." (It is a list: step 1.)
        let url = crate::url::spec::Url { path: crate::url::spec::UrlPath::List(seq![]), ..url };
        // 3. "Basic URL parse the given value with this's URL as url and
        //    path start state as state override."
        crate::url::spec::basic_url_parse_in_place(value, url, crate::url::spec::State::PathStart, domain_parser)
    }
}

/// "The given value with a single leading" `c` "removed, if any" (search
/// setter step 3, hash setter step 2).
pub open spec fn remove_single_leading(value: Seq<u32>, c: u32) -> Seq<u32> {
    if value.len() > 0 && value[0] == c {
        value.subrange(1, value.len() as int)
    } else {
        value
    }
}

/// The `search` setter (<https://url.spec.whatwg.org/#dom-url-search>).
pub open spec fn search_setter(url: crate::url::spec::Url, value: Seq<u32>, domain_parser: crate::host::spec::DomainParser) -> crate::url::spec::Url {
    // 1. "Let url be this's URL."
    if value.len() == 0 {
        // 2. "If the given value is the empty string, then set url's query
        //    to null, empty this's query object's list, and return." (the
        //    query object only for the list)
        crate::url::spec::Url { query: None, ..url }
    } else {
        // 3. "Let input be the given value with a single leading U+003F (?)
        //    removed, if any."
        let input = remove_single_leading(value, 0x3F);
        // 4. "Set url's query to the empty string."
        let url = crate::url::spec::Url { query: Some(seq![]), ..url };
        // 5. "Basic URL parse input with url as url and query state as
        //    state override."
        // 6. "Set this's query object's list to the result of parsing url's
        //    query." (query object only)
        crate::url::spec::basic_url_parse_in_place(input, url, crate::url::spec::State::Query, domain_parser)
    }
}

/// The `hash` setter (<https://url.spec.whatwg.org/#dom-url-hash>).
pub open spec fn hash_setter(url: crate::url::spec::Url, value: Seq<u32>, domain_parser: crate::host::spec::DomainParser) -> crate::url::spec::Url {
    if value.len() == 0 {
        // 1. "If the given value is the empty string, then set this's URL's
        //    fragment to null and return."
        crate::url::spec::Url { fragment: None, ..url }
    } else {
        // 2. "Let input be the given value with a single leading U+0023 (#)
        //    removed, if any."
        let input = remove_single_leading(value, 0x23);
        // 3. "Set this's URL's fragment to the empty string."
        let url = crate::url::spec::Url { fragment: Some(seq![]), ..url };
        // 4. "Basic URL parse input with this's URL as url and fragment
        //    state as state override."
        crate::url::spec::basic_url_parse_in_place(input, url, crate::url::spec::State::Fragment, domain_parser)
    }
}

} // verus!
