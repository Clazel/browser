//! An independent transcription of RFC 6265 (April 2011) §5.3 "Storage
//! Model" and §5.4 "The Cookie Header", written from the RFC text alone.
//!
//! Source: <https://www.rfc-editor.org/rfc/rfc6265.txt>, fetched as plain
//! text and transcribed from the RFC's own numbered steps. The `// N. "..."`
//! comments quote the RFC's words (whitespace re-flowed). Domain-match,
//! path-match and default-path are the proven-correct
//! `*_6265` functions of `crate::matching::independent`.
//!
//! Scope: §5.3 steps 1 to 12, the "expired" eviction paragraph (as
//! [`evict_expired_6265`]), and the end-of-session removal paragraph (as
//! [`end_session_6265`]); §5.4 steps 1 to 4. The "remove excess cookies"
//! limits are optional (MAY) and not modelled. §5.1.2 canonicalization is
//! not transcribed: a canonicalized host is an input ([`Host6265`]).
//!
//! Modelling choices:
//! - Strings are `Seq<u8>`, numbers and times are `int` (seconds). The
//!   cookie jar ("cookie store") is a `Seq<Cookie6265>`, in insertion order.
//! - A canonicalized request-host is a [`Host6265`] (its name and whether it
//!   is an IP address). The request-uri is a [`Request6265`]: `host` is
//!   `None` when the host fails to canonicalize, `path` is the uri-path as
//!   given (used as is by default-path and path-match), and `secure` is
//!   whether the scheme denotes a "secure" protocol (§5.3 does not use it).
//!   A request whose host is `None` stores no cookie (§5.3) and retrieves no
//!   cookie (§5.4): the RFC does not say, this is the plain reading that
//!   "canonicalized request-host" must exist.
//! - The parsed cookie-attribute-list of §5.2 is a `Seq<Attr6265>`. As
//!   §5.2.1, §5.2.2 and §5.2.3 produce them, `Expires` carries the parsed
//!   expiry date and `MaxAge` the expiry-time already computed from
//!   delta-seconds (§5.2.2: "the current date and time plus delta-seconds
//!   seconds", or the earliest date), both as absolute `int` times;
//!   `Domain` is lower-cased with any leading dot removed (§5.2.3); `Path`
//!   is the value §5.2.4 appends. Attributes are used as listed, nothing is
//!   re-validated here. "The last attribute with an attribute-name of X"
//!   is the right-most `X` entry.
//! - "The latest representable date" (§5.3 step 3) is the constant
//!   [`latest_date_6265`], `i64::MAX`. Callers' `now` is assumed to be below
//!   it.
//! - A cookie's `domain` is a [`Host6265`] so its IP-ness is kept. It is
//!   only a name comparison in the algorithms (domain-match needs "is a host
//!   name" of the request-host only). When set from the request-host it
//!   copies `is_ip`; when set from the domain-attribute it is `is_ip` only
//!   if the attribute is identical to the request-host and that host is an
//!   IP address, otherwise the attribute is taken to be a host name.
//! - "The user agent is configured to reject public suffixes" (§5.3 step 5)
//!   is assumed true; "is a public suffix" is the parameter
//!   `is_public_suffix`, applied to the domain-attribute exactly as the RFC
//!   says, including the empty string (step 5 is not skipped when the
//!   attribute is absent; a predicate that holds for the empty string would
//!   then drop every cookie with no Domain attribute unless the host is the
//!   empty string, which is the literal reading).
//! - §5.3 step 1 (MAY ignore) is not modelled: it is a choice of the agent
//!   that precedes this function. The "non-HTTP API" tests are the
//!   `from_non_http_api` flag.
//! - Steps 11 and 12 on the jar: "the cookie store contains a cookie with
//!   the same name, domain, and path" compares the three as byte strings
//!   (the domain by name only). The RFC's invariant is at most one such
//!   cookie; if a jar broke it, old-cookie is the first one in jar order and
//!   only that one is removed. "Insert" appends at the end of the jar (the
//!   RFC says no position). The new cookie keeps the old cookie's
//!   creation-time. If step 10 or 11.2 aborts, the jar is returned
//!   unchanged. [`store_cookie_6265`] ends at step 12 and does not evict
//!   expired cookies: that is [`evict_expired_6265`].
//! - "Expired" is `expiry_time < now` ("an expiry date in the past").
//!   Eviction is only the first removal priority; per-domain and total
//!   limits are not modelled. Session end removes `persistent_flag ==
//!   false` cookies.
//! - §5.4 "MAY omit the Cookie header in its entirety" is a choice of the
//!   agent and not modelled, nor is the header-count rule. "The cookie
//!   store" selection is step 1 only; its result keeps jar order.
//! - §5.4 step 1 "the cookie-string is being generated for a 'non-HTTP'
//!   API" is the `from_non_http_api` retrieval flag.
//! - §5.4 step 2 is a SHOULD; it is modelled as done. The order is a stable
//!   insertion sort (recursion), "listed before" being strictly longer
//!   path, or equal path length and strictly earlier creation-time. Ties
//!   keep jar order.
//! - §5.4 step 3 updates the last-access-time of each cookie in the
//!   cookie-list. The jar is updated as a whole by [`update_last_access_6265`],
//!   changing exactly the cookies that satisfy the step 1 conditions (the
//!   jar's order and the other cookies are untouched). Step 3 comes after
//!   the sort of step 2 but neither depends on the other's result.
//! - §5.4 step 4 always outputs the "=" even when the name is empty (the
//!   RFC has no exception). The cookie-string is a `Seq<u8>`.
//!
//! RFC errata-like places: none that change behaviour. Noted: step 5's
//! public-suffix test is read before the empty-domain-attribute test of
//! step 6; §5.2.2's Max-Age is stored as an absolute time though step 3
//! says "attribute-value" (both as above); "same name, domain, and path"
//! ignores the host-only-flag, as written.

#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// A canonicalized host: its name and whether it is an IP address.
pub struct Host6265 {
    /// The canonicalized host name or address text.
    pub name: Seq<u8>,
    /// The host is an IP address.
    pub is_ip: bool,
}

/// The request-uri, as far as §5.3 and §5.4 look at it.
pub struct Request6265 {
    /// The canonicalized request-host; `None` if it fails to canonicalize.
    pub host: Option<Host6265>,
    /// The uri-path of the request-uri.
    pub path: Seq<u8>,
    /// The scheme denotes a "secure" protocol.
    pub secure: bool,
}

/// A stored cookie (§5.3: "name, value, expiry-time, domain, path,
/// creation-time, last-access-time, persistent-flag, host-only-flag,
/// secure-only-flag, and http-only-flag").
pub struct Cookie6265 {
    /// name.
    pub name: Seq<u8>,
    /// value.
    pub value: Seq<u8>,
    /// expiry-time.
    pub expiry_time: int,
    /// domain.
    pub domain: Host6265,
    /// path.
    pub path: Seq<u8>,
    /// creation-time.
    pub creation_time: int,
    /// last-access-time.
    pub last_access_time: int,
    /// persistent-flag.
    pub persistent_flag: bool,
    /// host-only-flag.
    pub host_only_flag: bool,
    /// secure-only-flag.
    pub secure_only_flag: bool,
    /// http-only-flag.
    pub http_only_flag: bool,
}

/// An entry of the cookie-attribute-list (§5.2), after parsing.
pub enum Attr6265 {
    /// "Expires", with the parsed expiry date.
    Expires(int),
    /// "Max-Age", with the expiry-time §5.2.2 computes.
    MaxAge(int),
    /// "Domain", lower-cased, without a leading dot.
    Domain(Seq<u8>),
    /// "Path".
    Path(Seq<u8>),
    /// "Secure".
    Secure,
    /// "HttpOnly".
    HttpOnly,
}

/// "The latest representable date" (§5.3 step 3).
pub open spec fn latest_date_6265() -> int {
    0x7FFF_FFFF_FFFF_FFFFint
}

// ---------------------------------------------------------------------------
// "The last attribute in the cookie-attribute-list with an attribute-name of X"
// ---------------------------------------------------------------------------

/// The attribute-value of the last "Max-Age" attribute, if any.
pub open spec fn last_max_age_6265(attrs: Seq<Attr6265>) -> Option<int>
    decreases attrs.len(),
{
    if attrs.len() == 0 {
        None
    } else {
        match attrs[attrs.len() - 1] {
            Attr6265::MaxAge(v) => Some(v),
            _ => last_max_age_6265(attrs.subrange(0, attrs.len() - 1)),
        }
    }
}

/// The attribute-value of the last "Expires" attribute, if any.
pub open spec fn last_expires_6265(attrs: Seq<Attr6265>) -> Option<int>
    decreases attrs.len(),
{
    if attrs.len() == 0 {
        None
    } else {
        match attrs[attrs.len() - 1] {
            Attr6265::Expires(v) => Some(v),
            _ => last_expires_6265(attrs.subrange(0, attrs.len() - 1)),
        }
    }
}

/// The attribute-value of the last "Domain" attribute, if any.
pub open spec fn last_domain_6265(attrs: Seq<Attr6265>) -> Option<Seq<u8>>
    decreases attrs.len(),
{
    if attrs.len() == 0 {
        None
    } else {
        match attrs[attrs.len() - 1] {
            Attr6265::Domain(v) => Some(v),
            _ => last_domain_6265(attrs.subrange(0, attrs.len() - 1)),
        }
    }
}

/// The attribute-value of the last "Path" attribute, if any.
pub open spec fn last_path_6265(attrs: Seq<Attr6265>) -> Option<Seq<u8>>
    decreases attrs.len(),
{
    if attrs.len() == 0 {
        None
    } else {
        match attrs[attrs.len() - 1] {
            Attr6265::Path(v) => Some(v),
            _ => last_path_6265(attrs.subrange(0, attrs.len() - 1)),
        }
    }
}

/// The list "contains an attribute with an attribute-name of" "Secure".
pub open spec fn has_secure_6265(attrs: Seq<Attr6265>) -> bool {
    exists|i: int| 0 <= i < attrs.len() && attrs[i] === Attr6265::Secure
}

/// The list "contains an attribute with an attribute-name of" "HttpOnly".
pub open spec fn has_http_only_6265(attrs: Seq<Attr6265>) -> bool {
    exists|i: int| 0 <= i < attrs.len() && attrs[i] === Attr6265::HttpOnly
}

// ---------------------------------------------------------------------------
// 5.3 Storage Model
// ---------------------------------------------------------------------------

/// RFC 6265 §5.3 steps 1 to 10: the newly created cookie when the user agent
/// "receives a cookie" from the request-uri `req` with name `cookie_name`,
/// value `cookie_value` and `cookie_attribute_list`, or `None` for "ignore
/// the cookie entirely". `now` is "the current date and time".
pub open spec fn receive_cookie_6265(
    is_public_suffix: spec_fn(Seq<u8>) -> bool,
    req: Request6265,
    from_non_http_api: bool,
    cookie_name: Seq<u8>,
    cookie_value: Seq<u8>,
    cookie_attribute_list: Seq<Attr6265>,
    now: int,
) -> Option<Cookie6265> {
    match req.host {
        // (A request-host that failed to canonicalize: see the header.)
        None => None,
        Some(request_host) => {
            // 1. "A user agent MAY ignore a received cookie in its entirety."
            //    (Not modelled, see the header.)
            // 3. "If the cookie-attribute-list contains an attribute with an
            //    attribute-name of "Max-Age": Set the cookie's persistent-flag
            //    to true. Set the cookie's expiry-time to attribute-value of
            //    the last attribute in the cookie-attribute-list with an
            //    attribute-name of "Max-Age". Otherwise, if the
            //    cookie-attribute-list contains an attribute with an
            //    attribute-name of "Expires" (and does not contain an
            //    attribute with an attribute-name of "Max-Age"): Set the
            //    cookie's persistent-flag to true. Set the cookie's
            //    expiry-time to attribute-value of the last attribute in the
            //    cookie-attribute-list with an attribute-name of "Expires".
            //    Otherwise: Set the cookie's persistent-flag to false. Set
            //    the cookie's expiry-time to the latest representable date."
            let (persistent_flag, expiry_time): (bool, int) = match last_max_age_6265(
                cookie_attribute_list,
            ) {
                Some(v) => (true, v),
                None => match last_expires_6265(cookie_attribute_list) {
                    Some(v) => (true, v),
                    None => (false, latest_date_6265()),
                },
            };
            // 4. "If the cookie-attribute-list contains an attribute with an
            //    attribute-name of "Domain": Let the domain-attribute be the
            //    attribute-value of the last attribute in the
            //    cookie-attribute-list with an attribute-name of "Domain".
            //    Otherwise: Let the domain-attribute be the empty string."
            let domain_attribute_4: Seq<u8> = match last_domain_6265(cookie_attribute_list) {
                Some(v) => v,
                None => Seq::<u8>::empty(),
            };
            // 5. "If the user agent is configured to reject "public suffixes"
            //    and the domain-attribute is a public suffix: If the
            //    domain-attribute is identical to the canonicalized
            //    request-host: Let the domain-attribute be the empty string.
            //    Otherwise: Ignore the cookie entirely and abort these steps."
            //    (The user agent is assumed configured to reject.) `None`
            //    here is the abort.
            let domain_attribute_5: Option<Seq<u8>> = if is_public_suffix(domain_attribute_4) {
                if domain_attribute_4 == request_host.name {
                    Some(Seq::<u8>::empty())
                } else {
                    None
                }
            } else {
                Some(domain_attribute_4)
            };
            match domain_attribute_5 {
                None => None,
                Some(domain_attribute) => {
                    // 6. "If the domain-attribute is non-empty: If the
                    //    canonicalized request-host does not domain-match the
                    //    domain-attribute: Ignore the cookie entirely and
                    //    abort these steps. Otherwise: Set the cookie's
                    //    host-only-flag to false. Set the cookie's domain to
                    //    the domain-attribute. Otherwise: Set the cookie's
                    //    host-only-flag to true. Set the cookie's domain to
                    //    the canonicalized request-host."
                    let domain_step: Option<(bool, Host6265)> = if domain_attribute.len() > 0 {
                        if !crate::matching::independent::domain_matches_6265(
                            request_host.name,
                            !request_host.is_ip,
                            domain_attribute,
                        ) {
                            None
                        } else {
                            Some((
                                false,
                                Host6265 {
                                    name: domain_attribute,
                                    is_ip: request_host.is_ip && domain_attribute
                                        == request_host.name,
                                },
                            ))
                        }
                    } else {
                        Some((true, request_host))
                    };
                    match domain_step {
                        None => None,
                        Some((host_only_flag, domain)) => {
                            // 7. "If the cookie-attribute-list contains an
                            //    attribute with an attribute-name of "Path",
                            //    set the cookie's path to attribute-value of
                            //    the last attribute in the
                            //    cookie-attribute-list with an attribute-name
                            //    of "Path". Otherwise, set the cookie's path
                            //    to the default-path of the request-uri."
                            let path: Seq<u8> = match last_path_6265(cookie_attribute_list) {
                                Some(v) => v,
                                None => crate::matching::independent::default_path_6265(req.path),
                            };
                            // 8. "If the cookie-attribute-list contains an
                            //    attribute with an attribute-name of "Secure",
                            //    set the cookie's secure-only-flag to true.
                            //    Otherwise, set the cookie's secure-only-flag
                            //    to false."
                            let secure_only_flag = has_secure_6265(cookie_attribute_list);
                            // 9. "If the cookie-attribute-list contains an
                            //    attribute with an attribute-name of
                            //    "HttpOnly", set the cookie's http-only-flag
                            //    to true. Otherwise, set the cookie's
                            //    http-only-flag to false."
                            let http_only_flag = has_http_only_6265(cookie_attribute_list);
                            // 10. "If the cookie was received from a
                            //     "non-HTTP" API and the cookie's
                            //     http-only-flag is set, abort these steps
                            //     and ignore the cookie entirely."
                            if from_non_http_api && http_only_flag {
                                None
                            } else {
                                // 2. "Create a new cookie with name
                                //    cookie-name, value cookie-value. Set the
                                //    creation-time and the last-access-time
                                //    to the current date and time." (Placed
                                //    here, where the cookie is complete;
                                //    steps 3 to 9 set the other fields.)
                                Some(
                                    Cookie6265 {
                                        name: cookie_name,
                                        value: cookie_value,
                                        expiry_time,
                                        domain,
                                        path,
                                        creation_time: now,
                                        last_access_time: now,
                                        persistent_flag,
                                        host_only_flag,
                                        secure_only_flag,
                                        http_only_flag,
                                    },
                                )
                            }
                        },
                    }
                },
            }
        },
    }
}

/// The index of the cookie in `jar` "with the same name, domain, and path"
/// as `name`, `domain` and `path` (the first, in jar order), if any.
pub open spec fn find_old_cookie_6265(
    jar: Seq<Cookie6265>,
    name: Seq<u8>,
    domain: Seq<u8>,
    path: Seq<u8>,
) -> Option<int>
    decreases jar.len(),
{
    if jar.len() == 0 {
        None
    } else if jar[0].name == name && jar[0].domain.name == domain && jar[0].path == path {
        Some(0int)
    } else {
        match find_old_cookie_6265(jar.skip(1), name, domain, path) {
            Some(i) => Some(i + 1),
            None => None,
        }
    }
}

/// RFC 6265 §5.3 steps 11 and 12: the jar after the newly created cookie
/// `new_cookie` is handled against the cookie store `jar`.
pub open spec fn insert_cookie_6265(
    jar: Seq<Cookie6265>,
    new_cookie: Cookie6265,
    from_non_http_api: bool,
) -> Seq<Cookie6265> {
    // 11. "If the cookie store contains a cookie with the same name, domain,
    //     and path as the newly created cookie:"
    match find_old_cookie_6265(jar, new_cookie.name, new_cookie.domain.name, new_cookie.path) {
        Some(i) => {
            // 11.1. "Let old-cookie be the existing cookie with the same
            //       name, domain, and path as the newly created cookie."
            let old_cookie = jar[i];
            // 11.2. "If the newly created cookie was received from a
            //       "non-HTTP" API and the old-cookie's http-only-flag is
            //       set, abort these steps and ignore the newly created
            //       cookie entirely."
            if from_non_http_api && old_cookie.http_only_flag {
                jar
            } else {
                // 11.3. "Update the creation-time of the newly created
                //       cookie to match the creation-time of the old-cookie."
                let updated = Cookie6265 { creation_time: old_cookie.creation_time, ..new_cookie };
                // 11.4. "Remove the old-cookie from the cookie store."
                let removed = jar.remove(i);
                // 12. "Insert the newly created cookie into the cookie store."
                removed.push(updated)
            }
        },
        // 12. "Insert the newly created cookie into the cookie store."
        None => jar.push(new_cookie),
    }
}

/// RFC 6265 §5.3 steps 1 to 12: the cookie store after the user agent
/// "receives a cookie". The expired-cookie eviction that follows is
/// [`evict_expired_6265`].
pub open spec fn store_cookie_6265(
    is_public_suffix: spec_fn(Seq<u8>) -> bool,
    jar: Seq<Cookie6265>,
    req: Request6265,
    from_non_http_api: bool,
    cookie_name: Seq<u8>,
    cookie_value: Seq<u8>,
    cookie_attribute_list: Seq<Attr6265>,
    now: int,
) -> Seq<Cookie6265> {
    match receive_cookie_6265(
        is_public_suffix,
        req,
        from_non_http_api,
        cookie_name,
        cookie_value,
        cookie_attribute_list,
        now,
    ) {
        // "Ignore the cookie entirely" (steps 5, 6, 10).
        None => jar,
        Some(new_cookie) => insert_cookie_6265(jar, new_cookie, from_non_http_api),
    }
}

/// RFC 6265 §5.3: "A cookie is "expired" if the cookie has an expiry date in
/// the past." (`now` is the present.)
pub open spec fn is_expired_6265(c: Cookie6265, now: int) -> bool {
    c.expiry_time < now
}

/// RFC 6265 §5.3: "The user agent MUST evict all expired cookies from the
/// cookie store if, at any time, an expired cookie exists in the cookie
/// store." Order of the others is kept.
pub open spec fn evict_expired_6265(jar: Seq<Cookie6265>, now: int) -> Seq<Cookie6265> {
    jar.filter(|c: Cookie6265| !is_expired_6265(c, now))
}

/// RFC 6265 §5.3: "When "the current session is over" ..., the user agent
/// MUST remove from the cookie store all cookies with the persistent-flag set
/// to false."
pub open spec fn end_session_6265(jar: Seq<Cookie6265>) -> Seq<Cookie6265> {
    jar.filter(|c: Cookie6265| c.persistent_flag)
}

// ---------------------------------------------------------------------------
// 5.4 The Cookie Header
// ---------------------------------------------------------------------------

/// RFC 6265 §5.4 step 1: whether `c` is in the cookie-list for a request to
/// `req`, `from_non_http_api` being the "non-HTTP" API test of the last
/// requirement.
pub open spec fn in_cookie_list_6265(c: Cookie6265, req: Request6265, from_non_http_api: bool) -> bool {
    match req.host {
        // (No canonicalized request-host: nothing matches, see the header.)
        None => false,
        Some(request_host) => {
            // "*  Either: The cookie's host-only-flag is true and the
            //  canonicalized request-host is identical to the cookie's
            //  domain. Or: The cookie's host-only-flag is false and the
            //  canonicalized request-host domain-matches the cookie's
            //  domain."
            (if c.host_only_flag {
                request_host.name == c.domain.name
            } else {
                crate::matching::independent::domain_matches_6265(request_host.name, !request_host.is_ip, c.domain.name)
            })
            // "*  The request-uri's path path-matches the cookie's path."
            && crate::matching::independent::path_matches_6265(req.path, c.path)
            // "*  If the cookie's secure-only-flag is true, then the
            //  request-uri's scheme must denote a "secure" protocol (as
            //  defined by the user agent)."
            && (c.secure_only_flag ==> req.secure)
            // "*  If the cookie's http-only-flag is true, then exclude the
            //  cookie if the cookie-string is being generated for a
            //  "non-HTTP" API (as defined by the user agent)."
            && (c.http_only_flag ==> !from_non_http_api)
        },
    }
}

/// RFC 6265 §5.4 step 1: "Let cookie-list be the set of cookies from the
/// cookie store that meets all of the following requirements". A set in
/// jar order.
pub open spec fn cookie_list_unsorted_6265(
    jar: Seq<Cookie6265>,
    req: Request6265,
    from_non_http_api: bool,
) -> Seq<Cookie6265> {
    jar.filter(|c: Cookie6265| in_cookie_list_6265(c, req, from_non_http_api))
}

/// §5.4 step 2: `a` is "listed before" `b`: "Cookies with longer paths are
/// listed before cookies with shorter paths. Among cookies that have
/// equal-length path fields, cookies with earlier creation-times are listed
/// before cookies with later creation-times."
pub open spec fn listed_before_6265(a: Cookie6265, b: Cookie6265) -> bool {
    a.path.len() > b.path.len() || (a.path.len() == b.path.len() && a.creation_time
        < b.creation_time)
}

/// Insert `c` into the sorted list `sorted` after every cookie it is not
/// listed before, so that ties keep their earlier position.
pub open spec fn insert_sorted_6265(sorted: Seq<Cookie6265>, c: Cookie6265) -> Seq<Cookie6265>
    decreases sorted.len(),
{
    if sorted.len() == 0 {
        seq![c]
    } else if listed_before_6265(c, sorted[sorted.len() - 1]) {
        insert_sorted_6265(sorted.subrange(0, sorted.len() - 1), c).push(sorted[sorted.len() - 1])
    } else {
        sorted.push(c)
    }
}

/// RFC 6265 §5.4 step 2: "The user agent SHOULD sort the cookie-list in the
/// following order": a stable insertion sort by [`listed_before_6265`].
pub open spec fn sort_cookie_list_6265(list: Seq<Cookie6265>) -> Seq<Cookie6265>
    decreases list.len(),
{
    if list.len() == 0 {
        Seq::<Cookie6265>::empty()
    } else {
        insert_sorted_6265(
            sort_cookie_list_6265(list.subrange(0, list.len() - 1)),
            list[list.len() - 1],
        )
    }
}

/// RFC 6265 §5.4 steps 1 and 2: the sorted cookie-list.
pub open spec fn cookie_list_6265(
    jar: Seq<Cookie6265>,
    req: Request6265,
    from_non_http_api: bool,
) -> Seq<Cookie6265> {
    sort_cookie_list_6265(cookie_list_unsorted_6265(jar, req, from_non_http_api))
}

/// RFC 6265 §5.4 step 3: "Update the last-access-time of each cookie in the
/// cookie-list to the current date and time." As the new jar: exactly the
/// cookies of [`in_cookie_list_6265`] change.
pub open spec fn update_last_access_6265(
    jar: Seq<Cookie6265>,
    req: Request6265,
    from_non_http_api: bool,
    now: int,
) -> Seq<Cookie6265> {
    jar.map_values(
        |c: Cookie6265|
            if in_cookie_list_6265(c, req, from_non_http_api) {
                Cookie6265 { last_access_time: now, ..c }
            } else {
                c
            },
    )
}

/// RFC 6265 §5.4 step 4: "Serialize the cookie-list into a cookie-string by
/// processing each cookie in the cookie-list in order".
pub open spec fn serialize_cookie_list_6265(list: Seq<Cookie6265>) -> Seq<u8>
    decreases list.len(),
{
    if list.len() == 0 {
        Seq::<u8>::empty()
    } else {
        // 4.1. "Output the cookie's name, the %x3D ("=") character, and the
        //      cookie's value."
        let first = list[0];
        let item = first.name + seq![0x3Du8] + first.value;
        // 4.2. "If there is an unprocessed cookie in the cookie-list, output
        //      the characters %x3B and %x20 ("; ")."
        if list.len() > 1 {
            item + seq![0x3Bu8, 0x20u8] + serialize_cookie_list_6265(list.skip(1))
        } else {
            item
        }
    }
}

/// RFC 6265 §5.4: the cookie-string for a request, steps 1, 2 and 4 (step 3
/// changes only the jar: [`update_last_access_6265`]).
pub open spec fn cookie_string_6265(
    jar: Seq<Cookie6265>,
    req: Request6265,
    from_non_http_api: bool,
) -> Seq<u8> {
    serialize_cookie_list_6265(cookie_list_6265(jar, req, from_non_http_api))
}

} // verus!
