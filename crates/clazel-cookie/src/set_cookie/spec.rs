//! RFC 6265bis §5.4 (cookie name prefixes), §5.5 (cookie lifetime limits)
//! and §5.6 (the Set-Cookie header field, with §5.6.1 to §5.6.7), the
//! user agent's parse of a set-cookie-string, transcribed. Nothing here
//! runs; it defines what "correct" means. Each `// N.` comment is the step
//! number in the cited algorithm.
//!
//! Source (pinned; a review is against exactly this text):
//! - draft-ietf-httpbis-rfc6265bis-22, "Cookies: HTTP State Management
//!   Mechanism", 1 December 2025 (the latest revision on 21 October 2026;
//!   it has not been published as an RFC),
//!   <https://www.ietf.org/archive/id/draft-ietf-httpbis-rfc6265bis-22.txt>:
//!   §5.4, §5.5, §5.6 to §5.6.7, and the steps of §5.7 that §5.4 says
//!   hold the prefix requirements (20 to 22). §5.1.1 and §5.1.4 are in
//!   `crate::date` and `crate::matching`.
//!
//! Modelling choices (each one a deliberate deviation in form, never in
//! meaning):
//! - A string is a `Seq<u8>` of octets (see [`crate::ascii`]).
//! - Positions, not substrings. The standard's "unparsed-attributes" is
//!   the suffix of the set-cookie-string from a position `pos`; "consume
//!   the characters up to, but not including, the first %x3B" finds the
//!   index of that character ([`find_octet`], which is the length if there
//!   is none). "Return to Step 1" is a recursive call at the new position.
//! - The cookie-attribute-list is a `Seq<Attribute>`, in order. An
//!   attribute's name is the variant, and its value the payload; "Secure"
//!   and "HttpOnly" have the empty value, so no payload.
//! - **Time is a number of seconds since 1601-01-01T00:00:00Z** (`int`; the
//!   epoch of Windows and Chromium, and the earliest instant a cookie-date
//!   denotes, so no instant is negative). The
//!   algorithm needs "the current date and time", so [`parse_a_set_cookie_string`]
//!   takes it as the argument `now`. The "earliest representable date and
//!   time" is the earliest instant a cookie-date can denote, 1601-01-01
//!   (the year the §5.1.1 parser's step 5 sets as its lower bound):
//!   [`earliest_representable()`].
//! - The request-uri enters only as `uri_path`, the path portion of its
//!   URL, for the default-path (§5.1.4), which §5.6.4 step 1 uses.
//! - §5.5's limit is [`cookie_age_limit()`], 400 days (34 560 000 seconds),
//!   the recommended value. The draft lets a user agent choose a smaller
//!   one; ours is fixed, so that the limit is part of what is proven.
//! - Read literally, §5.6.1 steps 3 and 4 compare "the expiry-time" (an
//!   instant) to "cookie-age-limit" (defined as a maximum age, "400 days
//!   in the future or sooner"), then "set the expiry time to
//!   cookie-age-limit in seconds". We specify the evident intent: the
//!   limit for an Expires attribute is `now + cookie_age_limit()`, an
//!   instant, as §5.5 says the lifetime must be limited "400 days in the
//!   future". See `docs/ERRATA.md`.
//! - §5.6.2 step 4's "converted to a base 10 integer" is unbounded: the
//!   attribute-value is at most 1024 octets, so the integer may exceed
//!   any machine word; here it is an `int`.
//! - §5.4 states the prefix requirements are "detailed in the storage model
//!   algorithm defined in Section 5.7" (steps 20 to 22). Those steps read
//!   the secure-only-flag and host-only-flag, which §5.7 sets from the
//!   attribute list and the request. They are the arguments of
//!   [`name_prefix_requirements_met`], so that the storage model (item 2.9)
//!   passes what it computed.
//! - String literals are `Seq<u8>`, written in hex with the text in the
//!   doc comment (`lit_*` at the end of this file).

#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------
// The cookie-attribute-list and the parsed cookie.
// ---------------------------------------------------------------------

/// A SameSite "enforcement" (§5.6.7).
pub enum SameSite {
    /// "Default"
    Default,
    /// "None"
    None,
    /// "Strict"
    Strict,
    /// "Lax"
    Lax,
}

/// An attribute of the cookie-attribute-list: its attribute-name and
/// attribute-value.
pub enum Attribute {
    /// "Expires", with the expiry-time (seconds since 1601).
    Expires(int),
    /// "Max-Age", with the expiry-time (seconds since the epoch).
    MaxAge(int),
    /// "Domain", with the cookie-domain.
    Domain(Seq<u8>),
    /// "Path", with the cookie-path.
    Path(Seq<u8>),
    /// "Secure", with an empty attribute-value.
    Secure,
    /// "HttpOnly", with an empty attribute-value.
    HttpOnly,
    /// "SameSite", with the enforcement.
    SameSite(SameSite),
}

/// What the user agent "receives" (§5.6): "a cookie from the request-uri
/// with name cookie-name, value cookie-value, and attributes
/// cookie-attribute-list".
pub struct SetCookie {
    /// cookie-name.
    pub name: Seq<u8>,
    /// cookie-value.
    pub value: Seq<u8>,
    /// cookie-attribute-list.
    pub attributes: Seq<Attribute>,
}

// ---------------------------------------------------------------------
// §5.5 Cookie lifetime limits.
// ---------------------------------------------------------------------

/// §5.5: "The limit SHOULD NOT be greater than 400 days (34560000 seconds)
/// in the future. The RECOMMENDED limit is 400 days".
pub open spec fn cookie_age_limit() -> int {
    34560000
}

/// "the earliest representable date and time": 1601-01-01T00:00:00Z.
pub open spec fn earliest_representable() -> int {
    0
}

// ---------------------------------------------------------------------
// §5.6 The Set-Cookie header field.
// ---------------------------------------------------------------------

/// "%x00-08 / %x0A-1F / %x7F character (CTL characters excluding HTAB)".
pub open spec fn is_ctl_excluding_htab(c: u8) -> bool {
    c <= 0x08 || (0x0A <= c <= 0x1F) || c == 0x7F
}

/// `s` contains a CTL character excluding HTAB at index `i` or later.
pub open spec fn contains_ctl_from(s: Seq<u8>, i: nat) -> bool
    decreases s.len() - i
{
    i < s.len() && (is_ctl_excluding_htab(s[i as int]) || contains_ctl_from(s, i + 1))
}

/// `s` contains a CTL character excluding HTAB.
pub open spec fn contains_ctl_excluding_htab(s: Seq<u8>) -> bool {
    contains_ctl_from(s, 0)
}

/// Every octet of `s` from index `i` is a DIGIT.
pub open spec fn all_digits_from(s: Seq<u8>, i: nat) -> bool
    decreases s.len() - i
{
    i >= s.len() || (crate::ascii::is_digit(s[i as int]) && all_digits_from(s, i + 1))
}

/// §5.6.1: process an Expires attribute-value. `None`: "ignore the cookie-av".
pub open spec fn process_expires(attribute_value: Seq<u8>, now: int) -> Option<Attribute> {
    // 1. "Let the expiry-time be the result of parsing the attribute-value
    //    as cookie-date (see Section 5.1.1)."
    match crate::date::spec::parse_a_cookie_date(attribute_value) {
        // 2. "If the attribute-value failed to parse as a cookie date,
        //    ignore the cookie-av."
        None => None,
        Some(date) => {
            let expiry_time = crate::date::spec::seconds_since_1601(date);
            // 3. "Let cookie-age-limit be the maximum age of the cookie."
            //    (An instant here: see the modelling choices.)
            let limit = now + cookie_age_limit();
            // 4. "If the expiry-time is more than cookie-age-limit, the user
            //    agent MUST set the expiry time to cookie-age-limit."
            let expiry_time = if expiry_time > limit { limit } else { expiry_time };
            // 5. "If the expiry-time is earlier than the earliest date the
            //    user agent can represent, the user agent MAY replace the
            //    expiry-time with the earliest representable date." (Never
            //    the case: the earliest date a cookie-date denotes is
            //    [`earliest_representable()`]. Not applied; it would change
            //    nothing.)
            // 6. "Append an attribute to the cookie-attribute-list with an
            //    attribute-name of Expires and an attribute-value of
            //    expiry-time."
            Some(Attribute::Expires(expiry_time))
        },
    }
}

/// §5.6.2 steps 1 to 3: the attribute-value is acceptable.
pub open spec fn max_age_value_acceptable(attribute_value: Seq<u8>) -> bool {
    // 1. "If the attribute-value is empty, ignore the cookie-av."
    attribute_value.len() > 0
    // 2. "If the first character of the attribute-value is neither a DIGIT,
    //    nor a "-" character followed by a DIGIT, ignore the cookie-av."
    && (crate::ascii::is_digit(attribute_value[0]) || (attribute_value[0] == 0x2D && attribute_value.len() > 1
        && crate::ascii::is_digit(attribute_value[1])))
    // 3. "If the remainder of attribute-value contains a non-DIGIT
    //    character, ignore the cookie-av."
    && all_digits_from(attribute_value, 1)
}

/// §5.6.2 step 4: "Let delta-seconds be the attribute-value converted to a
/// base 10 integer." (For an acceptable attribute-value.)
pub open spec fn delta_seconds(attribute_value: Seq<u8>) -> int {
    if attribute_value[0] == 0x2D { -(crate::ascii::digits_value(attribute_value.skip(1)) as int) } else { crate::ascii::digits_value(attribute_value) as int }
}

/// §5.6.2: process a Max-Age attribute-value, given the current time.
pub open spec fn process_max_age(attribute_value: Seq<u8>, now: int) -> Option<Attribute> {
    if !max_age_value_acceptable(attribute_value) {
        None
    } else {
        // 4. delta-seconds.
        let delta = delta_seconds(attribute_value);
        // 5. "Let cookie-age-limit be the maximum age of the cookie".
        // 6. "Set delta-seconds to the smaller of its present value and
        //    cookie-age-limit."
        let delta = if delta < cookie_age_limit() { delta } else { cookie_age_limit() };
        // 7. "If delta-seconds is less than or equal to zero (0), let
        //    expiry-time be the earliest representable date and time.
        //    Otherwise, let the expiry-time be the current date and time
        //    plus delta-seconds seconds."
        let expiry_time = if delta <= 0 { earliest_representable() } else { now + delta };
        // 8. "Append an attribute to the cookie-attribute-list with an
        //    attribute-name of Max-Age and an attribute-value of
        //    expiry-time."
        Some(Attribute::MaxAge(expiry_time))
    }
}

/// §5.6.3: process a Domain attribute-value.
pub open spec fn process_domain(attribute_value: Seq<u8>) -> Option<Attribute> {
    // 1. "Let cookie-domain be the attribute-value."
    // 2. "If cookie-domain starts with %x2E ("."), let cookie-domain be
    //    cookie-domain without its leading %x2E (".")."
    let cookie_domain = if attribute_value.len() > 0 && attribute_value[0] == 0x2E {
        attribute_value.skip(1)
    } else {
        attribute_value
    };
    // 3. "Convert the cookie-domain to lower case."
    // 4. "Append an attribute to the cookie-attribute-list with an
    //    attribute-name of Domain and an attribute-value of cookie-domain."
    Some(Attribute::Domain(crate::ascii::ascii_lowercase(cookie_domain)))
}

/// §5.6.4: process a Path attribute-value, given the request path.
pub open spec fn process_path(attribute_value: Seq<u8>, uri_path: Seq<u8>) -> Option<Attribute> {
    // 1. "If the attribute-value is empty or if the first character of the
    //    attribute-value is not %x2F ("/"): Let cookie-path be the
    //    default-path. Otherwise: Let cookie-path be the attribute-value."
    let cookie_path = if attribute_value.len() == 0 || attribute_value[0] != 0x2F {
        crate::matching::spec::default_path(uri_path)
    } else {
        attribute_value
    };
    // 2. "Append an attribute to the cookie-attribute-list with an
    //    attribute-name of Path and an attribute-value of cookie-path."
    Some(Attribute::Path(cookie_path))
}

/// §5.6.7: process a SameSite attribute-value.
pub open spec fn process_same_site(attribute_value: Seq<u8>) -> Option<Attribute> {
    // 1. "Let enforcement be "Default"."
    // 2.-4. "If cookie-av's attribute-value is a case-insensitive match for
    //    "None" [...] "Strict" [...] "Lax", set enforcement to" it.
    let enforcement = if crate::ascii::case_insensitive_match(attribute_value, lit_none()) {
        SameSite::None
    } else if crate::ascii::case_insensitive_match(attribute_value, lit_strict()) {
        SameSite::Strict
    } else if crate::ascii::case_insensitive_match(attribute_value, lit_lax()) {
        SameSite::Lax
    } else {
        SameSite::Default
    };
    // 5. "Append an attribute to the cookie-attribute-list with an
    //    attribute-name of "SameSite" and an attribute-value of
    //    enforcement."
    Some(Attribute::SameSite(enforcement))
}

/// §5.6 step 7: "Process the attribute-name and attribute-value according
/// to the requirements in the following subsections. (Notice that
/// attributes with unrecognized attribute-names are ignored.)" `None`: the
/// cookie-av is ignored.
pub open spec fn process_attribute(
    attribute_name: Seq<u8>,
    attribute_value: Seq<u8>,
    uri_path: Seq<u8>,
    now: int,
) -> Option<Attribute> {
    if crate::ascii::case_insensitive_match(attribute_name, lit_expires()) {
        // §5.6.1
        process_expires(attribute_value, now)
    } else if crate::ascii::case_insensitive_match(attribute_name, lit_max_age()) {
        // §5.6.2
        process_max_age(attribute_value, now)
    } else if crate::ascii::case_insensitive_match(attribute_name, lit_domain()) {
        // §5.6.3
        process_domain(attribute_value)
    } else if crate::ascii::case_insensitive_match(attribute_name, lit_path()) {
        // §5.6.4
        process_path(attribute_value, uri_path)
    } else if crate::ascii::case_insensitive_match(attribute_name, lit_secure()) {
        // §5.6.5: "the user agent MUST append an attribute to the
        // cookie-attribute-list with an attribute-name of Secure and an
        // empty attribute-value."
        Some(Attribute::Secure)
    } else if crate::ascii::case_insensitive_match(attribute_name, lit_http_only()) {
        // §5.6.6, likewise.
        Some(Attribute::HttpOnly)
    } else if crate::ascii::case_insensitive_match(attribute_name, lit_same_site()) {
        // §5.6.7
        process_same_site(attribute_value)
    } else {
        None
    }
}

/// §5.6, "parse the unparsed-attributes", with `s[pos..]` as the
/// unparsed-attributes and `list` the cookie-attribute-list so far.
pub open spec fn parse_attributes(s: Seq<u8>, pos: nat, uri_path: Seq<u8>, now: int, list: Seq<Attribute>) -> Seq<Attribute>
    decreases s.len() - pos via parse_attributes_decreases
{
    if pos >= s.len() {
        // 1. "If the unparsed-attributes string is empty, skip the rest of
        //    these steps."
        list
    } else {
        // 2. "Discard the first character of the unparsed-attributes (which
        //    will be a %x3B (";") character)." (The cookie-av starts at
        //    pos + 1.)
        // 3. "If the remaining unparsed-attributes contains a %x3B (";")
        //    character: Consume the characters of the unparsed-attributes
        //    up to, but not including, the first %x3B (";") character.
        //    Otherwise: Consume the remainder of the unparsed-attributes.
        //    Let the cookie-av string be the characters consumed in this
        //    step; unparsed-attributes now contains any remaining
        //    characters." (They start at `end`.)
        let end = crate::ascii::find_octet(s, 0x3B, pos + 1);
        let cookie_av = s.subrange((pos + 1) as int, end as int);
        // 4. "If the cookie-av string contains a %x3D ("=") character: The
        //    (possibly empty) attribute-name string consists of the
        //    characters up to, but not including, the first %x3D ("=")
        //    character, and the (possibly empty) attribute-value string
        //    consists of the characters after the first %x3D ("=")
        //    character. Otherwise: The attribute-name string consists of
        //    the entire cookie-av string, and the attribute-value string is
        //    empty."
        let equals = crate::ascii::find_octet(cookie_av, 0x3D, 0);
        let (attribute_name, attribute_value) = if equals < cookie_av.len() {
            (cookie_av.take(equals as int), cookie_av.skip(equals as int + 1))
        } else {
            (cookie_av, seq![])
        };
        // 5. "Remove any leading or trailing WSP characters from the
        //    attribute-name string and the attribute-value string."
        let attribute_name = crate::ascii::remove_leading_and_trailing_wsp(attribute_name);
        let attribute_value = crate::ascii::remove_leading_and_trailing_wsp(attribute_value);
        if attribute_value.len() > 1024 {
            // 6. "If the attribute-value is longer than 1024 octets, ignore
            //    the cookie-av string and return to Step 1 of this
            //    algorithm."
            parse_attributes(s, end, uri_path, now, list)
        } else {
            // 7. "Process the attribute-name and attribute-value according
            //    to the requirements in the following subsections."
            let list = match process_attribute(attribute_name, attribute_value, uri_path, now) {
                Some(attribute) => list.push(attribute),
                None => list,
            };
            // 8. "Return to Step 1 of this algorithm."
            parse_attributes(s, end, uri_path, now, list)
        }
    }
}

/// Termination of [`parse_attributes`]: the next position is past the one
/// before, because a search starting at `pos + 1` never returns less.
#[via_fn]
pub proof fn parse_attributes_decreases(s: Seq<u8>, pos: nat, uri_path: Seq<u8>, now: int, list: Seq<Attribute>) {
    super::termination::lemma_find_octet_bounds(s, 0x3B, pos + 1);
}

/// §5.6, "parse a set-cookie-string": the cookie the user agent receives
/// from a request to a URL whose path is `uri_path`, at time `now`; `None`
/// is "ignore the set-cookie-string entirely".
pub open spec fn parse_a_set_cookie_string(s: Seq<u8>, uri_path: Seq<u8>, now: int) -> Option<SetCookie> {
    // 1. "If the set-cookie-string contains a %x00-08 / %x0A-1F / %x7F
    //    character (CTL characters excluding HTAB): Abort this algorithm
    //    and ignore the set-cookie-string entirely."
    if contains_ctl_excluding_htab(s) {
        None
    } else {
        // 2. "If the set-cookie-string contains a %x3B (";") character: The
        //    name-value-pair string consists of the characters up to, but
        //    not including, the first %x3B (";"), and the unparsed-
        //    attributes consist of the remainder of the set-cookie-string
        //    (including the %x3B (";") in question). Otherwise: The
        //    name-value-pair string consists of all the characters
        //    contained in the set-cookie-string, and the unparsed-
        //    attributes is the empty string."
        let semicolon = crate::ascii::find_octet(s, 0x3B, 0);
        let name_value_pair = s.subrange(0, semicolon as int);
        // 3. "If the name-value-pair string lacks a %x3D ("=") character,
        //    then the name string is empty, and the value string is the
        //    value of name-value-pair. Otherwise, the (possibly empty)
        //    name string consists of the characters up to, but not
        //    including, the first %x3D ("=") character, and the (possibly
        //    empty) value string consists of the characters after the first
        //    %x3D ("=") character."
        let equals = crate::ascii::find_octet(name_value_pair, 0x3D, 0);
        let (name_string, value_string) = if equals < name_value_pair.len() {
            (name_value_pair.take(equals as int), name_value_pair.skip(equals as int + 1))
        } else {
            (seq![], name_value_pair)
        };
        // 4. "Remove any leading or trailing WSP characters from the name
        //    string and the value string."
        let name_string = crate::ascii::remove_leading_and_trailing_wsp(name_string);
        let value_string = crate::ascii::remove_leading_and_trailing_wsp(value_string);
        // 5. "If the sum of the lengths of the name string and the value
        //    string is more than 4096 octets, abort this algorithm and
        //    ignore the set-cookie-string entirely."
        if name_string.len() + value_string.len() > 4096 {
            None
        } else {
            // 6. "The cookie-name is the name string, and the cookie-value
            //    is the value string." Then the attributes.
            Some(SetCookie {
                name: name_string,
                value: value_string,
                attributes: parse_attributes(s, semicolon, uri_path, now, seq![]),
            })
        }
    }
}

// ---------------------------------------------------------------------
// §5.4 Cookie name prefixes (requirements in §5.7 steps 20 to 22).
// ---------------------------------------------------------------------

/// The cookie's path, "the attribute-value of the last attribute in the
/// cookie-attribute-list with an attribute-name of Path" (§5.7 step 11),
/// if there is one.
pub open spec fn last_path_attribute(list: Seq<Attribute>) -> Option<Seq<u8>>
    decreases list.len()
{
    if list.len() == 0 {
        None
    } else {
        match list[list.len() - 1] {
            Attribute::Path(p) => Some(p),
            _ => last_path_attribute(list.drop_last()),
        }
    }
}

/// The cookie-attribute-list contains a Secure attribute (§5.7 step 12).
pub open spec fn contains_secure_attribute(list: Seq<Attribute>) -> bool {
    exists|i: int| 0 <= i < list.len() && (#[trigger] list[i]) is Secure
}

/// §5.7 steps 20 to 22, the cookie name prefix requirements (§5.4): the
/// newly-created cookie is not ignored for its name, given its
/// secure-only-flag and host-only-flag.
pub open spec fn name_prefix_requirements_met(cookie: SetCookie, secure_only_flag: bool, host_only_flag: bool) -> bool {
    // 20. "If the cookie-name begins with a case-insensitive match for the
    //     string "__Secure-", abort this algorithm and ignore the cookie
    //     entirely unless the cookie's secure-only-flag is true."
    (crate::ascii::begins_with_case_insensitive_match(cookie.name, lit_secure_prefix()) ==> secure_only_flag)
    // 21. "If the cookie-name begins with a case-insensitive match for the
    //     string "__Host-", abort this algorithm and ignore the cookie
    //     entirely unless the cookie meets all the following criteria: 1.
    //     The cookie's secure-only-flag is true. 2. The cookie's
    //     host-only-flag is true. 3. The cookie-attribute-list contains an
    //     attribute with an attribute-name of "Path", and the cookie's path
    //     is /."
    && (crate::ascii::begins_with_case_insensitive_match(cookie.name, lit_host_prefix()) ==> (secure_only_flag && host_only_flag
        && last_path_attribute(cookie.attributes) == Some(seq![0x2Fu8])))
    // 22. "If the cookie-name is empty and either of the following
    //     conditions are true, abort this algorithm and ignore the cookie
    //     entirely: the cookie-value begins with a case-insensitive match
    //     for the string "__Secure-"; the cookie-value begins with a
    //     case-insensitive match for the string "__Host-"."
    && !(cookie.name.len() == 0 && (crate::ascii::begins_with_case_insensitive_match(cookie.value, lit_secure_prefix())
        || crate::ascii::begins_with_case_insensitive_match(cookie.value, lit_host_prefix())))
}

// ---------------------------------------------------------------------
// String literals.
// ---------------------------------------------------------------------

/// "Expires"
pub open spec fn lit_expires() -> Seq<u8> {
    seq![0x45u8, 0x78, 0x70, 0x69, 0x72, 0x65, 0x73]
}

/// "Max-Age"
pub open spec fn lit_max_age() -> Seq<u8> {
    seq![0x4Du8, 0x61, 0x78, 0x2D, 0x41, 0x67, 0x65]
}

/// "Domain"
pub open spec fn lit_domain() -> Seq<u8> {
    seq![0x44u8, 0x6F, 0x6D, 0x61, 0x69, 0x6E]
}

/// "Path"
pub open spec fn lit_path() -> Seq<u8> {
    seq![0x50u8, 0x61, 0x74, 0x68]
}

/// "Secure"
pub open spec fn lit_secure() -> Seq<u8> {
    seq![0x53u8, 0x65, 0x63, 0x75, 0x72, 0x65]
}

/// "HttpOnly"
pub open spec fn lit_http_only() -> Seq<u8> {
    seq![0x48u8, 0x74, 0x74, 0x70, 0x4F, 0x6E, 0x6C, 0x79]
}

/// "SameSite"
pub open spec fn lit_same_site() -> Seq<u8> {
    seq![0x53u8, 0x61, 0x6D, 0x65, 0x53, 0x69, 0x74, 0x65]
}

/// "None"
pub open spec fn lit_none() -> Seq<u8> {
    seq![0x4Eu8, 0x6F, 0x6E, 0x65]
}

/// "Strict"
pub open spec fn lit_strict() -> Seq<u8> {
    seq![0x53u8, 0x74, 0x72, 0x69, 0x63, 0x74]
}

/// "Lax"
pub open spec fn lit_lax() -> Seq<u8> {
    seq![0x4Cu8, 0x61, 0x78]
}

/// "__Secure-"
pub open spec fn lit_secure_prefix() -> Seq<u8> {
    seq![0x5Fu8, 0x5F, 0x53, 0x65, 0x63, 0x75, 0x72, 0x65, 0x2D]
}

/// "__Host-"
pub open spec fn lit_host_prefix() -> Seq<u8> {
    seq![0x5Fu8, 0x5F, 0x48, 0x6F, 0x73, 0x74, 0x2D]
}

} // verus!
