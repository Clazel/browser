//! Executable-style specification of URLs, transcribed from the WHATWG URL
//! Standard §4 "URLs": §4.1 URL representation, §4.2 URL miscellaneous,
//! §4.4 URL parsing (the basic URL parser) and §4.5 URL serializing, with
//! the Infra definitions they use. Nothing here runs; it defines what
//! "correct" means. Every definition cites the standard, and each `// N.`
//! comment is the step number in the cited algorithm (for the basic URL
//! parser's states, the step number within that state).
//!
//! Sources (each pinned; a review is against exactly this text):
//! - URL Standard, Living Standard, `url.bs` at commit
//!   `845bafca22fb0c5a42c4bf384a9bdea525a2f10d` (19 October 2026),
//!   <https://url.spec.whatwg.org/>: §1.2 parsers (pointer, c, remaining,
//!   EOF code point), §4.1, §4.2, §4.4 (the basic URL parser), §4.5. The
//!   same commit as the host parser (item 1.9).
//! - Infra Standard, Living Standard, commit
//!   `459b7829230ad256a690dabd315db974469af8e7` (19 October 2026),
//!   <https://infra.spec.whatwg.org/>: §4.6 ASCII alpha, alphanumeric,
//!   C0 control or space, ASCII tab or newline, ASCII lowercase; §4.7 ASCII
//!   case-insensitive match.
//! - Hosts (URL §3: `Host`, the host parser and serializer) come from
//!   [`crate::host::spec`], percent-encoding (URL §1.3) from
//!   `clazel-percent`'s spec.
//!
//! **The domain parser is a parameter**, as in [`crate::host::spec`]: the
//! host and file host states run the host parser, whose step 6 runs the
//! URL §3.3 domain parser. Every parser definition here takes it as
//! `ctx.domain_parser`, and every theorem and contract holds for every
//! domain parser unless it says otherwise; the exec parser is proven
//! equal to the spec with `clazel-idna`'s domain parser.
//!
//! Not transcribed here: the "URL parser" (§4.4, which adds blob URL
//! entries on top of the basic URL parser), §4.3 URL writing (valid URL
//! strings), §4.6 equivalence, §4.7 origin, §4.8 rendering, and the API.
//!
//! Modelling choices (each one is a deliberate, reviewable deviation in form,
//! never in meaning):
//! - A string is a `Seq<u32>` of code points (as in [`crate::host::spec`]).
//! - Validation errors (URL §1.1) are not modelled: they never change what
//!   the parser returns. Each step that only reports one is a comment
//!   saying so; a step that reports one *and* returns failure returns
//!   failure.
//! - **The encoding is always UTF-8.** The basic URL parser's `encoding`
//!   argument is "a legacy concept only relevant for HTML", and this
//!   project has no other encoder yet (Phase 1 plan: legacy encodings
//!   arrive with HTML in Phase 4). So step 5 ("getting an output
//!   encoding") gives UTF-8, query state step 1 never changes it, and
//!   query state step 2.2's "percent-encode after encoding" is
//!   `clazel-percent`'s UTF-8 transcription.
//! - A URL (§4.1) is the struct [`Url`]. Its port is a `nat`; the port
//!   state only stores values below 2^16 (`lemmas.rs` proves it). Its path
//!   is [`UrlPath`]: `Opaque` is "a URL path segment" (an opaque path) and
//!   `List` "a list of zero or more URL path segments". Its host is
//!   `Option<Host>`, `None` being null; "the empty string" as a host is
//!   `Host::Empty` (§3.1: "An empty host is the empty string").
//! - The blob URL entry (§4.1) is not modelled: only the URL parser, not
//!   the basic URL parser, ever sets it, so it is always null here.
//! - The parser's variables (url, state, buffer, atSignSeen,
//!   insideBrackets, passwordTokenSeen, pointer) are the fields of a
//!   [`Machine`]; its inputs (input, base, state override, and the domain
//!   parser) are a [`Ctx`]. One state's run is one spec function, named
//!   after the state, from a machine to a [`Step`]: failure, "return"
//!   (only reachable with a state override, see below), or the machine
//!   after the run.
//! - Step 9's "Keep running the following state machine" is [`run`]: one
//!   run, then stop if pointer points to the EOF code point, otherwise
//!   increase pointer by 1 and run again. A pointer (§1.2) is an `int`,
//!   and "c" is `c_at` (`None` is the EOF code point). Decreasing the
//!   pointer by 1 and then by the step-9 increase is how a state hands c to
//!   the next state, exactly as in the standard. The termination argument
//!   is in `termination.rs`.
//! - The scheme state's "start over (from the first code point in input)"
//!   sets pointer to −1, so that step 9's increase makes it point to the
//!   first code point. (Pointer is never at the EOF code point there: the
//!   scheme state is only entered after the scheme start state read a
//!   code point.)
//! - Where the standard reads base ("base's scheme") in a state that is
//!   only reachable with a non-null base, [`base_of`] reads it; the null
//!   case gives a new URL, and is unreachable (`lemmas.rs`). Likewise
//!   appending to a path, query or fragment that the standard has always
//!   made a list or a string first ([`path_append`],
//!   [`opaque_path_append`], [`query_append`], [`fragment_append`]): the
//!   other case leaves the value as it is, or appends to the empty string,
//!   and is unreachable.
//! - **State override** (the setters, item 1.11) is transcribed: every
//!   "if state override is given" step is here, with `ctx.state_override`.
//!   The basic URL parser entry point used today, [`basic_url_parser`],
//!   passes none, and so does every contract and theorem in item 1.10; the
//!   state override branches are not yet tested or proven against
//!   anything (item 1.11 does that through `setters_tests.json`). Of
//!   "return" with no value, the setters only need the modified url, so a
//!   "return" is [`Step::Return`] with the url.
//! - [`state_step`], the switch on state, is `#[verifier::opaque]`: a
//!   proof aid only (proofs that need its body `reveal` it), so that
//!   reasoning about [`run`] does not unfold all twenty states at once.
//! - Assertions ("Assert: base's scheme is not "file"") are comments; the
//!   lemmas prove the ones that matter for the results.

#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------
// Infra §4.6 code points, §4.7 strings.
// ---------------------------------------------------------------------

/// Infra §4.6: "An ASCII upper alpha is a code point in the range U+0041
/// (A) to U+005A (Z), inclusive. An ASCII lower alpha is a code point in
/// the range U+0061 (a) to U+007A (z), inclusive. An ASCII alpha is an
/// ASCII upper alpha or ASCII lower alpha."
pub open spec fn is_ascii_alpha(c: u32) -> bool {
    (0x41 <= c <= 0x5A) || (0x61 <= c <= 0x7A)
}

/// Infra §4.6: "An ASCII alphanumeric is an ASCII digit or ASCII alpha."
pub open spec fn is_ascii_alphanumeric(c: u32) -> bool {
    crate::host::spec::is_ascii_digit(c) || is_ascii_alpha(c)
}

/// Infra §4.6: "A C0 control or space is a C0 control or U+0020 SPACE."
/// ("A C0 control is a code point in the range U+0000 NULL to U+001F
/// INFORMATION SEPARATOR ONE, inclusive.")
pub open spec fn is_c0_control_or_space(c: u32) -> bool {
    c <= 0x20
}

/// Infra §4.6: "An ASCII tab or newline is U+0009 TAB, U+000A LF, or
/// U+000D CR."
pub open spec fn is_ascii_tab_or_newline(c: u32) -> bool {
    c == 0x09 || c == 0x0A || c == 0x0D
}

/// Infra §4.6: "To ASCII lowercase a code point, replace every ASCII upper
/// alpha in it with the corresponding code point in ASCII lower alpha."
pub open spec fn ascii_lowercase(c: u32) -> u32 {
    if 0x41 <= c <= 0x5A {
        (c + 0x20) as u32
    } else {
        c
    }
}

/// Infra §4.7: "To ASCII lowercase a string, replace all ASCII upper alphas
/// in the string with their corresponding code point in ASCII lower
/// alpha."
pub open spec fn ascii_lowercase_string(s: Seq<u32>) -> Seq<u32>
    decreases s.len()
{
    if s.len() == 0 {
        seq![]
    } else {
        ascii_lowercase_string(s.drop_last()).push(ascii_lowercase(s.last()))
    }
}

/// Infra §4.7: "A string A is an ASCII case-insensitive match for a string
/// B, if the ASCII lowercase of A is the ASCII lowercase of B."
pub open spec fn is_ascii_case_insensitive_match(a: Seq<u32>, b: Seq<u32>) -> bool {
    ascii_lowercase_string(a) == ascii_lowercase_string(b)
}

/// Remove leading C0 control or space from `s` (basic URL parser step
/// 1.3).
pub open spec fn strip_leading_c0_control_or_space(s: Seq<u32>) -> Seq<u32>
    decreases s.len()
{
    if s.len() > 0 && is_c0_control_or_space(s[0]) {
        strip_leading_c0_control_or_space(s.subrange(1, s.len() as int))
    } else {
        s
    }
}

/// Remove trailing C0 control or space from `s` (basic URL parser step
/// 1.3).
pub open spec fn strip_trailing_c0_control_or_space(s: Seq<u32>) -> Seq<u32>
    decreases s.len()
{
    if s.len() > 0 && is_c0_control_or_space(s.last()) {
        strip_trailing_c0_control_or_space(s.drop_last())
    } else {
        s
    }
}

/// Remove all ASCII tab or newline from `s` (basic URL parser step 3).
pub open spec fn remove_ascii_tab_or_newline(s: Seq<u32>) -> Seq<u32>
    decreases s.len()
{
    if s.len() == 0 {
        seq![]
    } else if is_ascii_tab_or_newline(s.last()) {
        remove_ascii_tab_or_newline(s.drop_last())
    } else {
        remove_ascii_tab_or_newline(s.drop_last()).push(s.last())
    }
}

// ---------------------------------------------------------------------
// ASCII strings the algorithms name.
// ---------------------------------------------------------------------

/// "`file`".
pub open spec fn file_str() -> Seq<u32> {
    seq![0x66u32, 0x69, 0x6C, 0x65]
}

/// "`ftp`".
pub open spec fn ftp_str() -> Seq<u32> {
    seq![0x66u32, 0x74, 0x70]
}

/// "`http`".
pub open spec fn http_str() -> Seq<u32> {
    seq![0x68u32, 0x74, 0x74, 0x70]
}

/// "`https`".
pub open spec fn https_str() -> Seq<u32> {
    seq![0x68u32, 0x74, 0x74, 0x70, 0x73]
}

/// "`ws`".
pub open spec fn ws_str() -> Seq<u32> {
    seq![0x77u32, 0x73]
}

/// "`wss`".
pub open spec fn wss_str() -> Seq<u32> {
    seq![0x77u32, 0x73, 0x73]
}

/// "`localhost`".
pub open spec fn localhost_str() -> Seq<u32> {
    seq![0x6Cu32, 0x6F, 0x63, 0x61, 0x6C, 0x68, 0x6F, 0x73, 0x74]
}

// ---------------------------------------------------------------------
// §4.1 URL representation.
// ---------------------------------------------------------------------

/// §4.1: "A URL path is either a URL path segment or a list of zero or
/// more URL path segments." "A URL path segment is an ASCII string."
pub enum UrlPath {
    /// A URL path that is a URL path segment: an opaque path.
    Opaque(Seq<u32>),
    /// A list of zero or more URL path segments.
    List(Seq<Seq<u32>>),
}

/// §4.1: "A URL is a struct that represents a universal identifier." (The
/// blob URL entry is not modelled; see the header.)
pub struct Url {
    /// "A URL's scheme is an ASCII string that identifies the type of URL
    /// [...]. It is initially the empty string."
    pub scheme: Seq<u32>,
    /// "A URL's username is an ASCII string identifying a username. It is
    /// initially the empty string."
    pub username: Seq<u32>,
    /// "A URL's password is an ASCII string identifying a password. It is
    /// initially the empty string."
    pub password: Seq<u32>,
    /// "A URL's host is null or a host. It is initially null."
    pub host: Option<crate::host::spec::Host>,
    /// "A URL's port is either null or a 16-bit unsigned integer that
    /// identifies a networking port. It is initially null."
    pub port: Option<nat>,
    /// "A URL's path is a URL path, usually identifying a location. It is
    /// initially « »."
    pub path: UrlPath,
    /// "A URL's query is either null or an ASCII string. It is initially
    /// null."
    pub query: Option<Seq<u32>>,
    /// "A URL's fragment is either null or an ASCII string [...]. It is
    /// initially null."
    pub fragment: Option<Seq<u32>>,
}

/// A new URL: every field at its initial value (§4.1).
pub open spec fn new_url() -> Url {
    Url {
        scheme: seq![],
        username: seq![],
        password: seq![],
        host: None,
        port: None,
        path: UrlPath::List(seq![]),
        query: None,
        fragment: None,
    }
}

/// §4.1: "A single-dot URL path segment is a URL path segment that is "."
/// or an ASCII case-insensitive match for "%2e"."
pub open spec fn is_single_dot_segment(s: Seq<u32>) -> bool {
    s == seq![0x2Eu32] || is_ascii_case_insensitive_match(s, seq![0x25u32, 0x32, 0x65])
}

/// §4.1: "A double-dot URL path segment is a URL path segment that is ".."
/// or an ASCII case-insensitive match for ".%2e", "%2e.", or "%2e%2e"."
pub open spec fn is_double_dot_segment(s: Seq<u32>) -> bool {
    s == seq![0x2Eu32, 0x2E]
        || is_ascii_case_insensitive_match(s, seq![0x2Eu32, 0x25, 0x32, 0x65])
        || is_ascii_case_insensitive_match(s, seq![0x25u32, 0x32, 0x65, 0x2E])
        || is_ascii_case_insensitive_match(s, seq![0x25u32, 0x32, 0x65, 0x25, 0x32, 0x65])
}

// ---------------------------------------------------------------------
// §4.2 URL miscellaneous.
// ---------------------------------------------------------------------

/// §4.2: "A special scheme is an ASCII string that is listed in the first
/// column of the following table": ftp, file, http, https, ws, wss.
pub open spec fn is_special_scheme(s: Seq<u32>) -> bool {
    s == ftp_str() || s == file_str() || s == http_str() || s == https_str() || s == ws_str()
        || s == wss_str()
}

/// §4.2: "The default port for a special scheme is listed in the second
/// column on the same row. The default port for any other ASCII string is
/// null." (ftp 21, file null, http 80, https 443, ws 80, wss 443.)
pub open spec fn default_port(s: Seq<u32>) -> Option<nat> {
    if s == ftp_str() {
        Some(21)
    } else if s == http_str() {
        Some(80)
    } else if s == https_str() {
        Some(443)
    } else if s == ws_str() {
        Some(80)
    } else if s == wss_str() {
        Some(443)
    } else {
        None
    }
}

/// §4.2: "A URL is special if its scheme is a special scheme."
pub open spec fn is_special(url: Url) -> bool {
    is_special_scheme(url.scheme)
}

/// §4.2: "A URL includes credentials if its username or password is not
/// the empty string."
pub open spec fn includes_credentials(url: Url) -> bool {
    url.username.len() > 0 || url.password.len() > 0
}

/// §4.2: "A URL has an opaque path if its path is a URL path segment."
pub open spec fn has_opaque_path(url: Url) -> bool {
    url.path is Opaque
}

/// §4.2: "A Windows drive letter is two code points, of which the first is
/// an ASCII alpha and the second is either U+003A (:) or U+007C (|)."
pub open spec fn is_windows_drive_letter(s: Seq<u32>) -> bool {
    s.len() == 2 && is_ascii_alpha(s[0]) && (s[1] == 0x3A || s[1] == 0x7C)
}

/// §4.2: "A normalized Windows drive letter is a Windows drive letter of
/// which the second code point is U+003A (:)."
pub open spec fn is_normalized_windows_drive_letter(s: Seq<u32>) -> bool {
    is_windows_drive_letter(s) && s[1] == 0x3A
}

/// §4.2: "A string starts with a Windows drive letter if all of the
/// following are true: its length is greater than or equal to 2; its
/// first two code points are a Windows drive letter; its length is 2 or
/// its third code point is U+002F (/), U+005C (\), U+003F (?), or U+0023
/// (#)."
pub open spec fn starts_with_windows_drive_letter(s: Seq<u32>) -> bool {
    s.len() >= 2 && is_windows_drive_letter(s.subrange(0, 2)) && (s.len() == 2 || s[2] == 0x2F
        || s[2] == 0x5C || s[2] == 0x3F || s[2] == 0x23)
}

/// §4.2: "To shorten a url's path".
/// (<https://url.spec.whatwg.org/#shorten-a-urls-path>)
pub open spec fn shorten(url: Url) -> Url {
    // 1. "Assert: url does not have an opaque path." (An opaque path is
    //    left as it is; the parser never shortens one, see the header.)
    // 2. "Let path be url's path."
    match url.path {
        UrlPath::Opaque(_) => url,
        UrlPath::List(path) => if url.scheme == file_str() && path.len() == 1
            && is_normalized_windows_drive_letter(path[0]) {
            // 3. "If url's scheme is "file", path's size is 1, and path[0]
            //    is a normalized Windows drive letter, then return."
            url
        } else if path.len() > 0 {
            // 4. "Remove path's last item, if any."
            Url { path: UrlPath::List(path.drop_last()), ..url }
        } else {
            url
        },
    }
}

/// "Append" `segment` to a path that is a list (see the header for the
/// opaque case, which the parser never reaches).
pub open spec fn path_append(path: UrlPath, segment: Seq<u32>) -> UrlPath {
    match path {
        UrlPath::List(l) => UrlPath::List(l.push(segment)),
        UrlPath::Opaque(s) => UrlPath::Opaque(s),
    }
}

/// Append `s` to an opaque path (see the header for the list case, which
/// the parser never reaches).
pub open spec fn opaque_path_append(path: UrlPath, s: Seq<u32>) -> UrlPath {
    match path {
        UrlPath::Opaque(o) => UrlPath::Opaque(o + s),
        UrlPath::List(l) => UrlPath::List(l),
    }
}

/// Append `s` to a query, which the parser has set to a string (see the
/// header).
pub open spec fn query_append(query: Option<Seq<u32>>, s: Seq<u32>) -> Option<Seq<u32>> {
    match query {
        Some(q) => Some(q + s),
        None => Some(s),
    }
}

/// Append `s` to a fragment, which the parser has set to a string (see
/// the header).
pub open spec fn fragment_append(fragment: Option<Seq<u32>>, s: Seq<u32>) -> Option<Seq<u32>> {
    match fragment {
        Some(f) => Some(f + s),
        None => Some(s),
    }
}

// ---------------------------------------------------------------------
// §4.4 The basic URL parser: its variables and states.
// ---------------------------------------------------------------------

/// The basic URL parser's states (§4.4 step 9), with the standard's names.
/// "host state" and "hostname state" share one definition; the hostname
/// state is only ever a state override.
pub enum State {
    /// "scheme start state"
    SchemeStart,
    /// "scheme state"
    Scheme,
    /// "no scheme state"
    NoScheme,
    /// "special relative or authority state"
    SpecialRelativeOrAuthority,
    /// "path or authority state"
    PathOrAuthority,
    /// "relative state"
    Relative,
    /// "relative slash state"
    RelativeSlash,
    /// "special authority slashes state"
    SpecialAuthoritySlashes,
    /// "special authority ignore slashes state"
    SpecialAuthorityIgnoreSlashes,
    /// "authority state"
    Authority,
    /// "host state"
    Host,
    /// "hostname state"
    Hostname,
    /// "port state"
    Port,
    /// "file state"
    File,
    /// "file slash state"
    FileSlash,
    /// "file host state"
    FileHost,
    /// "path start state"
    PathStart,
    /// "path state"
    Path,
    /// "opaque path state"
    OpaquePath,
    /// "query state"
    Query,
    /// "fragment state"
    Fragment,
}

/// The basic URL parser's inputs: input (after steps 1 to 3), base, state
/// override, and the domain parser the host parser runs (see the header).
pub struct Ctx {
    /// input, after leading and trailing C0 control or space and all ASCII
    /// tab or newline are removed.
    pub input: Seq<u32>,
    /// base (`None` is null).
    pub base: Option<Url>,
    /// state override (`None` is "not given").
    pub state_override: Option<State>,
    /// The URL §3.3 domain parser.
    pub domain_parser: crate::host::spec::DomainParser,
}

/// The basic URL parser's variables (§4.4 steps 4 to 8, and url).
pub struct Machine {
    /// url
    pub url: Url,
    /// state
    pub state: State,
    /// buffer
    pub buffer: Seq<u32>,
    /// atSignSeen
    pub at_sign_seen: bool,
    /// insideBrackets
    pub inside_brackets: bool,
    /// passwordTokenSeen
    pub password_token_seen: bool,
    /// pointer
    pub pointer: int,
}

/// What one run of a state does.
pub enum Step {
    /// "return failure"
    Failure,
    /// "return" (with a state override; the url as it is then).
    Return(Url),
    /// The run ended normally; the machine after it (before step 9's
    /// increase of pointer).
    Continue(Machine),
}

/// "remaining starts with" `x`: the code point after c is `x` (c is not
/// the EOF code point).
pub open spec fn remaining_starts_with(input: Seq<u32>, pointer: int, x: u32) -> bool {
    0 <= pointer && pointer + 1 < input.len() && input[pointer + 1] == x
}

/// base, which is non-null wherever this is used (see the header).
pub open spec fn base_of(ctx: Ctx) -> Url {
    match ctx.base {
        Some(b) => b,
        None => new_url(),
    }
}

/// c is `x`.
pub open spec fn c_is(ctx: Ctx, m: Machine, x: u32) -> bool {
    crate::host::spec::c_at(ctx.input, m.pointer) == Some(x)
}

/// c is the EOF code point.
pub open spec fn c_is_eof(ctx: Ctx, m: Machine) -> bool {
    crate::host::spec::c_at(ctx.input, m.pointer) is None
}

/// c, which is not the EOF code point here.
pub open spec fn c_of(ctx: Ctx, m: Machine) -> u32 {
    match crate::host::spec::c_at(ctx.input, m.pointer) {
        Some(c) => c,
        None => 0,
    }
}

/// "c is the EOF code point, U+002F (/), U+003F (?), or U+0023 (#)", or
/// "url is special and c is U+005C (\)": the end of an authority, host or
/// port (authority state step 2, host state step 3, port state step 2).
pub open spec fn ends_authority(ctx: Ctx, m: Machine) -> bool {
    c_is_eof(ctx, m) || c_is(ctx, m, 0x2F) || c_is(ctx, m, 0x3F) || c_is(ctx, m, 0x23) || (is_special(m.url)
        && c_is(ctx, m, 0x5C))
}

// ---------------------------------------------------------------------
// §4.4 states: scheme.
// ---------------------------------------------------------------------

/// "scheme start state" (<https://url.spec.whatwg.org/#scheme-start-state>)
pub open spec fn scheme_start_state(ctx: Ctx, m: Machine) -> Step {
    if !c_is_eof(ctx, m) && is_ascii_alpha(c_of(ctx, m)) {
        // 1. "If c is an ASCII alpha, append c, lowercased, to buffer, and
        //    set state to scheme state."
        Step::Continue(Machine { buffer: m.buffer.push(ascii_lowercase(c_of(ctx, m))), state: State::Scheme, ..m })
    } else if ctx.state_override is None {
        // 2. "Otherwise, if state override is not given, set state to no
        //    scheme state and decrease pointer by 1."
        Step::Continue(Machine { state: State::NoScheme, pointer: m.pointer - 1, ..m })
    } else {
        // 3. "Otherwise, return failure."
        Step::Failure
    }
}

/// "scheme state" (<https://url.spec.whatwg.org/#scheme-state>)
pub open spec fn scheme_state(ctx: Ctx, m: Machine) -> Step {
    if !c_is_eof(ctx, m) && (is_ascii_alphanumeric(c_of(ctx, m)) || c_is(ctx, m, 0x2B) || c_is(ctx, m, 0x2D)
        || c_is(ctx, m, 0x2E)) {
        // 1. "If c is an ASCII alphanumeric, U+002B (+), U+002D (-), or
        //    U+002E (.), append c, lowercased, to buffer."
        Step::Continue(Machine { buffer: m.buffer.push(ascii_lowercase(c_of(ctx, m))), ..m })
    } else if c_is(ctx, m, 0x3A) {
        // 2. "Otherwise, if c is U+003A (:), then:"
        scheme_state_colon(ctx, m)
    } else if ctx.state_override is None {
        // 3. "Otherwise, if state override is not given, set buffer to the
        //    empty string, state to no scheme state, and start over (from
        //    the first code point in input)." (See the header for the
        //    pointer.)
        Step::Continue(Machine { buffer: seq![], state: State::NoScheme, pointer: -1, ..m })
    } else {
        // 4. "Otherwise, return failure."
        Step::Failure
    }
}

/// Scheme state step 2, "if c is U+003A (:)".
pub open spec fn scheme_state_colon(ctx: Ctx, m: Machine) -> Step {
    let url = m.url;
    let buffer = m.buffer;
    // 2.1 "If state override is given, then:"
    if ctx.state_override is Some && is_special_scheme(url.scheme) && !is_special_scheme(buffer) {
        // 2.1.1 "If url's scheme is a special scheme and buffer is not a
        //       special scheme, then return."
        Step::Return(url)
    } else if ctx.state_override is Some && !is_special_scheme(url.scheme) && is_special_scheme(buffer) {
        // 2.1.2 "If url's scheme is not a special scheme and buffer is a
        //       special scheme, then return."
        Step::Return(url)
    } else if ctx.state_override is Some && (includes_credentials(url) || url.port is Some) && buffer
        == file_str() {
        // 2.1.3 "If url includes credentials or has a non-null port, and
        //       buffer is "file", then return."
        Step::Return(url)
    } else if ctx.state_override is Some && url.scheme == file_str() && url.host == Some(crate::host::spec::Host::Empty) {
        // 2.1.4 "If url's scheme is "file" and its host is an empty host,
        //       then return."
        Step::Return(url)
    } else {
        // 2.2 "Set url's scheme to buffer."
        let url = Url { scheme: buffer, ..url };
        if ctx.state_override is Some {
            // 2.3 "If state override is given, then:"
            // 2.3.1 "If url's port is url's scheme's default port, then set
            //       url's port to null."
            let url = if url.port == default_port(url.scheme) {
                Url { port: None, ..url }
            } else {
                url
            };
            // 2.3.2 "Return."
            Step::Return(url)
        } else {
            // 2.4 "Set buffer to the empty string."
            let m = Machine { url: url, buffer: seq![], ..m };
            if url.scheme == file_str() {
                // 2.5 "If url's scheme is "file", then:"
                // 2.5.1 "If remaining does not start with "//",
                //       special-scheme-missing-following-solidus validation
                //       error." (validation error only)
                // 2.5.2 "Set state to file state."
                Step::Continue(Machine { state: State::File, ..m })
            } else if is_special(url) && (ctx.base matches Some(base) && base.scheme == url.scheme) {
                // 2.6 "Otherwise, if url is special, base is non-null, and
                //     base's scheme is url's scheme:"
                // 2.6.1 "Assert: base is special (and therefore does not
                //       have an opaque path)." (it has url's scheme)
                // 2.6.2 "Set state to special relative or authority state."
                Step::Continue(Machine { state: State::SpecialRelativeOrAuthority, ..m })
            } else if is_special(url) {
                // 2.7 "Otherwise, if url is special, set state to special
                //     authority slashes state."
                Step::Continue(Machine { state: State::SpecialAuthoritySlashes, ..m })
            } else if remaining_starts_with(ctx.input, m.pointer, 0x2F) {
                // 2.8 "Otherwise, if remaining starts with an U+002F (/), set
                //     state to path or authority state and increase pointer
                //     by 1."
                Step::Continue(Machine { state: State::PathOrAuthority, pointer: m.pointer + 1, ..m })
            } else {
                // 2.9 "Otherwise, set url's path to the empty string and set
                //     state to opaque path state."
                Step::Continue(
                    Machine { url: Url { path: UrlPath::Opaque(seq![]), ..url }, state: State::OpaquePath, ..m },
                )
            }
        }
    }
}

/// "no scheme state" (<https://url.spec.whatwg.org/#no-scheme-state>)
pub open spec fn no_scheme_state(ctx: Ctx, m: Machine) -> Step {
    let base = base_of(ctx);
    if ctx.base is None || (has_opaque_path(base) && !c_is(ctx, m, 0x23)) {
        // 1. "If base is null, or base has an opaque path and c is not U+0023
        //    (#), missing-scheme-non-relative-URL validation error, return
        //    failure."
        Step::Failure
    } else if has_opaque_path(base) && c_is(ctx, m, 0x23) {
        // 2. "Otherwise, if base has an opaque path and c is U+0023 (#), set
        //    url's scheme to base's scheme, url's path to base's path, url's
        //    query to base's query, url's fragment to the empty string, and
        //    set state to fragment state."
        Step::Continue(
            Machine {
                url: Url {
                    scheme: base.scheme,
                    path: base.path,
                    query: base.query,
                    fragment: Some(seq![]),
                    ..m.url
                },
                state: State::Fragment,
                ..m
            },
        )
    } else if base.scheme != file_str() {
        // 3. "Otherwise, if base's scheme is not "file", set state to
        //    relative state and decrease pointer by 1."
        Step::Continue(Machine { state: State::Relative, pointer: m.pointer - 1, ..m })
    } else {
        // 4. "Otherwise, set state to file state and decrease pointer by 1."
        Step::Continue(Machine { state: State::File, pointer: m.pointer - 1, ..m })
    }
}

// ---------------------------------------------------------------------
// §4.4 states: authority (and the relative and file states that lead to
// one).
// ---------------------------------------------------------------------

/// "special relative or authority state"
/// (<https://url.spec.whatwg.org/#special-relative-or-authority-state>)
pub open spec fn special_relative_or_authority_state(ctx: Ctx, m: Machine) -> Step {
    if c_is(ctx, m, 0x2F) && remaining_starts_with(ctx.input, m.pointer, 0x2F) {
        // 1. "If c is U+002F (/) and remaining starts with U+002F (/), then
        //    set state to special authority ignore slashes state and
        //    increase pointer by 1."
        Step::Continue(Machine { state: State::SpecialAuthorityIgnoreSlashes, pointer: m.pointer + 1, ..m })
    } else {
        // 2. "Otherwise, special-scheme-missing-following-solidus validation
        //    error, set state to relative state and decrease pointer by 1."
        Step::Continue(Machine { state: State::Relative, pointer: m.pointer - 1, ..m })
    }
}

/// "path or authority state"
/// (<https://url.spec.whatwg.org/#path-or-authority-state>)
pub open spec fn path_or_authority_state(ctx: Ctx, m: Machine) -> Step {
    if c_is(ctx, m, 0x2F) {
        // 1. "If c is U+002F (/), then set state to authority state."
        Step::Continue(Machine { state: State::Authority, ..m })
    } else {
        // 2. "Otherwise, set state to path state, and decrease pointer by 1."
        Step::Continue(Machine { state: State::Path, pointer: m.pointer - 1, ..m })
    }
}

/// "relative state" (<https://url.spec.whatwg.org/#relative-state>)
pub open spec fn relative_state(ctx: Ctx, m: Machine) -> Step {
    let base = base_of(ctx);
    // 1. "Assert: base's scheme is not "file"." (no scheme state step 3
    //    and scheme state step 2.6 only come here when it is not)
    // 2. "Set url's scheme to base's scheme."
    let url = Url { scheme: base.scheme, ..m.url };
    if c_is(ctx, m, 0x2F) {
        // 3. "If c is U+002F (/), then set state to relative slash state."
        Step::Continue(Machine { url: url, state: State::RelativeSlash, ..m })
    } else if is_special(url) && c_is(ctx, m, 0x5C) {
        // 4. "Otherwise, if url is special and c is U+005C (\),
        //    invalid-reverse-solidus validation error, set state to relative
        //    slash state."
        Step::Continue(Machine { url: url, state: State::RelativeSlash, ..m })
    } else {
        // 5. "Otherwise:"
        // 5.1 "Set url's username to base's username, url's password to
        //     base's password, url's host to base's host, url's port to
        //     base's port, url's path to a clone of base's path, and url's
        //     query to base's query."
        let url = Url {
            username: base.username,
            password: base.password,
            host: base.host,
            port: base.port,
            path: base.path,
            query: base.query,
            ..url
        };
        if c_is(ctx, m, 0x3F) {
            // 5.2 "If c is U+003F (?), then set url's query to the empty
            //     string, and state to query state."
            Step::Continue(Machine { url: Url { query: Some(seq![]), ..url }, state: State::Query, ..m })
        } else if c_is(ctx, m, 0x23) {
            // 5.3 "Otherwise, if c is U+0023 (#), set url's fragment to the
            //     empty string and state to fragment state."
            Step::Continue(Machine { url: Url { fragment: Some(seq![]), ..url }, state: State::Fragment, ..m })
        } else if !c_is_eof(ctx, m) {
            // 5.4 "Otherwise, if c is not the EOF code point:"
            // 5.4.1 "Set url's query to null."
            let url = Url { query: None, ..url };
            // 5.4.2 "Shorten url's path."
            let url = shorten(url);
            // 5.4.3 "Set state to path state and decrease pointer by 1."
            Step::Continue(Machine { url: url, state: State::Path, pointer: m.pointer - 1, ..m })
        } else {
            Step::Continue(Machine { url: url, ..m })
        }
    }
}

/// "relative slash state" (<https://url.spec.whatwg.org/#relative-slash-state>)
pub open spec fn relative_slash_state(ctx: Ctx, m: Machine) -> Step {
    let base = base_of(ctx);
    if is_special(m.url) && (c_is(ctx, m, 0x2F) || c_is(ctx, m, 0x5C)) {
        // 1. "If url is special and c is U+002F (/) or U+005C (\), then:"
        // 1.1 "If c is U+005C (\), invalid-reverse-solidus validation
        //     error." (validation error only)
        // 1.2 "Set state to special authority ignore slashes state."
        Step::Continue(Machine { state: State::SpecialAuthorityIgnoreSlashes, ..m })
    } else if c_is(ctx, m, 0x2F) {
        // 2. "Otherwise, if c is U+002F (/), then set state to authority
        //    state."
        Step::Continue(Machine { state: State::Authority, ..m })
    } else {
        // 3. "Otherwise, set url's username to base's username, url's
        //    password to base's password, url's host to base's host, url's
        //    port to base's port, state to path state, and then, decrease
        //    pointer by 1."
        Step::Continue(
            Machine {
                url: Url {
                    username: base.username,
                    password: base.password,
                    host: base.host,
                    port: base.port,
                    ..m.url
                },
                state: State::Path,
                pointer: m.pointer - 1,
                ..m
            },
        )
    }
}

/// "special authority slashes state"
/// (<https://url.spec.whatwg.org/#special-authority-slashes-state>)
pub open spec fn special_authority_slashes_state(ctx: Ctx, m: Machine) -> Step {
    if c_is(ctx, m, 0x2F) && remaining_starts_with(ctx.input, m.pointer, 0x2F) {
        // 1. "If c is U+002F (/) and remaining starts with U+002F (/), then
        //    set state to special authority ignore slashes state and
        //    increase pointer by 1."
        Step::Continue(Machine { state: State::SpecialAuthorityIgnoreSlashes, pointer: m.pointer + 1, ..m })
    } else {
        // 2. "Otherwise, special-scheme-missing-following-solidus validation
        //    error, set state to special authority ignore slashes state and
        //    decrease pointer by 1."
        Step::Continue(Machine { state: State::SpecialAuthorityIgnoreSlashes, pointer: m.pointer - 1, ..m })
    }
}

/// "special authority ignore slashes state"
/// (<https://url.spec.whatwg.org/#special-authority-ignore-slashes-state>)
pub open spec fn special_authority_ignore_slashes_state(ctx: Ctx, m: Machine) -> Step {
    if !c_is(ctx, m, 0x2F) && !c_is(ctx, m, 0x5C) {
        // 1. "If c is neither U+002F (/) nor U+005C (\), then set state to
        //    authority state and decrease pointer by 1."
        Step::Continue(Machine { state: State::Authority, pointer: m.pointer - 1, ..m })
    } else {
        // 2. "Otherwise, special-scheme-missing-following-solidus validation
        //    error." (validation error only)
        Step::Continue(m)
    }
}

/// Authority state step 1.4, "For each codePoint in buffer", from index
/// `i`, with url and passwordTokenSeen so far.
pub open spec fn authority_code_points(buffer: Seq<u32>, i: nat, url: Url, password_token_seen: bool) -> (Url, bool)
    decreases buffer.len() - i
{
    if i >= buffer.len() {
        (url, password_token_seen)
    } else {
        let code_point = buffer[i as int];
        if code_point == 0x3A && !password_token_seen {
            // 1.4.1 "If codePoint is U+003A (:) and passwordTokenSeen is
            //       false, then set passwordTokenSeen to true and continue."
            authority_code_points(buffer, i + 1, url, true)
        } else {
            // 1.4.2 "Let encodedCodePoints be the result of running UTF-8
            //       percent-encode codePoint using the userinfo
            //       percent-encode set."
            let encoded_code_points = clazel_percent::spec::utf8_percent_encode_code_point(
                code_point,
                clazel_percent::spec::PercentEncodeSet::Userinfo,
            );
            if password_token_seen {
                // 1.4.3 "If passwordTokenSeen is true, then append
                //       encodedCodePoints to url's password."
                authority_code_points(buffer, i + 1, Url { password: url.password + encoded_code_points, ..url }, password_token_seen)
            } else {
                // 1.4.4 "Otherwise, append encodedCodePoints to url's
                //       username."
                authority_code_points(buffer, i + 1, Url { username: url.username + encoded_code_points, ..url }, password_token_seen)
            }
        }
    }
}

/// "authority state" (<https://url.spec.whatwg.org/#authority-state>)
pub open spec fn authority_state(ctx: Ctx, m: Machine) -> Step {
    if c_is(ctx, m, 0x40) {
        // 1. "If c is U+0040 (@), then:"
        // 1.1 "Invalid-credentials validation error." (validation error
        //     only)
        // 1.2 "If atSignSeen is true, then prepend "%40" to buffer."
        let buffer = if m.at_sign_seen {
            seq![0x25u32, 0x34, 0x30] + m.buffer
        } else {
            m.buffer
        };
        // 1.3 "Set atSignSeen to true."
        // 1.4 "For each codePoint in buffer:"
        let (url, password_token_seen) = authority_code_points(buffer, 0, m.url, m.password_token_seen);
        // 1.5 "Set buffer to the empty string."
        Step::Continue(
            Machine { url: url, buffer: seq![], at_sign_seen: true, password_token_seen: password_token_seen, ..m },
        )
    } else if ends_authority(ctx, m) {
        // 2. "Otherwise, if one of the following is true: c is the EOF code
        //    point, U+002F (/), U+003F (?), or U+0023 (#); url is special
        //    and c is U+005C (\); then:"
        if m.at_sign_seen && m.buffer.len() == 0 {
            // 2.1 "If atSignSeen is true and buffer is the empty string,
            //     host-missing validation error, return failure."
            Step::Failure
        } else {
            // 2.2 "Decrease pointer by buffer's code point length + 1, set
            //     buffer to the empty string, and set state to host state."
            Step::Continue(
                Machine { buffer: seq![], state: State::Host, pointer: m.pointer - (m.buffer.len() + 1), ..m },
            )
        }
    } else {
        // 3. "Otherwise, append c to buffer."
        Step::Continue(Machine { buffer: m.buffer.push(c_of(ctx, m)), ..m })
    }
}

/// "host state" and "hostname state"
/// (<https://url.spec.whatwg.org/#host-state>)
pub open spec fn host_state(ctx: Ctx, m: Machine) -> Step {
    let url = m.url;
    if ctx.state_override is Some && url.scheme == file_str() {
        // 1. "If state override is given and url's scheme is "file", then
        //    decrease pointer by 1 and set state to file host state."
        Step::Continue(Machine { state: State::FileHost, pointer: m.pointer - 1, ..m })
    } else if c_is(ctx, m, 0x3A) && !m.inside_brackets {
        // 2. "Otherwise, if c is U+003A (:) and insideBrackets is false:"
        if m.buffer.len() == 0 {
            // 2.1 "If buffer is the empty string, host-missing validation
            //     error, return failure."
            Step::Failure
        } else if ctx.state_override == Some(State::Hostname) {
            // 2.2 "If state override is given and state override is hostname
            //     state, then return failure."
            Step::Failure
        } else {
            // 2.3 "Let host be the result of host parsing buffer with url is
            //     not special."
            match crate::host::spec::host_parser(m.buffer, !is_special(url), ctx.domain_parser) {
                // 2.4 "If host is failure, then return failure."
                None => Step::Failure,
                // 2.5 "Set url's host to host, buffer to the empty string, and
                //     state to port state."
                Some(host) => Step::Continue(
                    Machine { url: Url { host: Some(host), ..url }, buffer: seq![], state: State::Port, ..m },
                ),
            }
        }
    } else if ends_authority(ctx, m) {
        // 3. "Otherwise, if one of the following is true: c is the EOF code
        //    point, U+002F (/), U+003F (?), or U+0023 (#); url is special
        //    and c is U+005C (\); then decrease pointer by 1, and:"
        let pointer = m.pointer - 1;
        if is_special(url) && m.buffer.len() == 0 {
            // 3.1 "If url is special and buffer is the empty string,
            //     host-missing validation error, return failure."
            Step::Failure
        } else if ctx.state_override is Some && m.buffer.len() == 0 && (includes_credentials(url)
            || url.port is Some) {
            // 3.2 "Otherwise, if state override is given, buffer is the empty
            //     string, and either url includes credentials or url's port
            //     is non-null, then return failure."
            Step::Failure
        } else {
            // 3.3 "Let host be the result of host parsing buffer with url is
            //     not special."
            match crate::host::spec::host_parser(m.buffer, !is_special(url), ctx.domain_parser) {
                // 3.4 "If host is failure, then return failure."
                None => Step::Failure,
                Some(host) => {
                    // 3.5 "Set url's host to host, buffer to the empty
                    //     string, and state to path start state."
                    let url = Url { host: Some(host), ..url };
                    if ctx.state_override is Some {
                        // 3.6 "If state override is given, then return."
                        Step::Return(url)
                    } else {
                        Step::Continue(
                            Machine { url: url, buffer: seq![], state: State::PathStart, pointer: pointer, ..m },
                        )
                    }
                },
            }
        }
    } else {
        // 4. "Otherwise:"
        // 4.1 "If c is U+005B ([), then set insideBrackets to true."
        // 4.2 "If c is U+005D (]), then set insideBrackets to false."
        let inside_brackets = if c_is(ctx, m, 0x5B) {
            true
        } else if c_is(ctx, m, 0x5D) {
            false
        } else {
            m.inside_brackets
        };
        // 4.3 "Append c to buffer."
        Step::Continue(Machine { buffer: m.buffer.push(c_of(ctx, m)), inside_brackets: inside_brackets, ..m })
    }
}

/// "The mathematical integer value that is represented by buffer in
/// radix-10 using ASCII digits for digits with values 0 through 9" (port
/// state step 2.1.1), most significant digit first.
pub open spec fn decimal_value(s: Seq<u32>) -> nat
    decreases s.len()
{
    if s.len() == 0 {
        0
    } else {
        decimal_value(s.drop_last()) * 10 + (s.last() - 0x30) as nat
    }
}

/// "port state" (<https://url.spec.whatwg.org/#port-state>)
pub open spec fn port_state(ctx: Ctx, m: Machine) -> Step {
    if !c_is_eof(ctx, m) && crate::host::spec::is_ascii_digit(c_of(ctx, m)) {
        // 1. "If c is an ASCII digit, append c to buffer."
        Step::Continue(Machine { buffer: m.buffer.push(c_of(ctx, m)), ..m })
    } else if ends_authority(ctx, m) || ctx.state_override is Some {
        // 2. "Otherwise, if one of the following is true: c is the EOF code
        //    point, U+002F (/), U+003F (?), or U+0023 (#); url is special
        //    and c is U+005C (\); or state override is given, then:"
        if m.buffer.len() > 0 {
            // 2.1 "If buffer is not the empty string:"
            // 2.1.1 "Let port be the mathematical integer value that is
            //       represented by buffer in radix-10 using ASCII digits for
            //       digits with values 0 through 9."
            let port = decimal_value(m.buffer);
            if port > 0xFFFF {
                // 2.1.2 "If port is not a 16-bit unsigned integer,
                //       port-out-of-range validation error, return failure."
                Step::Failure
            } else {
                // 2.1.3 "Set url's port to null, if port is url's scheme's
                //       default port; otherwise to port."
                let url = if default_port(m.url.scheme) == Some(port) {
                    Url { port: None, ..m.url }
                } else {
                    Url { port: Some(port), ..m.url }
                };
                // 2.1.4 "Set buffer to the empty string."
                if ctx.state_override is Some {
                    // 2.1.5 "If state override is given, then return."
                    Step::Return(url)
                } else {
                    // 2.3 "Set state to path start state and decrease pointer
                    //     by 1."
                    Step::Continue(
                        Machine { url: url, buffer: seq![], state: State::PathStart, pointer: m.pointer - 1, ..m },
                    )
                }
            }
        } else if ctx.state_override is Some {
            // 2.2 "If state override is given, then return failure."
            Step::Failure
        } else {
            // 2.3 "Set state to path start state and decrease pointer by 1."
            Step::Continue(Machine { state: State::PathStart, pointer: m.pointer - 1, ..m })
        }
    } else {
        // 3. "Otherwise, port-invalid validation error, return failure."
        Step::Failure
    }
}

/// "The code point substring from pointer to the end of input".
pub open spec fn substring_from_pointer(ctx: Ctx, m: Machine) -> Seq<u32> {
    if 0 <= m.pointer <= ctx.input.len() {
        ctx.input.subrange(m.pointer, ctx.input.len() as int)
    } else {
        seq![]
    }
}

/// "file state" (<https://url.spec.whatwg.org/#file-state>)
pub open spec fn file_state(ctx: Ctx, m: Machine) -> Step {
    // 1. "Set url's scheme to "file"."
    // 2. "Set url's host to the empty string."
    let url = Url { scheme: file_str(), host: Some(crate::host::spec::Host::Empty), ..m.url };
    if c_is(ctx, m, 0x2F) || c_is(ctx, m, 0x5C) {
        // 3. "If c is U+002F (/) or U+005C (\), then:"
        // 3.1 "If c is U+005C (\), invalid-reverse-solidus validation
        //     error." (validation error only)
        // 3.2 "Set state to file slash state."
        Step::Continue(Machine { url: url, state: State::FileSlash, ..m })
    } else if ctx.base matches Some(base) && base.scheme == file_str() {
        // 4. "Otherwise, if base is non-null and base's scheme is "file":"
        let base = base_of(ctx);
        // 4.1 "Set url's host to base's host, url's path to a clone of
        //     base's path, and url's query to base's query."
        let url = Url { host: base.host, path: base.path, query: base.query, ..url };
        if c_is(ctx, m, 0x3F) {
            // 4.2 "If c is U+003F (?), then set url's query to the empty
            //     string and state to query state."
            Step::Continue(Machine { url: Url { query: Some(seq![]), ..url }, state: State::Query, ..m })
        } else if c_is(ctx, m, 0x23) {
            // 4.3 "Otherwise, if c is U+0023 (#), set url's fragment to the
            //     empty string and state to fragment state."
            Step::Continue(Machine { url: Url { fragment: Some(seq![]), ..url }, state: State::Fragment, ..m })
        } else if !c_is_eof(ctx, m) {
            // 4.4 "Otherwise, if c is not the EOF code point:"
            // 4.4.1 "Set url's query to null."
            let url = Url { query: None, ..url };
            let url = if !starts_with_windows_drive_letter(substring_from_pointer(ctx, m)) {
                // 4.4.2 "If the code point substring from pointer to the end
                //       of input does not start with a Windows drive letter,
                //       then shorten url's path."
                shorten(url)
            } else {
                // 4.4.3 "Otherwise:"
                // 4.4.3.1 "File-invalid-Windows-drive-letter validation
                //         error." (validation error only)
                // 4.4.3.2 "Set url's path to « »."
                Url { path: UrlPath::List(seq![]), ..url }
            };
            // 4.4.4 "Set state to path state and decrease pointer by 1."
            Step::Continue(Machine { url: url, state: State::Path, pointer: m.pointer - 1, ..m })
        } else {
            Step::Continue(Machine { url: url, ..m })
        }
    } else {
        // 5. "Otherwise, set state to path state, and decrease pointer by 1."
        Step::Continue(Machine { url: url, state: State::Path, pointer: m.pointer - 1, ..m })
    }
}

/// "file slash state" (<https://url.spec.whatwg.org/#file-slash-state>)
pub open spec fn file_slash_state(ctx: Ctx, m: Machine) -> Step {
    if c_is(ctx, m, 0x2F) || c_is(ctx, m, 0x5C) {
        // 1. "If c is U+002F (/) or U+005C (\), then:"
        // 1.1 "If c is U+005C (\), invalid-reverse-solidus validation
        //     error." (validation error only)
        // 1.2 "Set state to file host state."
        Step::Continue(Machine { state: State::FileHost, ..m })
    } else {
        // 2. "Otherwise:"
        let url = if ctx.base matches Some(base) && base.scheme == file_str() {
            // 2.1 "If base is non-null and base's scheme is "file", then:"
            let base = base_of(ctx);
            // 2.1.1 "Set url's host to base's host."
            let url = Url { host: base.host, ..m.url };
            // 2.1.2 "If the code point substring from pointer to the end of
            //       input does not start with a Windows drive letter and
            //       base's path[0] is a normalized Windows drive letter, then
            //       append base's path[0] to url's path."
            if !starts_with_windows_drive_letter(substring_from_pointer(ctx, m)) && (base.path matches UrlPath::List(
                p,
            ) && p.len() > 0 && is_normalized_windows_drive_letter(p[0])) {
                let p0 = match base.path {
                    UrlPath::List(p) => p[0],
                    UrlPath::Opaque(_) => seq![],
                };
                Url { path: path_append(url.path, p0), ..url }
            } else {
                url
            }
        } else {
            m.url
        };
        // 2.2 "Set state to path state, and decrease pointer by 1."
        Step::Continue(Machine { url: url, state: State::Path, pointer: m.pointer - 1, ..m })
    }
}

/// "file host state" (<https://url.spec.whatwg.org/#file-host-state>)
pub open spec fn file_host_state(ctx: Ctx, m: Machine) -> Step {
    if c_is_eof(ctx, m) || c_is(ctx, m, 0x2F) || c_is(ctx, m, 0x5C) || c_is(ctx, m, 0x3F) || c_is(ctx, m, 0x23) {
        // 1. "If c is the EOF code point, U+002F (/), U+005C (\), U+003F (?),
        //    or U+0023 (#), then decrease pointer by 1 and then:"
        let pointer = m.pointer - 1;
        if ctx.state_override is None && is_windows_drive_letter(m.buffer) {
            // 1.1 "If state override is not given and buffer is a Windows
            //     drive letter, file-invalid-Windows-drive-letter-host
            //     validation error, set state to path state." (buffer is
            //     kept, for the path state)
            Step::Continue(Machine { state: State::Path, pointer: pointer, ..m })
        } else if m.buffer.len() == 0 {
            // 1.2 "Otherwise, if buffer is the empty string, then:"
            // 1.2.1 "Set url's host to the empty string."
            let url = Url { host: Some(crate::host::spec::Host::Empty), ..m.url };
            if ctx.state_override is Some {
                // 1.2.2 "If state override is given, then return."
                Step::Return(url)
            } else {
                // 1.2.3 "Set state to path start state."
                Step::Continue(Machine { url: url, state: State::PathStart, pointer: pointer, ..m })
            }
        } else {
            // 1.3 "Otherwise, run these steps:"
            // 1.3.1 "Let host be the result of host parsing buffer with url
            //       is not special."
            match crate::host::spec::host_parser(m.buffer, !is_special(m.url), ctx.domain_parser) {
                // 1.3.2 "If host is failure, then return failure."
                None => Step::Failure,
                Some(host) => {
                    // 1.3.3 "If host is "localhost", then set host to the
                    //       empty string."
                    let host = if host == crate::host::spec::Host::Domain(localhost_str()) {
                        crate::host::spec::Host::Empty
                    } else {
                        host
                    };
                    // 1.3.4 "Set url's host to host."
                    let url = Url { host: Some(host), ..m.url };
                    if ctx.state_override is Some {
                        // 1.3.5 "If state override is given, then return."
                        Step::Return(url)
                    } else {
                        // 1.3.6 "Set buffer to the empty string and state to
                        //       path start state."
                        Step::Continue(
                            Machine { url: url, buffer: seq![], state: State::PathStart, pointer: pointer, ..m },
                        )
                    }
                },
            }
        }
    } else {
        // 2. "Otherwise, append c to buffer."
        Step::Continue(Machine { buffer: m.buffer.push(c_of(ctx, m)), ..m })
    }
}

// ---------------------------------------------------------------------
// §4.4 states: path.
// ---------------------------------------------------------------------

/// "path start state" (<https://url.spec.whatwg.org/#path-start-state>)
pub open spec fn path_start_state(ctx: Ctx, m: Machine) -> Step {
    if is_special(m.url) {
        // 1. "If url is special, then:"
        // 1.1 "If c is U+005C (\), invalid-reverse-solidus validation
        //     error." (validation error only)
        // 1.2 "Set state to path state."
        if !c_is(ctx, m, 0x2F) && !c_is(ctx, m, 0x5C) {
            // 1.3 "If c is neither U+002F (/) nor U+005C (\), then decrease
            //     pointer by 1."
            Step::Continue(Machine { state: State::Path, pointer: m.pointer - 1, ..m })
        } else {
            Step::Continue(Machine { state: State::Path, ..m })
        }
    } else if ctx.state_override is None && c_is(ctx, m, 0x3F) {
        // 2. "Otherwise, if state override is not given and c is U+003F (?),
        //    set url's query to the empty string and state to query state."
        Step::Continue(Machine { url: Url { query: Some(seq![]), ..m.url }, state: State::Query, ..m })
    } else if ctx.state_override is None && c_is(ctx, m, 0x23) {
        // 3. "Otherwise, if state override is not given and c is U+0023 (#),
        //    set url's fragment to the empty string and state to fragment
        //    state."
        Step::Continue(Machine { url: Url { fragment: Some(seq![]), ..m.url }, state: State::Fragment, ..m })
    } else if !c_is_eof(ctx, m) {
        // 4. "Otherwise, if c is not the EOF code point:"
        // 4.1 "Set state to path state."
        if !c_is(ctx, m, 0x2F) {
            // 4.2 "If c is not U+002F (/), then decrease pointer by 1."
            Step::Continue(Machine { state: State::Path, pointer: m.pointer - 1, ..m })
        } else {
            Step::Continue(Machine { state: State::Path, ..m })
        }
    } else if ctx.state_override is Some && m.url.host is None {
        // 5. "Otherwise, if state override is given and url's host is null,
        //    append the empty string to url's path."
        Step::Continue(Machine { url: Url { path: path_append(m.url.path, seq![]), ..m.url }, ..m })
    } else {
        Step::Continue(m)
    }
}

/// Path state step 1's condition: "c is the EOF code point or U+002F (/)";
/// "url is special and c is U+005C (\)"; "state override is not given and
/// c is U+003F (?) or U+0023 (#)".
pub open spec fn ends_path_segment(ctx: Ctx, m: Machine) -> bool {
    c_is_eof(ctx, m) || c_is(ctx, m, 0x2F) || (is_special(m.url) && c_is(ctx, m, 0x5C)) || (ctx.state_override is None
        && (c_is(ctx, m, 0x3F) || c_is(ctx, m, 0x23)))
}

/// "c is U+002F (/)", or "url is special and c is U+005C (\)" (path state
/// steps 1.2.2 and 1.3).
pub open spec fn c_is_path_slash(ctx: Ctx, m: Machine) -> bool {
    c_is(ctx, m, 0x2F) || (is_special(m.url) && c_is(ctx, m, 0x5C))
}

/// "path state" (<https://url.spec.whatwg.org/#path-state>)
pub open spec fn path_state(ctx: Ctx, m: Machine) -> Step {
    if ends_path_segment(ctx, m) {
        // 1. "If one of the following is true: [...] then:"
        // 1.1 "If url is special and c is U+005C (\), invalid-reverse-solidus
        //     validation error." (validation error only)
        let url = if is_double_dot_segment(m.buffer) {
            // 1.2 "If buffer is a double-dot URL path segment, then:"
            // 1.2.1 "Shorten url's path."
            let url = shorten(m.url);
            if !c_is_path_slash(ctx, m) {
                // 1.2.2 "If neither c is U+002F (/), nor url is special and c
                //       is U+005C (\), append the empty string to url's
                //       path."
                Url { path: path_append(url.path, seq![]), ..url }
            } else {
                url
            }
        } else if is_single_dot_segment(m.buffer) && !c_is_path_slash(ctx, m) {
            // 1.3 "Otherwise, if buffer is a single-dot URL path segment and
            //     if neither c is U+002F (/), nor url is special and c is
            //     U+005C (\), append the empty string to url's path."
            Url { path: path_append(m.url.path, seq![]), ..m.url }
        } else if !is_single_dot_segment(m.buffer) {
            // 1.4 "Otherwise, if buffer is not a single-dot URL path segment,
            //     then:"
            // 1.4.1 "If url's scheme is "file", url's path is empty, and
            //       buffer is a Windows drive letter, then replace the second
            //       code point in buffer with U+003A (:)."
            let buffer = if m.url.scheme == file_str() && m.url.path == UrlPath::List(seq![])
                && is_windows_drive_letter(m.buffer) {
                m.buffer.update(1, 0x3A)
            } else {
                m.buffer
            };
            // 1.4.2 "Append buffer to url's path."
            Url { path: path_append(m.url.path, buffer), ..m.url }
        } else {
            m.url
        };
        // 1.5 "Set buffer to the empty string."
        let m = Machine { url: url, buffer: seq![], ..m };
        if c_is(ctx, m, 0x3F) {
            // 1.6 "If c is U+003F (?), then set url's query to the empty
            //     string and state to query state."
            Step::Continue(Machine { url: Url { query: Some(seq![]), ..url }, state: State::Query, ..m })
        } else if c_is(ctx, m, 0x23) {
            // 1.7 "If c is U+0023 (#), then set url's fragment to the empty
            //     string and state to fragment state."
            Step::Continue(Machine { url: Url { fragment: Some(seq![]), ..url }, state: State::Fragment, ..m })
        } else {
            Step::Continue(m)
        }
    } else {
        // 2. "Otherwise, run these steps:"
        // 2.1 "If c is not a URL code point and not U+0025 (%),
        //     invalid-URL-unit validation error." (validation error only)
        // 2.2 "If c is U+0025 (%) and remaining does not start with two
        //     ASCII hex digits, invalid-URL-unit validation error."
        //     (validation error only)
        // 2.3 "UTF-8 percent-encode c using the path percent-encode set and
        //     append the result to buffer."
        Step::Continue(
            Machine {
                buffer: m.buffer + clazel_percent::spec::utf8_percent_encode_code_point(
                    c_of(ctx, m),
                    clazel_percent::spec::PercentEncodeSet::Path,
                ),
                ..m
            },
        )
    }
}

/// "opaque path state"
/// (<https://url.spec.whatwg.org/#cannot-be-a-base-url-path-state>)
pub open spec fn opaque_path_state(ctx: Ctx, m: Machine) -> Step {
    if c_is(ctx, m, 0x3F) {
        // 1. "If c is U+003F (?), then set url's query to the empty string
        //    and state to query state."
        Step::Continue(Machine { url: Url { query: Some(seq![]), ..m.url }, state: State::Query, ..m })
    } else if c_is(ctx, m, 0x23) {
        // 2. "Otherwise, if c is U+0023 (#), then set url's fragment to the
        //    empty string and state to fragment state."
        Step::Continue(Machine { url: Url { fragment: Some(seq![]), ..m.url }, state: State::Fragment, ..m })
    } else if c_is(ctx, m, 0x20) {
        // 3. "Otherwise, if c is U+0020 SPACE:"
        // 3.1 "Invalid-URL-unit validation error." (validation error only)
        if remaining_starts_with(ctx.input, m.pointer, 0x3F) || remaining_starts_with(ctx.input, m.pointer, 0x23) {
            // 3.2 "If remaining starts with U+003F (?) or U+0023 (#), then
            //     append "%20" to url's path."
            Step::Continue(
                Machine { url: Url { path: opaque_path_append(m.url.path, seq![0x25u32, 0x32, 0x30]), ..m.url }, ..m },
            )
        } else {
            // 3.3 "Otherwise, append U+0020 SPACE to url's path."
            Step::Continue(Machine { url: Url { path: opaque_path_append(m.url.path, seq![0x20u32]), ..m.url }, ..m })
        }
    } else if !c_is_eof(ctx, m) {
        // 4. "Otherwise, if c is not the EOF code point:"
        // 4.1 "If c is not a URL code point and not U+0025 (%),
        //     invalid-URL-unit validation error." (validation error only)
        // 4.2 "If c is U+0025 (%) and remaining does not start with two
        //     ASCII hex digits, invalid-URL-unit validation error."
        //     (validation error only)
        // 4.3 "UTF-8 percent-encode c using the C0 control percent-encode set
        //     and append the result to url's path."
        Step::Continue(
            Machine {
                url: Url {
                    path: opaque_path_append(
                        m.url.path,
                        clazel_percent::spec::utf8_percent_encode_code_point(
                            c_of(ctx, m),
                            clazel_percent::spec::PercentEncodeSet::C0Control,
                        ),
                    ),
                    ..m.url
                },
                ..m
            },
        )
    } else {
        Step::Continue(m)
    }
}

// ---------------------------------------------------------------------
// §4.4 states: query and fragment.
// ---------------------------------------------------------------------

/// "query state" (<https://url.spec.whatwg.org/#query-state>)
pub open spec fn query_state(ctx: Ctx, m: Machine) -> Step {
    // 1. "If encoding is not UTF-8 and one of the following is true: url is
    //    not special; url's scheme is "ws" or "wss", then set encoding to
    //    UTF-8." (encoding is always UTF-8; see the header)
    if (ctx.state_override is None && c_is(ctx, m, 0x23)) || c_is_eof(ctx, m) {
        // 2. "If one of the following is true: state override is not given
        //    and c is U+0023 (#); c is the EOF code point, then:"
        // 2.1 "Let queryPercentEncodeSet be the special-query percent-encode
        //     set if url is special; otherwise the query percent-encode
        //     set."
        let query_percent_encode_set = if is_special(m.url) {
            clazel_percent::spec::PercentEncodeSet::SpecialQuery
        } else {
            clazel_percent::spec::PercentEncodeSet::Query
        };
        // 2.2 "Percent-encode after encoding, with encoding, buffer, and
        //     queryPercentEncodeSet, and append the result to url's query."
        let url = Url {
            query: query_append(
                m.url.query,
                clazel_percent::spec::percent_encode_after_encoding_utf8(m.buffer, query_percent_encode_set),
            ),
            ..m.url
        };
        // 2.3 "Set buffer to the empty string."
        let m = Machine { url: url, buffer: seq![], ..m };
        if c_is(ctx, m, 0x23) {
            // 2.4 "If c is U+0023 (#), then set url's fragment to the empty
            //     string and state to fragment state."
            Step::Continue(Machine { url: Url { fragment: Some(seq![]), ..url }, state: State::Fragment, ..m })
        } else {
            Step::Continue(m)
        }
    } else if !c_is_eof(ctx, m) {
        // 3. "Otherwise, if c is not the EOF code point:"
        // 3.1 "If c is not a URL code point and not U+0025 (%),
        //     invalid-URL-unit validation error." (validation error only)
        // 3.2 "If c is U+0025 (%) and remaining does not start with two ASCII
        //     hex digits, invalid-URL-unit validation error." (validation
        //     error only)
        // 3.3 "Append c to buffer."
        Step::Continue(Machine { buffer: m.buffer.push(c_of(ctx, m)), ..m })
    } else {
        Step::Continue(m)
    }
}

/// "fragment state" (<https://url.spec.whatwg.org/#fragment-state>)
pub open spec fn fragment_state(ctx: Ctx, m: Machine) -> Step {
    if !c_is_eof(ctx, m) {
        // 1. "If c is not the EOF code point, then:"
        // 1.1 "If c is not a URL code point and not U+0025 (%),
        //     invalid-URL-unit validation error." (validation error only)
        // 1.2 "If c is U+0025 (%) and remaining does not start with two ASCII
        //     hex digits, invalid-URL-unit validation error." (validation
        //     error only)
        // 1.3 "UTF-8 percent-encode c using the fragment percent-encode set
        //     and append the result to url's fragment."
        Step::Continue(
            Machine {
                url: Url {
                    fragment: fragment_append(
                        m.url.fragment,
                        clazel_percent::spec::utf8_percent_encode_code_point(
                            c_of(ctx, m),
                            clazel_percent::spec::PercentEncodeSet::Fragment,
                        ),
                    ),
                    ..m.url
                },
                ..m
            },
        )
    } else {
        Step::Continue(m)
    }
}

// ---------------------------------------------------------------------
// §4.4 The basic URL parser.
// ---------------------------------------------------------------------

/// Step 9, "switching on state": one run of the state machine. (Opaque to
/// the prover, so that proofs about [`run`] do not unfold every state;
/// see the header.)
#[verifier::opaque]
pub open spec fn state_step(ctx: Ctx, m: Machine) -> Step {
    match m.state {
        State::SchemeStart => scheme_start_state(ctx, m),
        State::Scheme => scheme_state(ctx, m),
        State::NoScheme => no_scheme_state(ctx, m),
        State::SpecialRelativeOrAuthority => special_relative_or_authority_state(ctx, m),
        State::PathOrAuthority => path_or_authority_state(ctx, m),
        State::Relative => relative_state(ctx, m),
        State::RelativeSlash => relative_slash_state(ctx, m),
        State::SpecialAuthoritySlashes => special_authority_slashes_state(ctx, m),
        State::SpecialAuthorityIgnoreSlashes => special_authority_ignore_slashes_state(ctx, m),
        State::Authority => authority_state(ctx, m),
        State::Host => host_state(ctx, m),
        State::Hostname => host_state(ctx, m),
        State::Port => port_state(ctx, m),
        State::File => file_state(ctx, m),
        State::FileSlash => file_slash_state(ctx, m),
        State::FileHost => file_host_state(ctx, m),
        State::PathStart => path_start_state(ctx, m),
        State::Path => path_state(ctx, m),
        State::OpaquePath => opaque_path_state(ctx, m),
        State::Query => query_state(ctx, m),
        State::Fragment => fragment_state(ctx, m),
    }
}

/// Step 9: "Keep running the following state machine by switching on
/// state. If after a run pointer points to the EOF code point, go to the
/// next step. Otherwise, increase pointer by 1 and continue with the state
/// machine." Then step 10, "Return url." `None` is failure.
pub open spec fn run(ctx: Ctx, m: Machine) -> Option<Url>
    decreases super::termination::phase(m.state), super::termination::pointer_measure(
        ctx.input.len(),
        m.pointer,
    ), super::termination::rank(m.state) via run_decreases
{
    match state_step(ctx, m) {
        Step::Failure => None,
        Step::Return(url) => Some(url),
        Step::Continue(next) => if next.pointer >= ctx.input.len() {
            // 10. "Return url."
            Some(next.url)
        } else {
            run(ctx, Machine { pointer: next.pointer + 1, ..next })
        },
    }
}

/// Termination of [`run`]: every run lowers the measure in
/// `termination.rs`.
#[via_fn]
pub proof fn run_decreases(ctx: Ctx, m: Machine) {
    super::termination::lemma_state_step_measure(ctx, m);
}

/// "The basic URL parser takes a scalar value string input, with an
/// optional null or base URL base (default null), an optional encoding
/// encoding (default UTF-8), an optional URL url, and an optional state
/// override state override" (<https://url.spec.whatwg.org/#concept-basic-url-parser>);
/// encoding is UTF-8 (see the header). `None` is failure; with a state
/// override, the result is the modified url (see the header).
pub open spec fn basic_url_parser_with(input: Seq<u32>, base: Option<Url>, url: Option<Url>, state_override: Option<State>, domain_parser: crate::host::spec::DomainParser) -> Option<Url> {
    // 1. "If url is not given:"
    let (url, input) = match url {
        None => {
            // 1.1 "Set url to a new URL."
            // 1.2 "If input contains any leading or trailing C0 control or
            //     space, invalid-URL-unit validation error." (validation
            //     error only)
            // 1.3 "Remove any leading and trailing C0 control or space from
            //     input."
            (new_url(), strip_trailing_c0_control_or_space(strip_leading_c0_control_or_space(input)))
        },
        Some(url) => (url, input),
    };
    // 2. "If input contains any ASCII tab or newline, invalid-URL-unit
    //    validation error." (validation error only)
    // 3. "Remove all ASCII tab or newline from input."
    let input = remove_ascii_tab_or_newline(input);
    // 4. "Let state be state override if given, or scheme start state
    //    otherwise."
    let state = match state_override {
        Some(s) => s,
        None => State::SchemeStart,
    };
    // 5. "Set encoding to the result of getting an output encoding from
    //    encoding." (UTF-8)
    // 6. "Let buffer be the empty string."
    // 7. "Let atSignSeen, insideBrackets, and passwordTokenSeen be false."
    // 8. "Let pointer be a pointer for input."
    let ctx = Ctx { input: input, base: base, state_override: state_override, domain_parser: domain_parser };
    // 9. "Keep running the following state machine [...]"
    // 10. "Return url."
    run(
        ctx,
        Machine {
            url: url,
            state: state,
            buffer: seq![],
            at_sign_seen: false,
            inside_brackets: false,
            password_token_seen: false,
            pointer: 0,
        },
    )
}

/// The basic URL parser on `input` with `base`, with no url and no state
/// override: what parsing a string means (item 1.10's entry point).
pub open spec fn basic_url_parser(input: Seq<u32>, base: Option<Url>, domain_parser: crate::host::spec::DomainParser) -> Option<Url> {
    basic_url_parser_with(input, base, None, None, domain_parser)
}

// ---------------------------------------------------------------------
// §4.5 URL serializing.
// ---------------------------------------------------------------------

/// URL path serializer step 4, "For each segment of path: append U+002F
/// (/) followed by segment to output": the output for `path`, built from
/// its first segment to its last.
pub open spec fn serialize_segments(path: Seq<Seq<u32>>) -> Seq<u32>
    decreases path.len()
{
    if path.len() == 0 {
        seq![]
    } else {
        serialize_segments(path.drop_last()) + seq![0x2Fu32] + path.last()
    }
}

/// "The URL path serializer takes a URL or URL path urlOrPath and then
/// runs these steps. They return an ASCII string."
/// (<https://url.spec.whatwg.org/#url-path-serializer>)
pub open spec fn url_path_serializer(path: UrlPath) -> Seq<u32> {
    // 1. "Let path be urlOrPath's path if urlOrPath is a URL; otherwise
    //    urlOrPath." (callers pass the path)
    match path {
        // 2. "If path is a URL path segment, then return path."
        UrlPath::Opaque(s) => s,
        // 3. "Let output be the empty string."
        // 4. "For each segment of path: append U+002F (/) followed by
        //    segment to output."
        // 5. "Return output."
        UrlPath::List(l) => serialize_segments(l),
    }
}

/// "The URL serializer takes a URL url, with an optional boolean exclude
/// fragment (default false), and then runs these steps. They return an
/// ASCII string." (<https://url.spec.whatwg.org/#concept-url-serializer>)
pub open spec fn url_serializer(url: Url, exclude_fragment: bool) -> Seq<u32> {
    // 1. "Let output be url's scheme and U+003A (:) concatenated."
    let output = url.scheme + seq![0x3Au32];
    // 2. "If url's host is non-null:"
    let output = match url.host {
        Some(host) => {
            // 2.1 "Append "//" to output."
            let output = output + seq![0x2Fu32, 0x2F];
            // 2.2 "If url includes credentials, then:"
            let output = if includes_credentials(url) {
                // 2.2.1 "Append url's username to output."
                let output = output + url.username;
                // 2.2.2 "If url's password is not the empty string, then
                //       append U+003A (:), followed by url's password, to
                //       output."
                let output = if url.password.len() > 0 {
                    output + seq![0x3Au32] + url.password
                } else {
                    output
                };
                // 2.2.3 "Append U+0040 (@) to output."
                output + seq![0x40u32]
            } else {
                output
            };
            // 2.3 "Append url's host, serialized, to output."
            let output = output + crate::host::spec::host_serializer(host);
            // 2.4 "If url's port is non-null, append U+003A (:) followed by
            //     url's port, serialized, to output."
            match url.port {
                Some(port) => output + seq![0x3Au32] + crate::host::spec::serialize_integer(port),
                None => output,
            }
        },
        None => output,
    };
    // 3. "If url's host is null, url does not have an opaque path, url's
    //    path's size is greater than 1, and url's path[0] is the empty
    //    string, then append U+002F (/) followed by U+002E (.) to output."
    let output = if url.host is None && (url.path matches UrlPath::List(p) && p.len() > 1 && p[0].len() == 0) {
        output + seq![0x2Fu32, 0x2E]
    } else {
        output
    };
    // 4. "Append the result of URL path serializing url to output."
    let output = output + url_path_serializer(url.path);
    // 5. "If url's query is non-null, append U+003F (?), followed by url's
    //    query, to output."
    let output = match url.query {
        Some(query) => output + seq![0x3Fu32] + query,
        None => output,
    };
    // 6. "If exclude fragment is false and url's fragment is non-null, then
    //    append U+0023 (#), followed by url's fragment, to output."
    let output = match url.fragment {
        Some(fragment) => if !exclude_fragment {
            output + seq![0x23u32] + fragment
        } else {
            output
        },
        None => output,
    };
    // 7. "Return output."
    output
}

} // verus!
