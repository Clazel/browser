//! A second transcription of domain-match, default-path and path-match,
//! from RFC 6265 (April 2011) §5.1.3 and §5.1.4, and a proof that it equals
//! [`super::spec`] on every input.
//!
//! RFC 6265bis did not change these three algorithms, so the older RFC is
//! the independent source: the two documents were written five years
//! apart and are not copies of each other. Where the spec reads strings
//! as sequences and recurses on them, this transcription states each
//! condition on indices, and where the spec counts "/" characters it asks
//! whether any "/" follows the first, then picks the right-most "/" as the
//! only index with none after it.
//!
//! §5.1.2 is not transcribed here: RFC 6265's version (an IDNA2003-era
//! "lower case, and convert to ASCII") is the one 6265bis replaced, and
//! what browsers run is the URL Standard's host parser, which
//! `crate::matching::spec` uses and `clazel-url` proves.
//!
//! Equal on every input, with the exceptions listed here: none.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// RFC 6265 §5.1.3: "A string domain-matches a given domain string if at
/// least one of the following conditions hold".
pub open spec fn domain_matches_6265(string: Seq<u8>, string_is_host_name: bool, domain: Seq<u8>) -> bool {
    // "The domain string and the string are identical."
    (string.len() == domain.len() && forall|i: int| 0 <= i < string.len() ==> #[trigger] string[i] == domain[i])
    // "All of the following conditions hold:"
    || (
        // "The domain string is a suffix of the string."
        domain.len() <= string.len()
        && (forall|i: int| 0 <= i < domain.len() ==> #[trigger] string[string.len() - domain.len() + i] == domain[i])
        // "The last character of the string that is not included in the
        // domain string is a %x2E (".") character." (That character
        // exists only if the string is longer than the domain string.)
        && domain.len() < string.len()
        && string[string.len() - domain.len() - 1] == 0x2E
        // "The string is a host name (i.e., not an IP address)."
        && string_is_host_name
    )
}

/// `k` is the index of the right-most "/" of `p`: a "/" with no "/" after it.
pub open spec fn is_rightmost_slash(p: Seq<u8>, k: int) -> bool {
    0 <= k < p.len() && p[k] == 0x2F && (forall|j: int| k < j < p.len() ==> #[trigger] p[j] != 0x2F)
}

/// RFC 6265 §5.1.4's default-path algorithm, from the uri-path of step 1.
pub open spec fn default_path_6265(uri_path: Seq<u8>) -> Seq<u8> {
    // 2. "If the uri-path is empty or if the first character of the uri-path
    //    is not a %x2F ("/") character, output %x2F ("/") and skip the
    //    remaining steps."
    if uri_path.len() == 0 || uri_path[0] != 0x2F {
        seq![0x2Fu8]
    // 3. "If the uri-path contains no more than one %x2F ("/") character,
    //    output %x2F ("/") and skip the remaining step." (The first
    //    character is one; there is no other if none of the rest is.)
    } else if forall|j: int| 1 <= j < uri_path.len() ==> #[trigger] uri_path[j] != 0x2F {
        seq![0x2Fu8]
    } else {
        // 4. "Output the characters of the uri-path from the first
        //    character up to, but not including, the right-most %x2F ("/")."
        let k = choose|k: int| is_rightmost_slash(uri_path, k);
        uri_path.subrange(0, k)
    }
}

/// RFC 6265 §5.1.4: "A request-path path-matches a given cookie-path if at
/// least one of the following conditions holds".
pub open spec fn path_matches_6265(request_path: Seq<u8>, cookie_path: Seq<u8>) -> bool {
    // "The cookie-path and the request-path are identical."
    (cookie_path.len() == request_path.len() && forall|i: int| 0 <= i < cookie_path.len() ==> #[trigger] cookie_path[i]
        == request_path[i])
    // "The cookie-path is a prefix of the request-path, and the last
    // character of the cookie-path is %x2F ("/")." / "The cookie-path is a
    // prefix of the request-path, and the first character of the
    // request-path that is not included in the cookie-path is a %x2F ("/")
    // character."
    || (cookie_path.len() <= request_path.len()
        && (forall|i: int| 0 <= i < cookie_path.len() ==> #[trigger] cookie_path[i] == request_path[i])
        && ((cookie_path.len() > 0 && cookie_path[cookie_path.len() - 1] == 0x2F)
            || (cookie_path.len() < request_path.len() && request_path[cookie_path.len() as int] == 0x2F)))
}

/// Domain-match agrees with the spec on every input.
pub proof fn lemma_domain_matches_agree(string: Seq<u8>, string_is_host_name: bool, domain: Seq<u8>)
    ensures
        domain_matches_6265(string, string_is_host_name, domain) == domain_matches(string, string_is_host_name, domain),
{
    if string.len() == domain.len() && (forall|i: int| 0 <= i < string.len() ==> #[trigger] string[i] == domain[i]) {
        assert(string =~= domain);
    }
    if domain_matches(string, string_is_host_name, domain) && string != domain {
        let k = string.len() - domain.len();
        assert(string.skip(k) =~= domain);
        assert forall|i: int| 0 <= i < domain.len() implies #[trigger] string[string.len() - domain.len() + i] == domain[i] by {
            assert(string.skip(k)[i] == domain[i]);
        }
    }
    if domain_matches_6265(string, string_is_host_name, domain) && !(string.len() == domain.len() && (forall|i: int|
        0 <= i < string.len() ==> #[trigger] string[i] == domain[i])) {
        let k = string.len() - domain.len();
        assert(string.skip(k) =~= domain) by {
            assert forall|i: int| 0 <= i < domain.len() implies #[trigger] string.skip(k)[i] == domain[i] by {
                assert(string[string.len() - domain.len() + i] == domain[i]);
            }
        }
    }
}

/// With a "/" first, there is one "/" at most exactly when no other index
/// has one.
proof fn lemma_slash_count_one(p: Seq<u8>)
    requires
        p.len() > 0,
        p[0] == 0x2F,
    ensures
        (slash_count(p) <= 1) <==> (forall|j: int| 1 <= j < p.len() ==> #[trigger] p[j] != 0x2F),
        slash_count(p) >= 1,
    decreases p.len()
{
    let t = p.drop_last();
    if p.len() == 1 {
        assert(t =~= Seq::<u8>::empty());
        assert(slash_count(p) == 1);
    } else {
        assert(t[0] == p[0]);
        lemma_slash_count_one(t);
        assert forall|j: int| 1 <= j < t.len() implies t[j] == p[j] by {}
        let last = p[p.len() - 1];
        assert(slash_count(p) == slash_count(t) + if last == 0x2F { 1nat } else { 0nat });
        if last == 0x2F {
            assert(p[p.len() - 1] == 0x2F);
            assert(slash_count(p) >= 2);
            assert(!(forall|j: int| 1 <= j < p.len() ==> #[trigger] p[j] != 0x2F));
        } else {
            if !(forall|j: int| 1 <= j < t.len() ==> #[trigger] t[j] != 0x2F) {
                let j = choose|j: int| 1 <= j < t.len() && t[j] == 0x2F;
                assert(p[j] == 0x2F);
            }
        }
    }
}

/// `rightmost_slash` is the index of [`is_rightmost_slash`], when there is
/// one.
proof fn lemma_rightmost_is_last(p: Seq<u8>)
    ensures
        rightmost_slash(p) >= 0 ==> is_rightmost_slash(p, rightmost_slash(p)),
    decreases p.len()
{
    if p.len() > 0 && p[p.len() - 1] != 0x2F {
        let t = p.drop_last();
        lemma_rightmost_is_last(t);
        if rightmost_slash(t) >= 0 {
            assert forall|j: int| rightmost_slash(p) < j < p.len() implies #[trigger] p[j] != 0x2F by {
                if j < t.len() {
                    assert(t[j] == p[j]);
                }
            }
        }
    }
}

/// The right-most "/" of `rightmost_slash` is the index of
/// [`is_rightmost_slash`], and it is the only one.
proof fn lemma_rightmost_is_unique(p: Seq<u8>, k: int)
    requires
        is_rightmost_slash(p, k),
    ensures
        rightmost_slash(p) == k,
    decreases p.len()
{
    if p[p.len() - 1] == 0x2F {
        assert(k == p.len() - 1) by {
            if k < p.len() - 1 {
                assert(p[p.len() - 1] != 0x2F);
            }
        }
    } else {
        let t = p.drop_last();
        assert(k < p.len() - 1);
        assert(is_rightmost_slash(t, k)) by {
            assert forall|j: int| k < j < t.len() implies #[trigger] t[j] != 0x2F by {
                assert(t[j] == p[j]);
            }
        }
        lemma_rightmost_is_unique(t, k);
    }
}

/// Default-path agrees with the spec on every input.
pub proof fn lemma_default_path_agrees(uri_path: Seq<u8>)
    ensures
        default_path_6265(uri_path) == default_path(uri_path),
{
    if uri_path.len() > 0 && uri_path[0] == 0x2F {
        lemma_slash_count_one(uri_path);
        if slash_count(uri_path) > 1 {
            super::lemmas::lemma_rightmost_slash(uri_path);
            lemma_rightmost_is_last(uri_path);
            let r = rightmost_slash(uri_path);
            let k = choose|k: int| is_rightmost_slash(uri_path, k);
            lemma_rightmost_is_unique(uri_path, k);
            lemma_rightmost_is_unique(uri_path, r);
            assert(uri_path.take(r) =~= uri_path.subrange(0, r));
        }
    }
}

/// Path-match agrees with the spec on every input.
pub proof fn lemma_path_matches_agree(request_path: Seq<u8>, cookie_path: Seq<u8>)
    ensures
        path_matches_6265(request_path, cookie_path) == path_matches(request_path, cookie_path),
{
    if cookie_path == request_path {
        assert(path_matches_6265(request_path, cookie_path));
    }
    if cookie_path.len() <= request_path.len() && (forall|i: int| 0 <= i < cookie_path.len() ==> #[trigger] cookie_path[i]
        == request_path[i]) {
        assert(cookie_path.is_prefix_of(request_path)) by {
            assert(request_path.subrange(0, cookie_path.len() as int) =~= cookie_path);
        }
    }
    if cookie_path.is_prefix_of(request_path) {
        assert forall|i: int| 0 <= i < cookie_path.len() implies #[trigger] cookie_path[i] == request_path[i] by {
            assert(request_path.subrange(0, cookie_path.len() as int)[i] == cookie_path[i]);
        }
    }
    if path_matches_6265(request_path, cookie_path) && cookie_path.len() == request_path.len() {
        assert(cookie_path =~= request_path);
    }
}

} // verus!
