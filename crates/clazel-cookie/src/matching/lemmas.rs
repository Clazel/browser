//! Facts proven about [`super::spec`]. They are evidence that the
//! transcription is right (for example that domain-match is an order on
//! host names), not part of what the implementation must meet.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------
// §5.1.3 domain matching.
// ---------------------------------------------------------------------

/// A string domain-matches itself.
pub proof fn lemma_domain_match_reflexive(s: Seq<u8>, string_is_host_name: bool)
    ensures
        domain_matches(s, string_is_host_name, s),
{
}

/// Domain-match is transitive on host names: if `s` domain-matches `d1`
/// and `d1` (itself a host name) domain-matches `d2`, then `s`
/// domain-matches `d2`.
pub proof fn lemma_domain_match_transitive(s: Seq<u8>, d1: Seq<u8>, d2: Seq<u8>)
    requires
        domain_matches(s, true, d1),
        domain_matches(d1, true, d2),
    ensures
        domain_matches(s, true, d2),
{
    if s != d1 && d1 != d2 {
        let k = s.len() - d2.len();
        assert(d2.is_suffix_of(s)) by {
            assert forall|i: int| 0 <= i < d2.len() implies s.skip(k)[i] == d2[i] by {
                assert(s.skip(s.len() - d1.len())[(d1.len() - d2.len() + i)] == d1[d1.len() - d2.len() + i]);
                assert(d1.skip(d1.len() - d2.len())[i] == d2[i]);
            }
            assert(s.skip(k) =~= d2);
        }
        assert(s[s.len() - d2.len() - 1] == 0x2E) by {
            let j = d1.len() - d2.len() - 1;
            assert(s.skip(s.len() - d1.len())[j] == d1[j]);
        }
    }
}

/// A domain-match other than identity splits the string at a "." that
/// precedes the domain.
pub proof fn lemma_domain_match_is_suffix(string: Seq<u8>, string_is_host_name: bool, domain: Seq<u8>)
    requires
        domain_matches(string, string_is_host_name, domain),
    ensures
        domain.is_suffix_of(string),
{
    if string == domain {
        assert(domain.is_suffix_of(string)) by {
            assert(string.skip(0) =~= string);
        }
    }
}

/// An IP address (not a host name) only domain-matches itself.
pub proof fn lemma_ip_address_matches_only_itself(string: Seq<u8>, domain: Seq<u8>)
    requires
        domain_matches(string, false, domain),
    ensures
        string == domain,
{
}

// ---------------------------------------------------------------------
// §5.1.4 default-path and path-match.
// ---------------------------------------------------------------------

/// A string with a "/" has a right-most one, which is a "/".
pub proof fn lemma_rightmost_slash(s: Seq<u8>)
    ensures
        slash_count(s) > 0 ==> 0 <= rightmost_slash(s) < s.len(),
        0 <= rightmost_slash(s) ==> (rightmost_slash(s) < s.len() && s[rightmost_slash(s)] == 0x2F),
        rightmost_slash(s) < 0 ==> slash_count(s) == 0,
    decreases s.len()
{
    if s.len() > 0 {
        lemma_rightmost_slash(s.drop_last());
    }
}

/// The default-path starts with "/", and is a prefix of the uri-path
/// whenever the uri-path begins with "/".
pub proof fn lemma_default_path_shape(uri_path: Seq<u8>)
    ensures
        default_path(uri_path).len() > 0,
        default_path(uri_path)[0] == 0x2F,
        (uri_path.len() > 0 && uri_path[0] == 0x2F) ==> (default_path(uri_path).len() <= uri_path.len()
            && default_path(uri_path).is_prefix_of(uri_path)),
{
    if uri_path.len() > 0 && uri_path[0] == 0x2F && slash_count(uri_path) > 1 {
        lemma_rightmost_slash(uri_path);
        let k = rightmost_slash(uri_path);
        // The uri-path has two slashes, so the right-most is not the first:
        // otherwise every slash would be at index 0, and there is one.
        lemma_slash_count_at_most_one_when_rightmost_first(uri_path);
        assert(k > 0);
        assert(default_path(uri_path) =~= uri_path.take(k));
        assert(default_path(uri_path)[0] == uri_path[0]);
    } else if uri_path.len() > 0 && uri_path[0] == 0x2F {
        assert(seq![0x2Fu8].is_prefix_of(uri_path)) by {
            assert(uri_path.subrange(0, 1) =~= seq![0x2Fu8]);
        }
    }
}

/// If the right-most "/" is at index 0, there is exactly one "/".
proof fn lemma_slash_count_at_most_one_when_rightmost_first(s: Seq<u8>)
    requires
        s.len() > 0,
        s[0] == 0x2F,
        slash_count(s) > 1,
    ensures
        rightmost_slash(s) > 0,
    decreases s.len()
{
    if s.len() == 1 {
        assert(s.drop_last() =~= Seq::<u8>::empty());
    } else if s[s.len() - 1] != 0x2F {
        lemma_slash_count_at_most_one_when_rightmost_first(s.drop_last());
        assert(s.drop_last()[0] == s[0]);
    }
}

/// The default-path of a uri-path that begins with "/" path-matches it.
pub proof fn lemma_default_path_matches(uri_path: Seq<u8>)
    requires
        uri_path.len() > 0,
        uri_path[0] == 0x2F,
    ensures
        path_matches(uri_path, default_path(uri_path)),
{
    lemma_default_path_shape(uri_path);
    let d = default_path(uri_path);
    if slash_count(uri_path) <= 1 {
        // d is "/", and the uri-path starts with it.
        assert(d =~= seq![0x2Fu8]);
        assert(d[d.len() - 1] == 0x2F);
    } else {
        lemma_rightmost_slash(uri_path);
        let k = rightmost_slash(uri_path);
        assert(d =~= uri_path.take(k));
        assert(uri_path[k] == 0x2F);
        assert(d.len() == k);
        assert(uri_path.len() > d.len());
        assert(uri_path[d.len() as int] == 0x2F);
    }
}

/// A request-path path-matches itself.
pub proof fn lemma_path_match_reflexive(p: Seq<u8>)
    ensures
        path_matches(p, p),
{
}

/// If a request-path path-matches a cookie-path, the cookie-path is a
/// prefix of it.
pub proof fn lemma_path_match_is_prefix(request_path: Seq<u8>, cookie_path: Seq<u8>)
    requires
        path_matches(request_path, cookie_path),
    ensures
        cookie_path.is_prefix_of(request_path),
{
    if cookie_path == request_path {
        assert(cookie_path.is_prefix_of(request_path)) by {
            assert(request_path.subrange(0, request_path.len() as int) =~= request_path);
        }
    }
}

/// Path-match is transitive: it is a preorder on paths.
pub proof fn lemma_path_match_transitive(r: Seq<u8>, c1: Seq<u8>, c2: Seq<u8>)
    requires
        path_matches(r, c1),
        path_matches(c1, c2),
    ensures
        path_matches(r, c2),
{
    lemma_path_match_is_prefix(r, c1);
    lemma_path_match_is_prefix(c1, c2);
    if c1 != r && c2 != c1 {
        // c2 is a prefix of c1, which is a prefix of r.
        assert(c2.is_prefix_of(r)) by {
            assert forall|i: int| 0 <= i < c2.len() implies r.subrange(0, c2.len() as int)[i] == c2[i] by {
                assert(c1.subrange(0, c2.len() as int)[i] == c2[i]);
                assert(r.subrange(0, c1.len() as int)[i] == c1[i]);
            }
            assert(r.subrange(0, c2.len() as int) =~= c2);
        }
        // Either c2 ends with "/", or c1 continues with "/" after c2, and
        // then so does r.
        if !(c2.len() > 0 && c2[c2.len() - 1] == 0x2F) {
            assert(c1.len() > c2.len() && c1[c2.len() as int] == 0x2F);
            assert(r.subrange(0, c1.len() as int)[c2.len() as int] == c1[c2.len() as int]);
            assert(r.len() > c2.len());
        }
    }
}

/// Path-match is antisymmetric: paths that match each other are equal.
pub proof fn lemma_path_match_antisymmetric(a: Seq<u8>, b: Seq<u8>)
    requires
        path_matches(a, b),
        path_matches(b, a),
    ensures
        a == b,
{
    lemma_path_match_is_prefix(a, b);
    lemma_path_match_is_prefix(b, a);
    assert(a =~= b) by {
        assert(a.len() == b.len());
        assert forall|i: int| 0 <= i < a.len() implies a[i] == b[i] by {
            assert(a.subrange(0, b.len() as int)[i] == b[i]);
        }
    }
}

} // verus!
