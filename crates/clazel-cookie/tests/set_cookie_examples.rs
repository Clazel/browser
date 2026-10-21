//! Worked examples of the executable Set-Cookie parser and the matching
//! functions, written by us from the draft's own examples (§4.1.3, §5.4)
//! and from the algorithm. They are not an official suite and are not
//! counted as conformance; the proofs are what ties the code to the spec.

use clazel_cookie::matching::exec::{default_path, domain_matches, path_matches};
use clazel_cookie::set_cookie::exec::{
    AttributeExec, name_prefix_requirements_met, parse_a_set_cookie_string,
};
use clazel_cookie::set_cookie::spec::SameSite;

#[test]
fn name_value_and_attributes() {
    let c = parse_a_set_cookie_string(
        b" a = b c ; Path=/x; secure ;HttpOnly; SameSite=lax; Max-Age=10; Domain=.Example.COM",
        b"/p/q",
        1000,
    )
    .map(|c| (c.name, c.value, c.attributes));
    assert!(c.is_some());
    let (name, value, attributes) = c.unwrap_or_default();
    assert_eq!(name, b"a");
    assert_eq!(value, b"b c");
    assert_eq!(attributes.len(), 6);
    assert!(matches!(attributes.first(), Some(AttributeExec::Path(p)) if p == b"/x"));
    assert!(matches!(attributes.get(1), Some(AttributeExec::Secure)));
    assert!(matches!(attributes.get(2), Some(AttributeExec::HttpOnly)));
    assert!(matches!(
        attributes.get(3),
        Some(AttributeExec::SameSite(SameSite::Lax))
    ));
    assert!(matches!(
        attributes.get(4),
        Some(AttributeExec::MaxAge(1010))
    ));
    assert!(matches!(attributes.get(5), Some(AttributeExec::Domain(d)) if d == b"example.com"));
}

#[test]
fn nameless_and_rejected() {
    let parsed = parse_a_set_cookie_string(b"abc", b"/", 0);
    assert!(parsed.is_some());
    let Some(c) = parsed else {
        return;
    };
    assert!(c.name.is_empty());
    assert_eq!(c.value, b"abc");
    assert!(parse_a_set_cookie_string(b"a=b\x01", b"/", 0).is_none());
    assert!(parse_a_set_cookie_string(b"a=b\x7f", b"/", 0).is_none());
    assert!(parse_a_set_cookie_string(b"a=b\t;Secure", b"/", 0).is_some());
    let long = vec![b'x'; 4097];
    assert!(parse_a_set_cookie_string(&long, b"/", 0).is_none());
}

#[test]
fn max_age_and_limits() {
    let age = |v: &[u8]| {
        let mut s = b"a=b; Max-Age=".to_vec();
        s.extend_from_slice(v);
        parse_a_set_cookie_string(&s, b"/", 1000).and_then(|c| c.attributes.into_iter().next())
    };
    assert!(matches!(age(b"0"), Some(AttributeExec::MaxAge(0))));
    assert!(matches!(age(b"-5"), Some(AttributeExec::MaxAge(0))));
    assert!(matches!(
        age(b"99999999999999999999999"),
        Some(AttributeExec::MaxAge(34_561_000))
    ));
    assert!(age(b"").is_none());
    assert!(age(b"-").is_none());
    assert!(age(b"1x").is_none());
}

#[test]
fn prefixes() {
    let ok = |s: &[u8], secure: bool, host_only: bool| {
        parse_a_set_cookie_string(s, b"/", 0)
            .is_some_and(|c| name_prefix_requirements_met(&c, secure, host_only))
    };
    assert!(!ok(b"__Secure-SID=1", false, true));
    assert!(ok(b"__SECURE-SID=1; Secure", true, true));
    assert!(!ok(b"__Host-SID=1; Secure", true, true));
    assert!(ok(b"__host-SID=1; Secure; Path=/", true, true));
    assert!(!ok(b"__Host-SID=1; Secure; Path=/", true, false));
    assert!(!ok(b"=__Host-x", true, true));
}

#[test]
fn matching() {
    assert!(domain_matches(b"www.example.com", true, b"example.com"));
    assert!(!domain_matches(b"wwwexample.com", true, b"example.com"));
    assert!(!domain_matches(b"1.2.3.4", false, b"3.4"));
    assert_eq!(default_path(b"/a/b/c"), b"/a/b");
    assert_eq!(default_path(b"/a"), b"/");
    assert_eq!(default_path(b"a/b"), b"/");
    assert!(path_matches(b"/a/b", b"/a"));
    assert!(path_matches(b"/a/b", b"/a/"));
    assert!(!path_matches(b"/ab", b"/a"));
}
