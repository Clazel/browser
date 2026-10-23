//! Differential test against `cookie_store` (the cookie jar of reqwest's
//! `cookie_store` feature, which follows RFC 6265 and parses with the
//! `cookie` crate), on random Set-Cookie strings and random set and get
//! sequences (docs/phases/phase-2.md item 2.9).
//!
//! A sequence is a few operations on a fresh jar in each engine: set a
//! cookie string from a URL (as an HTTP response), or get the cookies for
//! a URL (as an HTTP request). The two must return the same cookies for
//! every get, as a multiset of `name=value` (`cookie_store` does not order
//! them). The generator stays inside what RFC 6265 and RFC 6265bis agree
//! on and what `cookie_store` implements:
//!
//! - names and values of a few letters and digits (no nameless cookies:
//!   RFC 6265bis allows them and `cookie_store` does not), no
//!   SameSite, no name prefixes, no control characters or long strings;
//! - names drawn from separate pools for host-only, domain, `Secure` and
//!   `Secure` domain cookies: RFC 6265 takes a host-only cookie and a domain
//!   cookie of the same name, domain and path for one cookie (6265bis, for
//!   two), and lets an insecure request overwrite a `Secure` cookie
//!   (6265bis §5.7 step 16 does not); `Secure` is set only over `https`
//!   (step 13 ignores it otherwise);
//! - the hosts `example.test`, `www.example.test`, `a.www.example.test` and
//!   `other.test` (`test` is a public suffix under the list's default rule,
//!   and `cookie_store` is built without a list, so `Domain=test` is never
//!   generated);
//! - `Path`, `Domain` (with or without a leading dot), `Secure`,
//!   `HttpOnly`, and `Max-Age` of 0, a large number, or a negative number
//!   (`Expires` and small `Max-Age` depend on the clock, which the engines
//!   read separately; ours is the system time);
//! - requests over `https` and `http`.
//!
//! The generator is a fixed-seed linear congruential generator, so a run is
//! reproducible. Prints `clazel-conformance:` with the number of sequences
//! whose gets all agree.
//!
//! Skipped under Miri (`#[cfg_attr(miri, ignore)]`, as `clazel-psl`'s
//! differential test is): `cookie_store` reads the system clock, which Miri's
//! isolation refuses, and each of our steps scans the Public Suffix List at
//! about ten seconds a step under Miri. The two other conformance tests of
//! this crate run a sample of their cases under Miri.

mod support;

use clazel_cookie::storage::exec::CookieRecord;
use cookie_store::CookieStore;
use url::Url;

/// A fixed-seed generator (Knuth's MMIX constants).
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 = self
            .0
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        self.0 >> 33
    }

    fn below(&mut self, n: usize) -> usize {
        let n = u64::try_from(n).unwrap_or(1).max(1);
        usize::try_from(self.next().checked_rem(n).unwrap_or(0)).unwrap_or(0)
    }

    fn pick<'a>(&mut self, items: &[&'a str]) -> &'a str {
        items.get(self.below(items.len())).copied().unwrap_or("")
    }
}

const HOSTS: &[&str] = &[
    "example.test",
    "www.example.test",
    "a.www.example.test",
    "other.test",
];
const PATHS: &[&str] = &["/", "/a", "/a/b", "/a/b/c", "/ab"];
const NAMES: &[&str] = &["a", "b", "c", "ab"];
const DOMAIN_NAMES: &[&str] = &["d", "e", "de"];
const SECURE_NAMES: &[&str] = &["s", "t", "st"];
const SECURE_DOMAIN_NAMES: &[&str] = &["u", "v", "uv"];
const VALUES: &[&str] = &["1", "2", "x", "yz", ""];
const ATTR_PATHS: &[&str] = &["/", "/a", "/a/b", "/ab", "a", ""];
const DOMAINS: &[&str] = &[
    "example.test",
    ".example.test",
    "www.example.test",
    "a.www.example.test",
    "other.test",
    "EXAMPLE.test",
];
const MAX_AGES: &[&str] = &["0", "1000000", "-5", "99999999"];

/// A random request URL.
fn url(rng: &mut Rng) -> String {
    let scheme = if rng.below(3) == 0 { "http" } else { "https" };
    format!("{scheme}://{}{}", rng.pick(HOSTS), rng.pick(PATHS))
}

/// A random Set-Cookie string for a request over `https` (or not).
///
/// The name comes from a pool for the kind of cookie, so that RFC 6265 and
/// RFC 6265bis agree on which cookie replaces which: a host-only cookie and
/// a domain cookie of the same name, domain and path are one cookie in RFC
/// 6265 and two in RFC 6265bis, and RFC 6265bis (§5.7 step 16) does not let
/// an insecure request overwrite a `Secure` cookie of the same name, which
/// RFC 6265 does.
fn set_cookie_string(rng: &mut Rng, https: bool) -> String {
    let domain_cookie = rng.below(3) == 0;
    let secure = https && rng.below(3) == 0;
    let names = match (domain_cookie, secure) {
        (false, false) => NAMES,
        (true, false) => DOMAIN_NAMES,
        (false, true) => SECURE_NAMES,
        (true, true) => SECURE_DOMAIN_NAMES,
    };
    let mut s = format!("{}={}", rng.pick(names), rng.pick(VALUES));
    if domain_cookie {
        s.push_str(&format!("; Domain={}", rng.pick(DOMAINS)));
    } else if rng.below(8) == 0 {
        s.push_str("; Domain=");
    }
    if secure {
        s.push_str("; Secure");
    }
    for _ in 0..rng.below(4) {
        match rng.below(3) {
            0 => s.push_str(&format!("; Path={}", rng.pick(ATTR_PATHS))),
            1 => s.push_str("; HttpOnly"),
            _ => s.push_str(&format!("; Max-Age={}", rng.pick(MAX_AGES))),
        }
    }
    s
}

/// `name=value` pairs of a cookie-string, sorted.
fn pairs(cookie_string: &str) -> Vec<(String, String)> {
    let mut out: Vec<(String, String)> = cookie_string
        .split("; ")
        .filter(|p| !p.is_empty())
        .map(|p| match p.split_once('=') {
            Some((n, v)) => (n.to_owned(), v.to_owned()),
            None => (String::new(), p.to_owned()),
        })
        .collect();
    out.sort();
    out
}

/// One sequence; the number of gets on which the engines disagree, and a
/// description of the first disagreement.
fn sequence(seed: u64, now: u64) -> Option<String> {
    let mut rng = Rng(seed);
    let mut store = CookieStore::default();
    let mut jar: Vec<CookieRecord> = Vec::new();
    let mut log: Vec<String> = Vec::new();
    for step in 0..12 {
        let target = url(&mut rng);
        let (Ok(theirs), Some(ours)) = (Url::parse(&target), support::parse(&target)) else {
            return Some(format!("{target}: does not parse"));
        };
        if rng.below(2) == 0 {
            let cookie = set_cookie_string(&mut rng, target.starts_with("https:"));
            log.push(format!("set {target} {cookie:?}"));
            let _ = store.parse(&cookie, &theirs);
            let context = support::http_context(&ours);
            match support::set_cookie(&jar, cookie.as_bytes(), &ours, &context, now) {
                Some(next) => jar = next,
                None => return Some(format!("{target}: no request URL")),
            }
        } else {
            let mut want: Vec<(String, String)> = store
                .get_request_values(&theirs)
                .map(|(n, v)| (n.to_owned(), v.to_owned()))
                .collect();
            want.sort();
            let context = support::http_context(&ours);
            let Some(got) = support::cookie_string(&mut jar, &ours, &context, now) else {
                return Some(format!("{target}: no request URL"));
            };
            let got = pairs(&String::from_utf8_lossy(&got));
            if got != want {
                return Some(format!(
                    "seed {seed} step {step}: get {target}: ours {got:?}, cookie_store {want:?}; after {log:?}"
                ));
            }
        }
    }
    None
}

#[test]
#[cfg_attr(miri, ignore)]
fn differential_cookie_store() {
    let sequences: u64 = 3000;
    let now_unix = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map_or(1_792_713_600, |d| d.as_secs());
    let now = support::since_1601(now_unix);
    let mut pass: u64 = 0;
    let mut failed: u64 = 0;
    for i in 0..sequences {
        match sequence(i.wrapping_mul(0x9E37_79B9).wrapping_add(1), now) {
            None => pass = pass.saturating_add(1),
            Some(why) => {
                failed = failed.saturating_add(1);
                if failed <= 10 {
                    println!("FAIL {why}");
                }
            }
        }
    }
    println!(
        "clazel-conformance: suite=\"cookie_store differential, random set and get sequences\" pass={pass} xfail=0 fail={failed} total={sequences}"
    );
    assert_eq!(failed, 0);
}
