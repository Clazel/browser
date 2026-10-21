//! Differential test against the `publicsuffix` crate (an independent
//! implementation, loaded with the same vendored list): for every ASCII rule
//! of the list, the rule's domain (with `*` replaced by a label), that
//! domain with one and with two labels above it, and with a label that is
//! not in the list above it, the public suffix and registrable domain of
//! `clazel-psl` must equal the crate's. (Rules with non-ASCII labels are
//! left out: the crate, without its `idna` feature, matches ASCII hosts
//! only.)
//!
//! Prints one `clazel-conformance:` line (format in `xtask/src/conformance.rs`).

use clazel_psl::exec::{public_suffix_of_domain_exec, registrable_domain_of_domain_exec};
use publicsuffix::{List, Psl};

const LIST: &str = include_str!("../data/publicsuffix-5dd321ff/public_suffix_list.dat");

fn to_u32(s: &str) -> Vec<u32> {
    s.bytes().map(u32::from).collect()
}

fn text(v: Option<Vec<u32>>) -> Option<String> {
    v.map(|v| v.iter().filter_map(|c| char::from_u32(*c)).collect())
}

#[test]
fn differential() {
    let parsed = LIST.parse::<List>();
    assert!(parsed.is_ok(), "the vendored list parses");
    let Ok(list) = parsed else { return };
    let mut domains: Vec<String> = Vec::new();
    for line in LIST.lines() {
        let Some(rule) = line.split_whitespace().next() else {
            continue;
        };
        if rule.starts_with("//") || !rule.is_ascii() {
            continue;
        }
        let rule = rule.trim_start_matches('!').replace('*', "wild");
        domains.push(rule.clone());
        domains.push(format!("www.{rule}"));
        domains.push(format!("a.b.{rule}"));
        domains.push(format!("zz-not-listed.{rule}"));
        domains.push(format!("{rule}."));
    }
    let total = domains.len();
    let mut pass = 0usize;
    let mut failures = Vec::new();
    for d in &domains {
        let bytes = d.as_bytes();
        let want_suffix = list
            .suffix(bytes)
            .map(|s| String::from_utf8_lossy(s.as_bytes()).into_owned());
        let want_domain = list
            .domain(bytes)
            .map(|s| String::from_utf8_lossy(s.as_bytes()).into_owned());
        let got_suffix = text(public_suffix_of_domain_exec(&to_u32(d)));
        let got_domain = text(registrable_domain_of_domain_exec(&to_u32(d)));
        if got_suffix == want_suffix && got_domain == want_domain {
            pass += 1;
        } else {
            failures.push(format!(
                "{d}: suffix {got_suffix:?} vs {want_suffix:?}; domain {got_domain:?} vs {want_domain:?}"
            ));
        }
    }
    println!(
        "clazel-conformance: suite=\"differential vs publicsuffix 2.3.0\" pass={pass} xfail=0 fail={} total={total}",
        failures.len()
    );
    assert!(
        failures.is_empty(),
        "{} differences, first: {:#?}",
        failures.len(),
        failures.iter().take(15).collect::<Vec<_>>()
    );
}
