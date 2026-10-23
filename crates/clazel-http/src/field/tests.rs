//! Unit tests for every executable function. The proofs say the code meets
//! the spec; these run it (and Miri runs them), on the RFC's examples and
//! on the inputs where a loop or an index could go wrong.

use super::content_length::{parse_content_length, parse_content_length_lines};
use super::contract::ContentLengthError;
use super::list::{list_elements, split_values};
use super::params::{parse_connection, parse_parameters, parse_transfer_encoding};
use super::quoted::{parse_quoted_string, quote};
use super::section::{combine, combined_field_value, field_values_named, set_cookie_lines};
use super::spec::{Class, ParameterGrammar};
use super::string::{
    all_in_exec, append, at, copy, field_name_eq, in_class_exec, is_bws, is_field_name,
    is_field_value, is_ows, is_rws, is_tchar_exec, is_token, run_len_exec, slice_eq, strip_ows,
};
use super::types::{FieldLineBuf, ParameterBuf, TransferCodingBuf};

fn v(s: &[u8]) -> Vec<u8> {
    s.to_vec()
}

fn vs(items: &[&[u8]]) -> Vec<Vec<u8>> {
    items.iter().map(|i| i.to_vec()).collect()
}

fn line(name: &[u8], value: &[u8]) -> FieldLineBuf {
    FieldLineBuf {
        name: v(name),
        value: v(value),
    }
}

type Pairs = Vec<(Vec<u8>, Vec<u8>)>;

fn params(p: Vec<ParameterBuf>) -> Pairs {
    p.into_iter().map(|p| (p.name, p.value)).collect()
}

fn pairs(items: &[(&[u8], &[u8])]) -> Pairs {
    items
        .iter()
        .map(|(a, b)| (a.to_vec(), b.to_vec()))
        .collect()
}

fn codings(c: Vec<TransferCodingBuf>) -> Vec<(Vec<u8>, Pairs)> {
    c.into_iter()
        .map(|c| (c.name, params(c.parameters)))
        .collect()
}

#[test]
fn helpers() {
    assert_eq!(copy(b"abc"), b"abc");
    let mut out = v(b"ab");
    append(&mut out, b"cd");
    assert_eq!(out, b"abcd");
    assert_eq!(at(b"ab", 1), Some(b'b'));
    assert_eq!(at(b"ab", 2), None);
    assert!(slice_eq(b"ab", b"ab"));
    assert!(!slice_eq(b"ab", b"ac"));
    assert!(!slice_eq(b"ab", b"a"));
    assert!(is_tchar_exec(b'~') && !is_tchar_exec(b'"') && !is_tchar_exec(0x80));
    assert!(in_class_exec(&Class::Digit, b'7') && !in_class_exec(&Class::Digit, b'a'));
    assert!(in_class_exec(&Class::Ows, b'\t') && !in_class_exec(&Class::Ows, b'\n'));
    assert!(
        in_class_exec(&Class::FieldContent, 0xFF) && !in_class_exec(&Class::FieldContent, 0x7F)
    );
    assert!(in_class_exec(&Class::QuotedPair, b'\t') && !in_class_exec(&Class::QuotedPair, 0));
    assert_eq!(run_len_exec(&Class::Tchar, b"ab cd"), 2);
    assert_eq!(run_len_exec(&Class::Tchar, b""), 0);
    assert_eq!(run_len_exec(&Class::Tchar, b"abc"), 3);
    assert!(all_in_exec(b"123", &Class::Digit) && !all_in_exec(b"12a", &Class::Digit));
    assert!(all_in_exec(b"", &Class::Digit));
}

#[test]
fn tokens_and_names() {
    assert!(is_token(b"Content-Length"));
    assert!(is_token(b"!#$%&'*+-.^_`|~09azAZ"));
    assert!(!is_token(b""));
    for d in b"\"(),/:;<=>?@[\\]{}" {
        assert!(!is_token(&[b'a', *d, b'b']));
    }
    assert!(!is_token(b"a b") && !is_token(b"a\x7f") && !is_token(b"\x80"));
    assert!(is_field_name(b"Host") && !is_field_name(b"Ho st") && !is_field_name(b""));
    assert!(field_name_eq(b"Content-Length", b"CONTENT-length"));
    assert!(!field_name_eq(b"@", b"`") && !field_name_eq(b"[", b"{"));
    assert!(!field_name_eq(b"a", b"ab") && !field_name_eq(b"ab", b"ac"));
    assert!(field_name_eq(b"", b""));
}

#[test]
fn whitespace_and_values() {
    assert!(is_ows(b"") && is_ows(b" \t") && !is_ows(b" x"));
    assert!(is_rws(b" ") && !is_rws(b"") && !is_rws(b"\n"));
    assert!(is_bws(b"") && is_bws(b"\t") && !is_bws(b"\x0b"));
    assert_eq!(strip_ows(b"  \t a b \t "), b"a b");
    assert_eq!(strip_ows(b""), b"");
    assert_eq!(strip_ows(b" \t "), b"");
    assert_eq!(strip_ows(b"\ra\n"), b"\ra\n");
    assert!(is_field_value(b"") && is_field_value(b"a b\tc") && is_field_value(b"\x80\xff"));
    assert!(!is_field_value(b" a") && !is_field_value(b"a ") && !is_field_value(b" "));
    assert!(!is_field_value(b"a\nb") && !is_field_value(b"a\0") && !is_field_value(b"a\x7fb"));
    assert!(is_field_value(b"a"));
}

#[test]
fn sections() {
    let section = vec![
        line(b"Example-Field", b"Foo, Bar"),
        line(b"Other", b"x"),
        line(b"example-FIELD", b"Baz"),
        line(b"Set-Cookie", b"a=b"),
        line(b"set-cookie", b"c=d"),
    ];
    assert_eq!(
        field_values_named(&section, b"EXAMPLE-FIELD"),
        vs(&[b"Foo, Bar", b"Baz"])
    );
    assert_eq!(
        field_values_named(&section, b"missing"),
        Vec::<Vec<u8>>::new()
    );
    assert_eq!(field_values_named(&[], b"a"), Vec::<Vec<u8>>::new());
    assert_eq!(combine(&vs(&[b"Foo, Bar", b"Baz"])), b"Foo, Bar, Baz");
    assert_eq!(combine(&vs(&[b"a"])), b"a");
    assert_eq!(combine(&[]), b"");
    assert_eq!(combine(&vs(&[b"", b"b"])), b", b");
    assert_eq!(
        combined_field_value(&section, b"example-field"),
        Some(v(b"Foo, Bar, Baz"))
    );
    assert_eq!(combined_field_value(&section, b"missing"), None);
    assert_eq!(combined_field_value(&section, b"Set-Cookie"), None);
    assert_eq!(combined_field_value(&section, b"SET-COOKIE"), None);
    assert_eq!(set_cookie_lines(&section), vs(&[b"a=b", b"c=d"]));
    assert_eq!(
        set_cookie_lines(section.get(..3).unwrap_or_default()),
        Vec::<Vec<u8>>::new()
    );
}

#[test]
fn lists() {
    assert_eq!(list_elements(b"foo,bar"), vs(&[b"foo", b"bar"]));
    assert_eq!(list_elements(b"foo ,bar,"), vs(&[b"foo", b"bar"]));
    assert_eq!(
        list_elements(b"foo , ,bar,charlie"),
        vs(&[b"foo", b"bar", b"charlie"])
    );
    for empty in [&b""[..], b",", b",   ,"] {
        assert!(list_elements(empty).is_empty());
    }
    assert_eq!(
        list_elements(
            b"\"http://example.com/a.html,foo\", \"http://without-a-comma.example.com/\""
        ),
        vs(&[
            b"\"http://example.com/a.html,foo\"",
            b"\"http://without-a-comma.example.com/\""
        ])
    );
    assert_eq!(
        list_elements(b"\"Sat, 04 May 1996\", \"Wed, 14 Sep 2005\""),
        vs(&[b"\"Sat, 04 May 1996\"", b"\"Wed, 14 Sep 2005\""])
    );
    assert_eq!(
        list_elements(b"\"a\\\",b\", c"),
        vs(&[b"\"a\\\",b\"", b"c"])
    );
    assert_eq!(list_elements(b"\"a,b"), vs(&[b"\"a,b"]));
    assert_eq!(list_elements(b"\"a\\"), vs(&[b"\"a\\"]));
    assert_eq!(list_elements(b"x\"a,b\"y, z"), vs(&[b"x\"a,b\"y", b"z"]));
    assert_eq!(split_values(b"a,,b"), vs(&[b"a", b"", b"b"]));
    assert_eq!(split_values(b""), vs(&[b""]));
    assert_eq!(split_values(b" , "), vs(&[b"", b""]));
    assert_eq!(split_values(b"a, b ,c"), vs(&[b"a", b"b", b"c"]));
}

#[test]
fn quoted_strings() {
    assert_eq!(parse_quoted_string(b"\"abc\""), Some((v(b"abc"), 5)));
    assert_eq!(parse_quoted_string(b"\"\""), Some((v(b""), 2)));
    assert_eq!(parse_quoted_string(b"\"a\\\"b\" x"), Some((v(b"a\"b"), 6)));
    assert_eq!(parse_quoted_string(b"\"a\\\\b\""), Some((v(b"a\\b"), 6)));
    assert_eq!(parse_quoted_string(b"\"\\a\""), Some((v(b"a"), 4)));
    assert_eq!(parse_quoted_string(b"\"\\\x80\""), Some((v(b"\x80"), 4)));
    assert_eq!(
        parse_quoted_string(b"\"a\tb \x80~\""),
        Some((v(b"a\tb \x80~"), 8))
    );
    assert_eq!(parse_quoted_string(b"\"a\",\"b\""), Some((v(b"a"), 3)));
    for bad in [
        &b"\"abc"[..],
        b"abc\"",
        b"",
        b"\"",
        b"\"\\",
        b"\"\\\"",
        b"\"a\\\0\"",
        b"\"a\\\n\"",
        b"\"a\x01\"",
        b"\"a\nb\"",
        b"\"a\x7f\"",
    ] {
        assert_eq!(parse_quoted_string(bad), None);
    }
    assert_eq!(quote(b"a\"b\\"), Some(v(b"\"a\\\"b\\\\\"")));
    assert_eq!(quote(b""), Some(v(b"\"\"")));
    assert_eq!(quote(b"a b\t\x80"), Some(v(b"\"a b\t\x80\"")));
    assert_eq!(quote(b"a\r\nb"), None);
    assert_eq!(quote(b"a\0"), None);
    assert_eq!(quote(b"\x7f"), None);
    // What quote writes, parse_quoted_string reads back.
    let q = quote(b"x\"y\\z \t").unwrap_or_default();
    assert_eq!(parse_quoted_string(&q), Some((v(b"x\"y\\z \t"), q.len())));
}

#[test]
fn parameter_lists() {
    let p = &ParameterGrammar::Parameters;
    let t = &ParameterGrammar::TransferCoding;
    let ok = |input: &[u8], g: &ParameterGrammar| parse_parameters(input, g).map(params);
    assert_eq!(
        ok(b";charset=utf-8", p),
        Some(pairs(&[(b"charset", b"utf-8")]))
    );
    assert_eq!(
        ok(b"; charset=\"utf-8\"", p),
        Some(pairs(&[(b"charset", b"utf-8")]))
    );
    assert_eq!(ok(b"", p), Some(vec![]));
    assert_eq!(ok(b";", p), Some(vec![]));
    assert_eq!(ok(b"; ;", p), Some(vec![]));
    assert_eq!(ok(b";;a=b;;", p), Some(pairs(&[(b"a", b"b")])));
    assert_eq!(
        ok(b"; ; a=b ; ;c=d", p),
        Some(pairs(&[(b"a", b"b"), (b"c", b"d")]))
    );
    assert_eq!(
        ok(b";a=\"x y\";b=\"\"", p),
        Some(pairs(&[(b"a", b"x y"), (b"b", b"")]))
    );
    assert_eq!(ok(b";a=\"x;y=z\"", p), Some(pairs(&[(b"a", b"x;y=z")])));
    assert_eq!(ok(b"\t;\ta=b", p), Some(pairs(&[(b"a", b"b")])));
    for bad in [
        &b";a=b "[..],
        b";a",
        b";a=",
        b";a =b",
        b";a= b",
        b"a=b",
        b";=b",
        b";a=\"b",
        b";a=\"b\"c",
        b";a=b c",
        b";a=(b)",
        b";a=b;c",
    ] {
        assert_eq!(ok(bad, p), None);
    }
    assert_eq!(ok(b"; a = b", t), Some(pairs(&[(b"a", b"b")])));
    assert_eq!(ok(b";\ta\t=\t\"x y\"", t), Some(pairs(&[(b"a", b"x y")])));
    assert_eq!(
        ok(b";a=b ;c=d", t),
        Some(pairs(&[(b"a", b"b"), (b"c", b"d")]))
    );
    assert_eq!(ok(b"", t), Some(vec![]));
    for bad in [&b";"[..], b"; ;a=b", b";a", b";a=", b";a=b ", b";a = "] {
        assert_eq!(ok(bad, t), None);
    }
}

#[test]
fn transfer_encoding_and_connection() {
    let te = |input: &[u8]| parse_transfer_encoding(input).map(codings);
    assert_eq!(te(b"chunked"), Some(vec![(v(b"chunked"), vec![])]));
    assert_eq!(
        te(b"gzip, chunked"),
        Some(vec![(v(b"gzip"), vec![]), (v(b"chunked"), vec![])])
    );
    assert_eq!(
        te(b" gzip ,, chunked ,"),
        Some(vec![(v(b"gzip"), vec![]), (v(b"chunked"), vec![])])
    );
    assert_eq!(te(b""), Some(vec![]));
    assert_eq!(te(b","), Some(vec![]));
    assert_eq!(
        te(b"foo ; bar = \"a,b\" ; q=1, chunked"),
        Some(vec![
            (v(b"foo"), pairs(&[(b"bar", b"a,b"), (b"q", b"1")])),
            (v(b"chunked"), vec![])
        ])
    );
    for bad in [
        &b"gzip chunked"[..],
        b"gzip;",
        b"foo;bar",
        b"\"gzip\"",
        b"gzip, (x)",
        b"a/b",
    ] {
        assert_eq!(te(bad), None);
    }
    assert_eq!(parse_connection(b"close"), Some(vs(&[b"close"])));
    assert_eq!(
        parse_connection(b"keep-alive, Upgrade"),
        Some(vs(&[b"keep-alive", b"Upgrade"]))
    );
    assert_eq!(parse_connection(b",, close ,"), Some(vs(&[b"close"])));
    assert_eq!(parse_connection(b""), Some(vec![]));
    for bad in [&b"a b"[..], b"a;b", b"\"a\"", b"a, b c", b"a, \x80"] {
        assert_eq!(parse_connection(bad), None);
    }
}

#[test]
fn content_length() {
    let ok = |n: u64| Ok(n);
    assert_eq!(parse_content_length(b"3495"), ok(3495));
    assert_eq!(parse_content_length(b"0"), ok(0));
    assert_eq!(parse_content_length(b"0042"), ok(42));
    assert_eq!(parse_content_length(b"42, 42"), ok(42));
    assert_eq!(parse_content_length(b"42,42"), ok(42));
    assert_eq!(parse_content_length(b" 7 , 7 , 7 "), ok(7));
    assert_eq!(parse_content_length(b"18446744073709551615"), ok(u64::MAX));
    assert_eq!(
        parse_content_length(b"18446744073709551616"),
        Err(ContentLengthError::TooLarge)
    );
    assert_eq!(
        parse_content_length(b"99999999999999999999999999"),
        Err(ContentLengthError::TooLarge)
    );
    assert_eq!(
        parse_content_length(b"00000000000000000000000000000001"),
        ok(1)
    );
    for bad in [
        &b""[..],
        b" ",
        b"+1",
        b"-1",
        b"1.5",
        b"1 2",
        b"0x10",
        b"1e3",
        b"42, 43",
        b"42, 042",
        b"42,,42",
        b",42",
        b"42,",
        b"42, ",
        b"\"42\"",
    ] {
        assert_eq!(parse_content_length(bad), Err(ContentLengthError::Invalid));
    }
    assert_eq!(parse_content_length_lines(&vs(&[b"42", b"42"])), ok(42));
    assert_eq!(parse_content_length_lines(&vs(&[b"42, 42", b"42"])), ok(42));
    assert_eq!(parse_content_length_lines(&vs(&[b"5"])), ok(5));
    assert_eq!(
        parse_content_length_lines(&vs(&[b"1", b"2"])),
        Err(ContentLengthError::Invalid)
    );
    assert_eq!(
        parse_content_length_lines(&vs(&[b"1", b""])),
        Err(ContentLengthError::Invalid)
    );
    assert_eq!(
        parse_content_length_lines(&[]),
        Err(ContentLengthError::Invalid)
    );
}

/// The example in README.md.
#[test]
fn readme_example() {
    assert_eq!(
        list_elements(b"foo , ,\"a,b\",bar,"),
        vec![b"foo".to_vec(), b"\"a,b\"".to_vec(), b"bar".to_vec()]
    );
    assert_eq!(
        parse_quoted_string(b"\"a\\\"b\" rest"),
        Some((b"a\"b".to_vec(), 6))
    );
    assert_eq!(parse_content_length(b"42, 42"), Ok(42));
    assert!(parse_content_length(b"42, 43").is_err());
    let codings = parse_transfer_encoding(b"gzip, chunked").unwrap_or_default();
    assert_eq!(codings.len(), 2);
}
