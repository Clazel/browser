//! Facts proven about the spec itself. They are evidence that the
//! transcription is right (docs/SPEC-STYLE.md), not part of what the
//! implementation must meet.
//!
//! What the RFC states, proven:
//! - [`lemma_tchar_is_vchar_except_delimiters`]: §5.6.2's comment on
//!   `tchar`, "any VCHAR, except delimiters", and [`lemma_token_no_delimiter`]:
//!   a token contains no delimiter.
//! - [`lemma_unquote_quote`], [`lemma_quote_unquote`]: unquoting what
//!   [`quote`] wrote gives the value back (for every value a quoted string
//!   can carry), and quoting what a canonical quoted string unquotes to
//!   gives the quoted string back (canonical: its only quoted-pairs are the
//!   ones §5.6.4 says a sender uses, for DQUOTE and backslash).
//! - [`lemma_combined_splits_back`]: a combined value splits back into
//!   its field lines when none contains a comma (or a DQUOTE, which would
//!   start a quoted string that swallows the commas after it; see the
//!   lemma) and each is a non-empty field value (§5.5).
//! - [`lemma_content_length_repeated`]: `Content-Length` with repeated
//!   identical values (§8.6) equals the single value.
//! - [`lemma_set_cookie_not_combined`]: §5.3's note.
//!
//! The RFC's own examples are evaluated in [`super::examples`]; the
//! index forms of the recursive definitions, which the executable loops
//! use, come first below.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ===========================================================================
// Index forms of the recursive definitions.
// ===========================================================================

/// `all_in` says every octet is in the class.
pub proof fn lemma_all_in_index(s: Seq<u8>, class: Class)
    ensures
        all_in(s, class) <==> (forall|i: int| 0 <= i < s.len() ==> in_class(class, #[trigger] s[i])),
    decreases s.len()
{
    if s.len() > 0 {
        lemma_all_in_index(s.drop_first(), class);
        if all_in(s, class) {
            assert forall|i: int| 0 <= i < s.len() implies in_class(class, #[trigger] s[i]) by {
                if i > 0 {
                    assert(s.drop_first()[i - 1] == s[i]);
                }
            }
        }
        if forall|i: int| 0 <= i < s.len() ==> in_class(class, #[trigger] s[i]) {
            assert forall|j: int| 0 <= j < s.drop_first().len() implies in_class(class, #[trigger] s.drop_first()[j]) by {
                assert(s.drop_first()[j] == s[j + 1]);
            }
        }
    }
}

/// What `run_len` measures: the longest prefix whose octets are all in the
/// class.
pub proof fn lemma_run_len_props(class: Class, s: Seq<u8>)
    ensures
        run_len(class, s) <= s.len(),
        forall|j: int| 0 <= j < run_len(class, s) ==> in_class(class, #[trigger] s[j]),
        run_len(class, s) < s.len() ==> !in_class(class, s[run_len(class, s) as int]),
    decreases s.len()
{
    if s.len() > 0 && in_class(class, s[0]) {
        lemma_run_len_props(class, s.drop_first());
        let n = run_len(class, s.drop_first());
        assert forall|j: int| 0 <= j < run_len(class, s) implies in_class(class, #[trigger] s[j]) by {
            if j > 0 {
                assert(s.drop_first()[j - 1] == s[j]);
            }
        }
        if run_len(class, s) < s.len() {
            assert(s.drop_first()[n as int] == s[(n + 1) as int]);
        }
    }
}

/// Joining one more value: the first has nothing before it, the others
/// come after ", ".
pub proof fn lemma_combine_push(values: Seq<Seq<u8>>, v: Seq<u8>)
    ensures
        combine(values.push(v)) == if values.len() == 0 { v } else { combine(values) + seq![0x2Cu8, 0x20u8] + v },
    decreases values.len()
{
    let pushed = values.push(v);
    if values.len() >= 2 {
        lemma_combine_push(values.drop_first(), v);
        assert(pushed.drop_first() =~= values.drop_first().push(v));
        assert(pushed[0] == values[0]);
        assert(combine(pushed) =~= combine(values) + seq![0x2Cu8, 0x20u8] + v);
    } else if values.len() == 1 {
        assert(pushed.drop_first() =~= seq![v]);
        assert(combine(seq![v]) == v);
        assert(combine(values) == values[0]);
    } else {
        assert(pushed =~= seq![v]);
    }
}

/// Dropping empty members commutes with appending one.
pub proof fn lemma_drop_empty_push(v: Seq<Seq<u8>>, e: Seq<u8>)
    ensures
        drop_empty(v.push(e)) == drop_empty(v) + (if e.len() == 0 { seq![] } else { seq![e] }),
    decreases v.len()
{
    let pushed = v.push(e);
    if v.len() == 0 {
        assert(pushed =~= seq![e]);
        assert(pushed.drop_first() =~= Seq::<Seq<u8>>::empty());
        assert(v =~= Seq::<Seq<u8>>::empty());
    } else {
        lemma_drop_empty_push(v.drop_first(), e);
        assert(pushed.drop_first() =~= v.drop_first().push(e));
        assert(pushed[0] == v[0]);
        assert(drop_empty(pushed) =~= drop_empty(v) + (if e.len() == 0 { seq![] } else { seq![e] }));
    }
}

/// Quoting one more octet.
pub proof fn lemma_quote_octets_push(v: Seq<u8>, c: u8)
    ensures
        quote_octets(v.push(c)) == quote_octets(v) + (if c == 0x22 || c == 0x5C { seq![0x5Cu8, c] } else { seq![c] }),
    decreases v.len()
{
    let pushed = v.push(c);
    if v.len() == 0 {
        assert(pushed =~= seq![c]);
        assert(pushed.drop_first() =~= Seq::<u8>::empty());
        assert(v =~= Seq::<u8>::empty());
    } else {
        lemma_quote_octets_push(v.drop_first(), c);
        assert(pushed.drop_first() =~= v.drop_first().push(c));
        assert(pushed[0] == v[0]);
        assert(quote_octets(pushed) =~= quote_octets(v) + (if c == 0x22 || c == 0x5C { seq![0x5Cu8, c] } else { seq![c] }));
    }
}

/// `all_tokens` says every member is a token.
pub proof fn lemma_all_tokens_index(v: Seq<Seq<u8>>)
    ensures
        all_tokens(v) <==> (forall|i: int| 0 <= i < v.len() ==> is_token(#[trigger] v[i])),
    decreases v.len()
{
    if v.len() > 0 {
        lemma_all_tokens_index(v.drop_first());
        if all_tokens(v) {
            assert forall|i: int| 0 <= i < v.len() implies is_token(#[trigger] v[i]) by {
                if i > 0 {
                    assert(v.drop_first()[i - 1] == v[i]);
                }
            }
        }
        if forall|i: int| 0 <= i < v.len() ==> is_token(#[trigger] v[i]) {
            assert forall|j: int| 0 <= j < v.drop_first().len() implies is_token(#[trigger] v.drop_first()[j]) by {
                assert(v.drop_first()[j] == v[j + 1]);
            }
        }
    }
}

/// `all_equal` says every member is `e`.
pub proof fn lemma_all_equal_index(v: Seq<Seq<u8>>, e: Seq<u8>)
    ensures
        all_equal(v, e) <==> (forall|i: int| 0 <= i < v.len() ==> (#[trigger] v[i]) == e),
    decreases v.len()
{
    if v.len() > 0 {
        lemma_all_equal_index(v.drop_first(), e);
        if all_equal(v, e) {
            assert forall|i: int| 0 <= i < v.len() implies (#[trigger] v[i]) == e by {
                if i > 0 {
                    assert(v.drop_first()[i - 1] == v[i]);
                }
            }
        }
        if forall|i: int| 0 <= i < v.len() ==> (#[trigger] v[i]) == e {
            assert forall|j: int| 0 <= j < v.drop_first().len() implies (#[trigger] v.drop_first()[j]) == e by {
                assert(v.drop_first()[j] == v[j + 1]);
            }
        }
    }
}

/// Reading one more transfer coding.
pub proof fn lemma_codings_push(elements: Seq<Seq<u8>>, e: Seq<u8>)
    ensures
        parse_transfer_codings(elements.push(e)) == match (parse_transfer_codings(elements), parse_transfer_coding(e)) {
            (Some(a), Some(c)) => Some(a.push(c)),
            _ => None,
        },
    decreases elements.len()
{
    let pushed = elements.push(e);
    if elements.len() == 0 {
        assert(pushed =~= seq![e]);
        assert(pushed.drop_first() =~= Seq::<Seq<u8>>::empty());
        assert(elements =~= Seq::<Seq<u8>>::empty());
        if parse_transfer_coding(e) is Some {
            assert(seq![parse_transfer_coding(e)->Some_0] + Seq::<TransferCoding>::empty() =~= seq![parse_transfer_coding(e)->Some_0]);
        }
    } else {
        lemma_codings_push(elements.drop_first(), e);
        assert(pushed.drop_first() =~= elements.drop_first().push(e));
        assert(pushed[0] == elements[0]);
        if let (Some(first), Some(a), Some(c)) = (
            parse_transfer_coding(elements[0]),
            parse_transfer_codings(elements.drop_first()),
            parse_transfer_coding(e),
        ) {
            assert(seq![first] + a.push(c) =~= (seq![first] + a).push(c));
        }
    }
}

/// Reading one more digit.
pub proof fn lemma_decimal_value_push(s: Seq<u8>, c: u8)
    ensures
        decimal_value(s.push(c)) == decimal_value(s) * 10 + ((c - 0x30) as nat),
{
    assert(s.push(c).drop_last() =~= s);
    assert(s.push(c).last() == c);
}

/// A string is all in the class exactly when its run is all of it.
pub proof fn lemma_all_in_run_len(s: Seq<u8>, class: Class)
    ensures
        all_in(s, class) <==> run_len(class, s) == s.len(),
    decreases s.len()
{
    if s.len() > 0 && in_class(class, s[0]) {
        lemma_all_in_run_len(s.drop_first(), class);
    }
}


// ===========================================================================
// Tokens.
// ===========================================================================

/// §5.6.2: "tchar ... any VCHAR, except delimiters".
pub proof fn lemma_tchar_is_vchar_except_delimiters(c: u8)
    ensures
        is_tchar(c) <==> (is_vchar(c) && !is_delimiter(c)),
{
}

/// A token contains no delimiter (§5.6.2: "Tokens are short textual
/// identifiers that do not include whitespace or delimiters").
pub proof fn lemma_token_no_delimiter(s: Seq<u8>)
    requires
        is_token(s),
    ensures
        forall|i: int| 0 <= i < s.len() ==> !is_delimiter(#[trigger] s[i]) && !is_ows_octet(s[i]),
{
    lemma_all_in_index(s, Class::Tchar);
    assert forall|i: int| 0 <= i < s.len() implies !is_delimiter(#[trigger] s[i]) && !is_ows_octet(s[i]) by {
        assert(is_tchar(s[i]));
    }
}

// ===========================================================================
// Quoted strings.
// ===========================================================================

/// Reading what [`quote_octets`] wrote, closed by a DQUOTE, gives the
/// octets back.
pub proof fn lemma_quoted_body_of_quote(v: Seq<u8>, value: Seq<u8>)
    requires
        is_quotable(v),
    ensures
        quoted_body(quote_octets(v) + seq![0x22u8], value) == Some((value + v, Seq::<u8>::empty())),
    decreases v.len()
{
    lemma_all_in_index(v, Class::QuotedPair);
    let input = quote_octets(v) + seq![0x22u8];
    if v.len() == 0 {
        assert(quote_octets(v) =~= Seq::<u8>::empty());
        assert(input =~= seq![0x22u8]);
        assert(input.drop_first() =~= Seq::<u8>::empty());
        assert(value + v =~= value);
    } else {
        let c = v[0];
        let rest = v.drop_first();
        assert(is_quoted_pair_octet(c));
        assert(is_quotable(rest)) by {
            assert forall|i: int| 0 <= i < rest.len() implies in_class(Class::QuotedPair, #[trigger] rest[i]) by {
                assert(rest[i] == v[i + 1]);
            }
            lemma_all_in_index(rest, Class::QuotedPair);
        }
        if c == 0x22 || c == 0x5C {
            assert(quote_octets(v) =~= seq![0x5Cu8, c] + quote_octets(rest));
            assert(input =~= seq![0x5Cu8, c] + (quote_octets(rest) + seq![0x22u8]));
            assert(input.drop_first().drop_first() =~= quote_octets(rest) + seq![0x22u8]);
            lemma_quoted_body_of_quote(rest, value.push(c));
            assert(value.push(c) + rest =~= value + v);
        } else {
            assert(quote_octets(v) =~= seq![c] + quote_octets(rest));
            assert(input =~= seq![c] + (quote_octets(rest) + seq![0x22u8]));
            assert(input.drop_first() =~= quote_octets(rest) + seq![0x22u8]);
            assert(is_qdtext(c));
            lemma_quoted_body_of_quote(rest, value.push(c));
            assert(value.push(c) + rest =~= value + v);
        }
    }
}

/// Unquoting what [`quote`] wrote gives the value back, on every value a
/// quoted string can carry, and nothing is left over.
pub proof fn lemma_unquote_quote(v: Seq<u8>)
    requires
        is_quotable(v),
    ensures
        parse_quoted_string(quote(v)) == Some((v, Seq::<u8>::empty())),
{
    lemma_quoted_body_of_quote(v, Seq::<u8>::empty());
    let q = quote(v);
    assert(q.drop_first() =~= quote_octets(v) + seq![0x22u8]);
    assert(Seq::<u8>::empty() + v =~= v);
}

/// A quoted-string body is canonical when its only quoted-pairs are for
/// DQUOTE and backslash (§5.6.4: "A sender SHOULD NOT generate a
/// quoted-pair in a quoted-string except where necessary to quote DQUOTE
/// and backslash octets"), read as far as its closing DQUOTE.
pub open spec fn canonical_body(body: Seq<u8>) -> bool
    decreases body.len()
{
    if body.len() == 0 {
        false
    } else if body[0] == 0x22 {
        true
    } else if body[0] == 0x5C {
        body.len() >= 2 && (body[1] == 0x22 || body[1] == 0x5C) && canonical_body(body.drop_first().drop_first())
    } else {
        canonical_body(body.drop_first())
    }
}

/// Reading a canonical body: what was read, quoted again, with the
/// closing DQUOTE and what follows, is the body.
pub proof fn lemma_quoted_body_canonical(body: Seq<u8>, value: Seq<u8>, v: Seq<u8>, rest: Seq<u8>)
    requires
        quoted_body(body, value) == Some((v, rest)),
        canonical_body(body),
    ensures
        v.len() >= value.len(),
        v.take(value.len() as int) == value,
        body == quote_octets(v.skip(value.len() as int)) + seq![0x22u8] + rest,
    decreases body.len()
{
    if body[0] == 0x22 {
        assert(v == value);
        assert(v.skip(value.len() as int) =~= Seq::<u8>::empty());
        assert(quote_octets(Seq::<u8>::empty()) =~= Seq::<u8>::empty());
        assert(body =~= seq![0x22u8] + rest);
        assert(v.take(value.len() as int) =~= value);
    } else if body[0] == 0x5C {
        let c = body[1];
        let next = body.drop_first().drop_first();
        let value2 = value.push(c);
        lemma_quoted_body_canonical(next, value2, v, rest);
        let t = v.skip(value2.len() as int);
        assert(v.take(value.len() as int) =~= value) by {
            assert(v.take(value2.len() as int) == value2);
            assert(v.take(value.len() as int) =~= v.take(value2.len() as int).take(value.len() as int));
            assert(value2.take(value.len() as int) =~= value);
        }
        assert(v.skip(value.len() as int) =~= seq![c] + t) by {
            assert(v.take(value2.len() as int)[value.len() as int] == value2[value.len() as int]);
            assert(v[value.len() as int] == v.take(value2.len() as int)[value.len() as int]);
            assert(value2[value.len() as int] == c);
        }
        assert(quote_octets(seq![c] + t) =~= seq![0x5Cu8, c] + quote_octets(t)) by {
            assert((seq![c] + t)[0] == c);
            assert((seq![c] + t).drop_first() =~= t);
        }
        assert(body =~= seq![0x5Cu8, c] + next);
        assert(body =~= quote_octets(v.skip(value.len() as int)) + seq![0x22u8] + rest);
    } else {
        let c = body[0];
        let next = body.drop_first();
        let value2 = value.push(c);
        assert(is_qdtext(c));
        lemma_quoted_body_canonical(next, value2, v, rest);
        let t = v.skip(value2.len() as int);
        assert(v.take(value.len() as int) =~= value) by {
            assert(v.take(value2.len() as int) == value2);
            assert(v.take(value.len() as int) =~= v.take(value2.len() as int).take(value.len() as int));
            assert(value2.take(value.len() as int) =~= value);
        }
        assert(v.skip(value.len() as int) =~= seq![c] + t) by {
            assert(v.take(value2.len() as int)[value.len() as int] == value2[value.len() as int]);
            assert(v[value.len() as int] == v.take(value2.len() as int)[value.len() as int]);
            assert(value2[value.len() as int] == c);
        }
        assert(quote_octets(seq![c] + t) =~= seq![c] + quote_octets(t)) by {
            assert((seq![c] + t)[0] == c);
            assert((seq![c] + t).drop_first() =~= t);
        }
        assert(body =~= seq![c] + next);
        assert(body =~= quote_octets(v.skip(value.len() as int)) + seq![0x22u8] + rest);
    }
}

/// Quoting what a canonical quoted string unquotes to gives the quoted
/// string back: if `input` starts with a quoted string whose body is
/// canonical, and it unquotes to `v` with `rest` after it, then `input` is
/// `quote(v)` followed by `rest`. (A quoted string with a needless
/// quoted-pair, such as `"\a"`, unquotes to the same value as `"a"`, so
/// the round trip cannot hold for it: that is the one class left out.)
pub proof fn lemma_quote_unquote(input: Seq<u8>, v: Seq<u8>, rest: Seq<u8>)
    requires
        parse_quoted_string(input) == Some((v, rest)),
        canonical_body(input.drop_first()),
    ensures
        input == quote(v) + rest,
{
    lemma_quoted_body_canonical(input.drop_first(), Seq::<u8>::empty(), v, rest);
    assert(v.skip(0) =~= v);
    assert(input =~= seq![0x22u8] + input.drop_first());
    assert(input =~= quote(v) + rest);
}

// ===========================================================================
// Lists, and combined field values.
// ===========================================================================

/// No octet of `s` is a comma or a DQUOTE.
pub open spec fn no_comma_or_quote(s: Seq<u8>) -> bool {
    forall|i: int| 0 <= i < s.len() ==> (#[trigger] s[i]) != 0x2C && s[i] != 0x22
}

/// The splitter passes over octets that are neither a comma nor a DQUOTE,
/// outside a quoted string, by adding them to the current piece.
pub proof fn lemma_scan_plain_run(seg: Seq<u8>, rest: Seq<u8>, cur: Seq<u8>, acc: Seq<Seq<u8>>)
    requires
        no_comma_or_quote(seg),
    ensures
        split_scan(seg + rest, QState::Plain, cur, acc) == split_scan(rest, QState::Plain, cur + seg, acc),
    decreases seg.len()
{
    if seg.len() > 0 {
        let c = seg[0];
        assert((seg + rest)[0] == c);
        assert((seg + rest).drop_first() =~= seg.drop_first() + rest);
        assert(no_comma_or_quote(seg.drop_first())) by {
            assert forall|i: int| 0 <= i < seg.drop_first().len() implies (#[trigger] seg.drop_first()[i]) != 0x2C
                && seg.drop_first()[i] != 0x22 by {
                assert(seg.drop_first()[i] == seg[i + 1]);
            }
        }
        lemma_scan_plain_run(seg.drop_first(), rest, cur.push(c), acc);
        assert(cur.push(c) + seg.drop_first() =~= cur + seg);
    } else {
        assert(seg + rest =~= rest);
        assert(cur + seg =~= cur);
    }
}

/// Removing OWS from a string that starts with SP is the same as from the
/// rest.
pub proof fn lemma_strip_ows_leading_sp(s: Seq<u8>)
    ensures
        strip_ows(seq![0x20u8] + s) == strip_ows(s),
{
    let t = seq![0x20u8] + s;
    assert(t[0] == 0x20u8);
    assert(t.drop_first() =~= s);
    assert(strip_leading_ows(t) =~= strip_leading_ows(s)) by {
        assert(run_len(Class::Ows, t) == 1 + run_len(Class::Ows, s));
        let n = run_len(Class::Ows, s);
        super::termination::lemma_run_len_le(Class::Ows, s);
        assert forall|k: int| 0 <= k < s.skip(n as int).len() implies t.skip((1 + n) as int)[k] == (#[trigger] s.skip(n as int))[k] by {
            assert(t[1 + n + k] == s[n + k]);
        }
        assert(t.skip((1 + n) as int) =~= s.skip(n as int));
    }
}

/// A string without OWS at its ends is unchanged by removing it.
pub proof fn lemma_strip_ows_of_trimmed(s: Seq<u8>)
    requires
        s.len() == 0 || (!is_ows_octet(s[0]) && !is_ows_octet(s.last())),
    ensures
        strip_ows(s) == s,
{
    if s.len() > 0 {
        assert(run_len(Class::Ows, s) == 0);
        assert(s.skip(0) =~= s);
        assert(strip_leading_ows(s) == s);
        assert(strip_trailing_ows(s) == s);
    } else {
        assert(strip_leading_ows(s) =~= s);
    }
}

/// Splitting the combination of lines none of which has a comma or a
/// DQUOTE, after a prefix `cur` of the first piece, gives the finished
/// pieces so far, the first line after `cur`, and the other lines, each
/// stripped of OWS.
pub proof fn lemma_combined_scan(lines: Seq<Seq<u8>>, cur: Seq<u8>, acc: Seq<Seq<u8>>)
    requires
        lines.len() >= 1,
        forall|i: int| 0 <= i < lines.len() ==> no_comma_or_quote(#[trigger] lines[i]),
    ensures
        split_scan(combine(lines), QState::Plain, cur, acc) == acc + seq![strip_ows(cur + lines[0])]
            + lines.drop_first().map_values(|l: Seq<u8>| strip_ows(l)),
    decreases lines.len()
{
    let first = lines[0];
    assert(no_comma_or_quote(first));
    if lines.len() == 1 {
        lemma_scan_plain_run(first, Seq::<u8>::empty(), cur, acc);
        assert(combine(lines) == first);
        assert(first + Seq::<u8>::empty() =~= first);
        assert(lines.drop_first() =~= Seq::<Seq<u8>>::empty());
        assert(lines.drop_first().map_values(|l: Seq<u8>| strip_ows(l)) =~= Seq::<Seq<u8>>::empty());
        assert(split_scan(Seq::<u8>::empty(), QState::Plain, cur + first, acc) == acc.push(strip_ows(cur + first)));
        assert(acc.push(strip_ows(cur + first)) =~= acc + seq![strip_ows(cur + first)]);
    } else {
        let rest = lines.drop_first();
        assert(forall|i: int| 0 <= i < rest.len() ==> no_comma_or_quote(#[trigger] rest[i])) by {
            assert forall|i: int| 0 <= i < rest.len() implies no_comma_or_quote(#[trigger] rest[i]) by {
                assert(rest[i] == lines[i + 1]);
            }
        }
        let tail = seq![0x2Cu8, 0x20u8] + combine(rest);
        assert(combine(lines) =~= first + tail);
        lemma_scan_plain_run(first, tail, cur, acc);
        // The comma ends the first piece; the space after it starts the next.
        let acc2 = acc.push(strip_ows(cur + first));
        assert(tail[0] == 0x2Cu8);
        assert(tail.drop_first() =~= seq![0x20u8] + combine(rest));
        assert(split_scan(tail, QState::Plain, cur + first, acc) == split_scan(seq![0x20u8] + combine(rest), QState::Plain, Seq::<u8>::empty(), acc2));
        let sp = seq![0x20u8] + combine(rest);
        assert(sp[0] == 0x20u8);
        assert(sp.drop_first() =~= combine(rest));
        assert(split_scan(sp, QState::Plain, Seq::<u8>::empty(), acc2) == split_scan(combine(rest), QState::Plain, seq![0x20u8], acc2));
        lemma_combined_scan(rest, seq![0x20u8], acc2);
        lemma_strip_ows_leading_sp(rest[0]);
        assert(acc2 + seq![strip_ows(seq![0x20u8] + rest[0])] + rest.drop_first().map_values(|l: Seq<u8>| strip_ows(l))
            =~= acc + seq![strip_ows(cur + first)] + lines.drop_first().map_values(|l: Seq<u8>| strip_ows(l))) by {
            assert(lines.drop_first().map_values(|l: Seq<u8>| strip_ows(l))
                =~= seq![strip_ows(rest[0])] + rest.drop_first().map_values(|l: Seq<u8>| strip_ows(l)));
        }
    }
}

/// Every non-empty member survives [`drop_empty`].
pub proof fn lemma_drop_empty_of_nonempty(v: Seq<Seq<u8>>)
    requires
        forall|i: int| 0 <= i < v.len() ==> (#[trigger] v[i]).len() > 0,
    ensures
        drop_empty(v) == v,
    decreases v.len()
{
    if v.len() > 0 {
        assert(forall|i: int| 0 <= i < v.drop_first().len() ==> (#[trigger] v.drop_first()[i]).len() > 0) by {
            assert forall|i: int| 0 <= i < v.drop_first().len() implies (#[trigger] v.drop_first()[i]).len() > 0 by {
                assert(v.drop_first()[i] == v[i + 1]);
            }
        }
        lemma_drop_empty_of_nonempty(v.drop_first());
        assert(v =~= seq![v[0]] + v.drop_first());
    }
}

/// A combined value splits back into its field lines when none contains
/// a comma: if every line is a non-empty field value (§5.5, so with no
/// leading or trailing whitespace) with no comma, then the elements of the
/// list that [`combine`] makes (§5.6.1.2) are the lines. A line may not
/// contain a DQUOTE either: it would open a quoted string that swallows
/// the commas combining puts after it (so `a"b` and `c` combine to `a"b,
/// c`, which is one element), and the lemma does not hold for such lines.
pub proof fn lemma_combined_splits_back(lines: Seq<Seq<u8>>)
    requires
        forall|i: int| 0 <= i < lines.len() ==> is_field_value(#[trigger] lines[i]) && lines[i].len() > 0
            && no_comma_or_quote(lines[i]),
    ensures
        list_elements(combine(lines)) == lines,
{
    if lines.len() == 0 {
        assert(combine(lines) =~= Seq::<u8>::empty());
        assert(strip_ows(Seq::<u8>::empty()) =~= Seq::<u8>::empty()) by {
            assert(strip_leading_ows(Seq::<u8>::empty()) =~= Seq::<u8>::empty());
        }
        assert(split_values(combine(lines)) =~= seq![Seq::<u8>::empty()]);
        let x = split_values(combine(lines));
        assert(x == seq![Seq::<u8>::empty()]);
        assert(x.drop_first() =~= Seq::<Seq<u8>>::empty());
        assert(drop_empty(Seq::<Seq<u8>>::empty()) == Seq::<Seq<u8>>::empty());
        assert(drop_empty(x) == Seq::<Seq<u8>>::empty());
        assert(lines =~= Seq::<Seq<u8>>::empty());
    } else {
        lemma_combined_scan(lines, Seq::<u8>::empty(), Seq::<Seq<u8>>::empty());
        assert(Seq::<u8>::empty() + lines[0] =~= lines[0]);
        let mapped = lines.map_values(|l: Seq<u8>| strip_ows(l));
        assert forall|i: int| 0 <= i < lines.len() implies strip_ows(#[trigger] lines[i]) == lines[i] by {
            let l = lines[i];
            assert(is_field_vchar(l[0]) && is_field_vchar(l.last()));
            lemma_strip_ows_of_trimmed(l);
        }
        assert(mapped =~= lines);
        assert(split_values(combine(lines)) =~= lines) by {
            assert(Seq::<Seq<u8>>::empty() + seq![strip_ows(lines[0])] + lines.drop_first().map_values(|l: Seq<u8>| strip_ows(l))
                =~= mapped);
        }
        lemma_drop_empty_of_nonempty(lines);
    }
}

// ===========================================================================
// Content-Length.
// ===========================================================================

/// `Content-Length` with repeated identical values equals the single
/// value (§8.6: "a Content-Length header field value consisting of the
/// same decimal value repeated as a comma-separated list ... replace that
/// invalid field value with a single instance of the decimal value"): `n`
/// field lines, all `digits`.
pub proof fn lemma_content_length_repeated(digits: Seq<u8>, n: nat)
    requires
        is_digits(digits),
        n >= 1,
    ensures
        parse_content_length_lines(Seq::new(n, |i: int| digits)) == Some(decimal_value(digits)),
{
    let lines = Seq::new(n, |i: int| digits);
    lemma_all_in_index(digits, Class::Digit);
    assert(no_comma_or_quote(digits)) by {
        assert forall|i: int| 0 <= i < digits.len() implies (#[trigger] digits[i]) != 0x2C && digits[i] != 0x22 by {
            assert(is_digit(digits[i]));
        }
    }
    assert forall|i: int| 0 <= i < lines.len() implies no_comma_or_quote(#[trigger] lines[i]) by {
        assert(lines[i] == digits);
    }
    lemma_combined_scan(lines, Seq::<u8>::empty(), Seq::<Seq<u8>>::empty());
    assert(Seq::<u8>::empty() + digits =~= digits);
    assert(is_digit(digits[0]) && is_digit(digits.last()));
    lemma_strip_ows_of_trimmed(digits);
    let mapped = lines.drop_first().map_values(|l: Seq<u8>| strip_ows(l));
    assert forall|i: int| 0 <= i < lines.len() - 1 implies (#[trigger] mapped[i]) == digits by {
        assert(lines.drop_first()[i] == lines[i + 1]);
    }
    let members = split_values(combine(lines));
    assert(members =~= lines) by {
        assert(members == Seq::<Seq<u8>>::empty() + seq![digits] + mapped);
        assert(members.len() == lines.len());
        assert forall|i: int| 0 <= i < members.len() implies members[i] == lines[i] by {
            if i > 0 {
                assert(members[i] == mapped[i - 1]);
            }
        }
    }
    lemma_all_equal_index(members, members[0]);
    assert(all_equal(members, members[0]));
    assert(parse_content_length(combine(lines)) == Some(decimal_value(digits)));
}

// ===========================================================================
// Set-Cookie.
// ===========================================================================

/// Names that are equal ignoring case select the same lines.
pub proof fn lemma_field_values_named_eq(section: Seq<FieldLine>, a: Seq<u8>, b: Seq<u8>)
    requires
        field_name_eq(a, b),
    ensures
        field_values_named(section, a) == field_values_named(section, b),
    decreases section.len()
{
    if section.len() > 0 {
        lemma_field_values_named_eq(section.drop_first(), a, b);
    }
}

/// `Set-Cookie` is never combined (§5.3's note), however it is written,
/// and its lines are still there one by one.
pub proof fn lemma_set_cookie_not_combined(section: Seq<FieldLine>, name: Seq<u8>)
    requires
        is_set_cookie(name),
    ensures
        combined_field_value(section, name) is None,
        field_values_named(section, name) == set_cookie_lines(section),
{
    // The two names are equal after lowercasing, so they select the same lines.
    lemma_field_values_named_eq(section, name, lit_set_cookie());
}

} // verus!
