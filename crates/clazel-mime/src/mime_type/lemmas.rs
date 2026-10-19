//! Facts proven about the MIME type spec in [`super::spec`]. Some are the
//! working facts the implementation's proof uses (the recursive
//! definitions restated with quantifiers); the rest are evidence that the
//! transcription behaves as the standard says.
//!
//! Main results:
//! - [`lemma_parse_form`]: every record parse a MIME type returns has a
//!   non-empty, lowercase HTTP token type and subtype, and parameters with
//!   distinct non-empty lowercase token names and values of HTTP
//!   quoted-string token code points ([`parsed_form`]). This is what §4.1
//!   requires of a record ("non-empty ASCII string", "values ... limited to
//!   HTTP quoted-string token code points"), and more.
//! - [`lemma_parse_serialize`]: for every record in that form, parsing its
//!   serialization gives an equal record. So
//!   [`lemma_parse_serialize_parse`]: whatever parsing returns survives a
//!   serialize-and-parse round trip unchanged. At the pinned commit the
//!   standard does not state this as a sentence; the nearest is §4.3's
//!   example (parsing "text/html;" gives a record identical to parsing
//!   "text/html"). `tests/conformance_mime_types.rs` also checks it on
//!   every WPT case.
//! - [`lemma_parse_serializable`]: serialize a MIME type to bytes is
//!   defined (isomorphic encode's assertion holds) on every parsed record.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ===========================================================================
// The recursive definitions, restated.
// ===========================================================================

/// "Solely contains HTTP token code points" is: every code point is one.
pub proof fn lemma_solely_token(s: Seq<u32>)
    ensures
        solely_http_token_code_points(s) <==> forall|k: int| 0 <= k < s.len() ==> is_http_token_code_point(#[trigger] s[k]),
    decreases s.len()
{
    if s.len() > 0 {
        let rest = s.drop_first();
        lemma_solely_token(rest);
        assert forall|k: int| 0 < k < s.len() implies s[k] == #[trigger] rest[k - 1] by {}
        if forall|k: int| 0 <= k < s.len() ==> is_http_token_code_point(#[trigger] s[k]) {
            assert(is_http_token_code_point(s[0]));
            assert forall|k: int| 0 <= k < rest.len() implies is_http_token_code_point(#[trigger] rest[k]) by {
                assert(rest[k] == s[k + 1]);
            }
        }
        if is_http_token_code_point(s[0]) && forall|k: int| 0 <= k < rest.len() ==> is_http_token_code_point(#[trigger] rest[k]) {
            assert forall|k: int| 0 <= k < s.len() implies is_http_token_code_point(#[trigger] s[k]) by {
                if k > 0 {
                    assert(s[k] == rest[k - 1]);
                }
            }
        }
    }
}

/// "Solely contains HTTP quoted-string token code points" is: every code
/// point is one.
pub proof fn lemma_solely_quoted_string_token(s: Seq<u32>)
    ensures
        solely_http_quoted_string_token_code_points(s) <==> forall|k: int| 0 <= k < s.len() ==> is_http_quoted_string_token_code_point(#[trigger] s[k]),
    decreases s.len()
{
    if s.len() > 0 {
        let rest = s.drop_first();
        lemma_solely_quoted_string_token(rest);
        assert forall|k: int| 0 < k < s.len() implies s[k] == #[trigger] rest[k - 1] by {}
        if forall|k: int| 0 <= k < s.len() ==> is_http_quoted_string_token_code_point(#[trigger] s[k]) {
            assert(is_http_quoted_string_token_code_point(s[0]));
            assert forall|k: int| 0 <= k < rest.len() implies is_http_quoted_string_token_code_point(#[trigger] rest[k]) by {
                assert(rest[k] == s[k + 1]);
            }
        }
        if is_http_quoted_string_token_code_point(s[0]) && forall|k: int| 0 <= k < rest.len() ==> is_http_quoted_string_token_code_point(#[trigger] rest[k]) {
            assert forall|k: int| 0 <= k < s.len() implies is_http_quoted_string_token_code_point(#[trigger] s[k]) by {
                if k > 0 {
                    assert(s[k] == rest[k - 1]);
                }
            }
        }
    }
}

/// "map[key] exists" is: some entry has that key.
pub proof fn lemma_map_exists(map: OrderedMap, key: Seq<u32>)
    ensures
        map_exists(map, key) <==> exists|i: int| 0 <= i < map.len() && (#[trigger] map[i]).0 == key,
    decreases map.len()
{
    if map.len() > 0 {
        let rest = map.drop_first();
        lemma_map_exists(rest, key);
        if exists|i: int| 0 <= i < map.len() && (#[trigger] map[i]).0 == key {
            let i = choose|i: int| 0 <= i < map.len() && (#[trigger] map[i]).0 == key;
            if i > 0 {
                assert(rest[i - 1] == map[i]);
            }
        }
        if exists|i: int| 0 <= i < rest.len() && (#[trigger] rest[i]).0 == key {
            let i = choose|i: int| 0 <= i < rest.len() && (#[trigger] rest[i]).0 == key;
            assert(map[i + 1] == rest[i]);
        }
    }
}

/// Setting a key that does not exist appends an entry.
pub proof fn lemma_map_set_new(map: OrderedMap, key: Seq<u32>, value: Seq<u32>)
    requires
        !map_exists(map, key),
    ensures
        map_set(map, key, value) == map.push((key, value)),
    decreases map.len()
{
    if map.len() > 0 {
        lemma_map_set_new(map.drop_first(), key, value);
        assert(seq![map[0]] + map.drop_first().push((key, value)) =~= map.push((key, value)));
    } else {
        assert(seq![(key, value)] =~= map.push((key, value)));
    }
}

/// `collect_loop` from `position` with `result` collected so far is
/// `result` followed by the run of code points meeting the condition.
pub proof fn lemma_collect_loop(condition: Condition, input: Seq<u32>, position: nat, result: Seq<u32>)
    requires
        position <= input.len(),
    ensures
        ({
            let (r, p) = collect_loop(condition, input, position, result);
            &&& position <= p <= input.len()
            &&& r == result + input.subrange(position as int, p as int)
            &&& forall|k: int| position <= k < p ==> meets(condition, #[trigger] input[k])
            &&& (p < input.len() ==> !meets(condition, input[p as int]))
        }),
    decreases input.len() - position
{
    if position < input.len() && meets(condition, input[position as int]) {
        let c = input[position as int];
        lemma_collect_loop(condition, input, position + 1, result.push(c));
        let p = collect_loop(condition, input, position, result).1;
        assert(result.push(c) + input.subrange(position as int + 1, p as int)
            =~= result + input.subrange(position as int, p as int));
    } else {
        assert(input.subrange(position as int, position as int) =~= seq![]);
        assert(result + seq![] =~= result);
    }
}

/// Collecting from `position` returns the run of code points there that
/// meet the condition, and the position after it.
pub proof fn lemma_collect(condition: Condition, input: Seq<u32>, position: nat)
    requires
        position <= input.len(),
    ensures
        ({
            let (r, p) = collect(condition, input, position);
            &&& position <= p <= input.len()
            &&& r == input.subrange(position as int, p as int)
            &&& forall|k: int| position <= k < p ==> meets(condition, #[trigger] input[k])
            &&& (p < input.len() ==> !meets(condition, input[p as int]))
        }),
{
    lemma_collect_loop(condition, input, position, seq![]);
    let p = collect(condition, input, position).1;
    assert(seq![] + input.subrange(position as int, p as int) =~= input.subrange(position as int, p as int));
}

/// The JavaScript MIME type essence strings are already in ASCII
/// lowercase, so an ASCII case-insensitive match for one is: the ASCII
/// lowercase of the string is one of them.
pub proof fn lemma_javascript_essences_lowercase()
    ensures
        forall|i: int| 0 <= i < javascript_mime_type_essences().len()
            ==> ascii_lowercase(#[trigger] javascript_mime_type_essences()[i]) == javascript_mime_type_essences()[i],
{
    let l = javascript_mime_type_essences();
    assert(ascii_lowercase(lit_application_ecmascript()) =~= lit_application_ecmascript()) by (compute_only);
    assert(ascii_lowercase(lit_application_javascript()) =~= lit_application_javascript()) by (compute_only);
    assert(ascii_lowercase(lit_application_x_ecmascript()) =~= lit_application_x_ecmascript()) by (compute_only);
    assert(ascii_lowercase(lit_application_x_javascript()) =~= lit_application_x_javascript()) by (compute_only);
    assert(ascii_lowercase(lit_text_ecmascript()) =~= lit_text_ecmascript()) by (compute_only);
    assert(ascii_lowercase(lit_text_javascript()) =~= lit_text_javascript()) by (compute_only);
    assert(ascii_lowercase(lit_text_javascript1_0()) =~= lit_text_javascript1_0()) by (compute_only);
    assert(ascii_lowercase(lit_text_javascript1_1()) =~= lit_text_javascript1_1()) by (compute_only);
    assert(ascii_lowercase(lit_text_javascript1_2()) =~= lit_text_javascript1_2()) by (compute_only);
    assert(ascii_lowercase(lit_text_javascript1_3()) =~= lit_text_javascript1_3()) by (compute_only);
    assert(ascii_lowercase(lit_text_javascript1_4()) =~= lit_text_javascript1_4()) by (compute_only);
    assert(ascii_lowercase(lit_text_javascript1_5()) =~= lit_text_javascript1_5()) by (compute_only);
    assert(ascii_lowercase(lit_text_jscript()) =~= lit_text_jscript()) by (compute_only);
    assert(ascii_lowercase(lit_text_livescript()) =~= lit_text_livescript()) by (compute_only);
    assert(ascii_lowercase(lit_text_x_ecmascript()) =~= lit_text_x_ecmascript()) by (compute_only);
    assert(ascii_lowercase(lit_text_x_javascript()) =~= lit_text_x_javascript()) by (compute_only);
    assert forall|i: int| 0 <= i < l.len() implies ascii_lowercase(#[trigger] l[i]) == l[i] by {
        if i == 0 {} else if i == 1 {} else if i == 2 {} else if i == 3 {} else if i == 4 {}
        else if i == 5 {} else if i == 6 {} else if i == 7 {} else if i == 8 {} else if i == 9 {}
        else if i == 10 {} else if i == 11 {} else if i == 12 {} else if i == 13 {} else if i == 14 {}
        else {}
    }
}


/// Collecting stops exactly at the first code point at or after
/// `position` that does not meet the condition.
pub proof fn lemma_collect_exact(condition: Condition, input: Seq<u32>, position: nat, q: nat)
    requires
        position <= q <= input.len(),
        forall|k: int| position <= k < q ==> meets(condition, #[trigger] input[k]),
        q < input.len() ==> !meets(condition, input[q as int]),
    ensures
        collect(condition, input, position) == (input.subrange(position as int, q as int), q),
{
    lemma_collect(condition, input, position);
    let p = collect(condition, input, position).1;
    if p < q {
        assert(meets(condition, input[p as int]));
    } else if p > q {
        assert(meets(condition, input[q as int]));
    }
}

/// No leading or trailing HTTP whitespace to remove.
pub proof fn lemma_trim_nothing(s: Seq<u32>)
    requires
        s.len() > 0 ==> !is_http_whitespace(s[0]) && !is_http_whitespace(s.last()),
    ensures
        remove_leading_and_trailing_http_whitespace(s) == s,
        remove_trailing_http_whitespace(s) == s,
{
}

// ===========================================================================
// What parsing produces.
// ===========================================================================

/// A non-empty string of HTTP token code points, in ASCII lowercase: what
/// parsing makes of a type, subtype or parameter name.
pub open spec fn is_lowercase_token(s: Seq<u32>) -> bool {
    s.len() > 0 && solely_http_token_code_points(s) && ascii_lowercase(s) == s
}

/// The parameters parsing can produce: lowercase token names, values of
/// HTTP quoted-string token code points, and no name twice.
pub open spec fn parsed_parameters(parameters: OrderedMap) -> bool {
    &&& forall|i: int| 0 <= i < parameters.len() ==> is_lowercase_token((#[trigger] parameters[i]).0)
    &&& forall|i: int| 0 <= i < parameters.len() ==> solely_http_quoted_string_token_code_points((#[trigger] parameters[i]).1)
    &&& forall|i: int, j: int| 0 <= i < j < parameters.len() ==> (#[trigger] parameters[i]).0 != (#[trigger] parameters[j]).0
}

/// The records parsing can produce.
pub open spec fn parsed_form(mime_type: MimeTypeRecord) -> bool {
    &&& is_lowercase_token(mime_type.type_)
    &&& is_lowercase_token(mime_type.subtype)
    &&& parsed_parameters(mime_type.parameters)
}

/// ASCII lowercase keeps the length, is idempotent, and keeps HTTP token
/// code points HTTP token code points.
pub proof fn lemma_ascii_lowercase(s: Seq<u32>)
    ensures
        ascii_lowercase(s).len() == s.len(),
        ascii_lowercase(ascii_lowercase(s)) == ascii_lowercase(s),
        solely_http_token_code_points(s) ==> solely_http_token_code_points(ascii_lowercase(s)),
{
    let l = ascii_lowercase(s);
    assert(ascii_lowercase(l) =~= l);
    lemma_solely_token(s);
    lemma_solely_token(l);
}

/// One iteration of parse a MIME type's step 11.10 keeps the parameters in
/// parsed form.
pub proof fn lemma_set_parameter_form(mime_type: MimeTypeRecord, raw_name: Seq<u32>, value: Seq<u32>)
    requires
        parsed_parameters(mime_type.parameters),
    ensures
        ({
            let m = set_parameter_if_valid(mime_type, ascii_lowercase(raw_name), value);
            &&& parsed_parameters(m.parameters)
            &&& m.type_ == mime_type.type_
            &&& m.subtype == mime_type.subtype
        }),
{
    let name = ascii_lowercase(raw_name);
    lemma_ascii_lowercase(raw_name);
    let params = mime_type.parameters;
    if name.len() != 0 && solely_http_token_code_points(name) && solely_http_quoted_string_token_code_points(value)
        && !map_exists(params, name)
    {
        lemma_map_set_new(params, name, value);
        lemma_map_exists(params, name);
        let new = params.push((name, value));
        assert forall|i: int, j: int| 0 <= i < j < new.len() implies (#[trigger] new[i]).0 != (#[trigger] new[j]).0 by {
            if j == params.len() {
                assert(new[i] == params[i]);
            } else {
                assert(new[i] == params[i] && new[j] == params[j]);
            }
        }
        assert forall|i: int| 0 <= i < new.len() implies is_lowercase_token((#[trigger] new[i]).0) by {
            if i < params.len() {
                assert(new[i] == params[i]);
            }
        }
        assert forall|i: int| 0 <= i < new.len() implies solely_http_quoted_string_token_code_points((#[trigger] new[i]).1) by {
            if i < params.len() {
                assert(new[i] == params[i]);
            }
        }
    }
}

/// Parse a MIME type's step 11 loop keeps the record in parsed form.
pub proof fn lemma_parse_parameters_form(input: Seq<u32>, position: nat, mime_type: MimeTypeRecord)
    requires
        parsed_parameters(mime_type.parameters),
    ensures
        ({
            let m = parse_parameters(input, position, mime_type);
            &&& parsed_parameters(m.parameters)
            &&& m.type_ == mime_type.type_
            &&& m.subtype == mime_type.subtype
        }),
    decreases input.len() - position
{
    if position < input.len() {
        super::termination::lemma_collect_loop_position(Condition::HttpWhitespace, input, position + 1, seq![]);
        let (_, p2) = collect(Condition::HttpWhitespace, input, position + 1);
        super::termination::lemma_collect_loop_position(Condition::NotSemicolonOrEqualsSign, input, p2, seq![]);
        let (raw_name, p3) = collect(Condition::NotSemicolonOrEqualsSign, input, p2);
        let name = ascii_lowercase(raw_name);
        if p3 < input.len() && input[p3 as int] == 0x3B {
            lemma_parse_parameters_form(input, p3, mime_type);
        } else {
            let p4 = if p3 < input.len() { p3 + 1 } else { p3 };
            if p4 < input.len() {
                if input[p4 as int] == 0x22 {
                    super::termination::lemma_quoted_string_loop_position(input, p4 + 1, seq![]);
                    let (value, p5) = collect_an_http_quoted_string(input, p4, true);
                    super::termination::lemma_collect_loop_position(Condition::NotSemicolon, input, p5, seq![]);
                    let (_, p6) = collect(Condition::NotSemicolon, input, p5);
                    lemma_set_parameter_form(mime_type, raw_name, value);
                    lemma_parse_parameters_form(input, p6, set_parameter_if_valid(mime_type, name, value));
                } else {
                    super::termination::lemma_collect_loop_position(Condition::NotSemicolon, input, p4, seq![]);
                    let (raw_value, p5) = collect(Condition::NotSemicolon, input, p4);
                    let value = remove_trailing_http_whitespace(raw_value);
                    if value.len() == 0 {
                        lemma_parse_parameters_form(input, p5, mime_type);
                    } else {
                        lemma_set_parameter_form(mime_type, raw_name, value);
                        lemma_parse_parameters_form(input, p5, set_parameter_if_valid(mime_type, name, value));
                    }
                }
            }
        }
    }
}

/// Every record parse a MIME type returns is in parsed form.
pub proof fn lemma_parse_form(input: Seq<u32>)
    ensures
        parse_a_mime_type(input) matches Some(m) ==> parsed_form(m),
{
    let s = remove_leading_and_trailing_http_whitespace(input);
    let (type_, p) = collect(Condition::NotSolidus, s, 0);
    if type_.len() != 0 && solely_http_token_code_points(type_) && p < s.len() {
        super::termination::lemma_collect_loop_position(Condition::NotSolidus, s, 0, seq![]);
        let (raw_subtype, p2) = collect(Condition::NotSemicolon, s, p + 1);
        let subtype = remove_trailing_http_whitespace(raw_subtype);
        if subtype.len() != 0 && solely_http_token_code_points(subtype) {
            lemma_ascii_lowercase(type_);
            lemma_ascii_lowercase(subtype);
            let m0 = MimeTypeRecord { type_: ascii_lowercase(type_), subtype: ascii_lowercase(subtype), parameters: seq![] };
            lemma_parse_parameters_form(s, p2, m0);
        }
    }
}

// ===========================================================================
// Round trip: parsing a serialization gives the record back.
// ===========================================================================

/// One parameter as serialize a MIME type step 2 appends it.
pub open spec fn segment(name: Seq<u32>, value: Seq<u32>) -> Seq<u32> {
    seq![0x3Bu32] + name + seq![0x3Du32] + serialize_value(value)
}

/// The serialized parameters from entry `i` on.
pub open spec fn segments(parameters: OrderedMap, i: nat) -> Seq<u32>
    decreases parameters.len() - i
{
    if i < parameters.len() {
        segment(parameters[i as int].0, parameters[i as int].1) + segments(parameters, i + 1)
    } else {
        seq![]
    }
}

/// Serialize a MIME type step 2 appends [`segments`].
pub proof fn lemma_serialize_parameters(parameters: OrderedMap, i: nat, acc: Seq<u32>)
    ensures
        serialize_parameters(parameters, i, acc) == acc + segments(parameters, i),
    decreases parameters.len() - i
{
    if i < parameters.len() {
        let (name, value) = parameters[i as int];
        let next = acc + seq![0x3Bu32] + name + seq![0x3Du32] + serialize_value(value);
        lemma_serialize_parameters(parameters, i + 1, next);
        assert(next + segments(parameters, i + 1) =~= acc + segments(parameters, i));
    } else {
        assert(acc + seq![] =~= acc);
    }
}

/// An HTTP token code point is none of the delimiters parsing looks for.
pub proof fn lemma_token_code_point(c: u32)
    requires
        is_http_token_code_point(c),
    ensures
        !is_http_whitespace(c),
        c != 0x22 && c != 0x2F && c != 0x3B && c != 0x3D && c != 0x5C,
        is_http_quoted_string_token_code_point(c),
        c <= 0x7E,
{
}

/// The serialized value is never empty, and does not end in HTTP whitespace.
pub proof fn lemma_serialize_value_ends(value: Seq<u32>)
    ensures
        serialize_value(value).len() > 0,
        !is_http_whitespace(serialize_value(value).last()),
{
    if solely_http_token_code_points(value) && value.len() != 0 {
        lemma_solely_token(value);
        lemma_token_code_point(value.last());
    }
}

/// [`segments`] is empty or starts with U+003B (;), and does not end in
/// HTTP whitespace.
pub proof fn lemma_segments_ends(parameters: OrderedMap, i: nat)
    ensures
        segments(parameters, i).len() > 0 ==> segments(parameters, i)[0] == 0x3B,
        segments(parameters, i).len() > 0 ==> !is_http_whitespace(segments(parameters, i).last()),
        segments(parameters, i).len() == 0 <==> i >= parameters.len(),
    decreases parameters.len() - i
{
    if i < parameters.len() {
        let (name, value) = parameters[i as int];
        lemma_segments_ends(parameters, i + 1);
        lemma_serialize_value_ends(value);
        let seg = segment(name, value);
        let rest = segments(parameters, i + 1);
        assert((seg + rest)[0] == seg[0]);
        if rest.len() > 0 {
            assert((seg + rest).last() == rest.last());
        } else {
            assert((seg + rest).last() == seg.last());
            assert(seg.last() == serialize_value(value).last());
        }
    }
}

/// `input` holds `piece` at `position`.
pub open spec fn holds_at(input: Seq<u32>, position: int, piece: Seq<u32>) -> bool {
    0 <= position && position + piece.len() <= input.len() && input.subrange(position, position + piece.len()) == piece
}

/// Reading a string held at a position.
pub proof fn lemma_holds_at(input: Seq<u32>, position: int, piece: Seq<u32>)
    requires
        holds_at(input, position, piece),
    ensures
        forall|k: int| 0 <= k < piece.len() ==> input[position + k] == #[trigger] piece[k],
{
    assert forall|k: int| 0 <= k < piece.len() implies input[position + k] == #[trigger] piece[k] by {
        assert(input.subrange(position, position + piece.len())[k] == input[position + k]);
    }
}

/// A concatenation held at a position: each part is held in turn.
pub proof fn lemma_holds_at_split(input: Seq<u32>, position: int, a: Seq<u32>, b: Seq<u32>)
    requires
        holds_at(input, position, a + b),
    ensures
        holds_at(input, position, a),
        holds_at(input, position + a.len(), b),
{
    lemma_holds_at(input, position, a + b);
    assert(input.subrange(position, position + a.len()) =~= a) by {
        assert forall|k: int| 0 <= k < a.len() implies input.subrange(position, position + a.len())[k] == a[k] by {
            assert((a + b)[k] == a[k]);
        }
    }
    assert(input.subrange(position + a.len(), position + a.len() + b.len()) =~= b) by {
        assert forall|k: int| 0 <= k < b.len() implies input.subrange(position + a.len(), position + a.len() + b.len())[k] == b[k] by {
            assert((a + b)[a.len() + k] == b[k]);
        }
    }
}

/// Collecting an HTTP quoted string's loop over an escaped value followed
/// by U+0022 (") gives the value back, and stops after that quote.
pub proof fn lemma_quoted_string_loop_escaped(input: Seq<u32>, position: nat, value: Seq<u32>, v: Seq<u32>)
    requires
        holds_at(input, position as int, precede_quotes_and_backslashes(v) + seq![0x22u32]),
    ensures
        quoted_string_loop(input, position, value)
            == (value + v, position + precede_quotes_and_backslashes(v).len() + 1),
    decreases v.len()
{
    let esc = precede_quotes_and_backslashes(v);
    lemma_holds_at_split(input, position as int, esc, seq![0x22u32]);
    lemma_holds_at(input, position as int, esc);
    lemma_holds_at(input, position + esc.len() as int, seq![0x22u32]);
    let nq = Condition::NotQuotationMarkOrReverseSolidus;
    if v.len() == 0 {
        assert(seq![0x22u32][0] == 0x22);
        assert(input[position as int] == 0x22);
        lemma_collect_exact(nq, input, position, position);
        assert(input.subrange(position as int, position as int) =~= seq![]);
        assert(value + seq![] =~= value);
        assert(value + v =~= value);
    } else {
        let c = v[0];
        let rest = v.drop_first();
        let esc_rest = precede_quotes_and_backslashes(rest);
        if c == 0x22 || c == 0x5C {
            assert(esc == seq![0x5Cu32, c] + esc_rest);
            assert(esc[0] == 0x5C && esc[1] == c);
            assert(input[position as int] == 0x5C);
            assert(input[position as int + 1] == c);
            lemma_collect_exact(nq, input, position, position);
            assert(input.subrange(position as int, position as int) =~= seq![]);
            assert(value + seq![] =~= value);
            assert(esc + seq![0x22u32] =~= seq![0x5Cu32, c] + (esc_rest + seq![0x22u32]));
            lemma_holds_at_split(input, position as int, seq![0x5Cu32, c], esc_rest + seq![0x22u32]);
            lemma_quoted_string_loop_escaped(input, position + 2, value.push(c), rest);
            assert(value.push(c) + rest =~= value + v);
        } else {
            assert(esc == seq![c] + esc_rest);
            assert(esc[0] == c);
            assert(input[position as int] == c);
            assert(esc + seq![0x22u32] =~= seq![c] + (esc_rest + seq![0x22u32]));
            lemma_holds_at_split(input, position as int, seq![c], esc_rest + seq![0x22u32]);
            lemma_quoted_string_loop_escaped(input, position + 1, value.push(c), rest);
            // Collecting from `position` and from `position + 1` stop at the
            // same place, since `c` is collected.
            lemma_collect(nq, input, position + 1);
            let q = collect(nq, input, position + 1).1;
            lemma_collect_exact(nq, input, position, q);
            assert(value + input.subrange(position as int, q as int)
                =~= value.push(c) + input.subrange(position as int + 1, q as int));
            assert(value.push(c) + rest =~= value + v);
        }
    }
}

/// Parse a MIME type's step 11 loop, over serialized parameters from entry
/// `i` on, adds exactly those parameters.
pub proof fn lemma_parse_segments(input: Seq<u32>, parameters: OrderedMap, i: nat, mime_type: MimeTypeRecord)
    requires
        parsed_parameters(parameters),
        i <= parameters.len(),
        holds_at(input, input.len() - segments(parameters, i).len(), segments(parameters, i)),
        mime_type.parameters == parameters.subrange(0, i as int),
    ensures
        parse_parameters(input, (input.len() - segments(parameters, i).len()) as nat, mime_type)
            == (MimeTypeRecord { parameters, ..mime_type }),
    decreases parameters.len() - i
{
    let p = (input.len() - segments(parameters, i).len()) as nat;
    lemma_segments_ends(parameters, i);
    if i == parameters.len() {
        assert(parameters.subrange(0, i as int) =~= parameters);
    } else {
        let (name, value) = parameters[i as int];
        assert(is_lowercase_token(parameters[i as int].0));
        assert(solely_http_quoted_string_token_code_points(parameters[i as int].1));
        let sv = serialize_value(value);
        let rest = segments(parameters, i + 1);
        let p_next = (input.len() - rest.len()) as nat;
        lemma_segments_ends(parameters, i + 1);
        lemma_serialize_value_ends(value);
        lemma_solely_token(name);
        // The segment: ";" name "=" sv, then the rest.
        let e = p + 1 + name.len();
        assert(segments(parameters, i) == seq![0x3Bu32] + name + seq![0x3Du32] + sv + rest);
        lemma_holds_at_split(input, p as int, seq![0x3Bu32] + name + seq![0x3Du32] + sv, rest);
        lemma_holds_at_split(input, p as int, seq![0x3Bu32] + name + seq![0x3Du32], sv);
        lemma_holds_at_split(input, p as int, seq![0x3Bu32] + name, seq![0x3Du32]);
        lemma_holds_at_split(input, p as int, seq![0x3Bu32], name);
        lemma_holds_at(input, p as int + 1, name);
        lemma_holds_at(input, e as int, seq![0x3Du32]);
        lemma_holds_at(input, e as int + 1, sv);
        assert(p_next == e + 1 + sv.len());
        assert(seq![0x3Du32][0] == 0x3D);
        assert(input[e as int] == 0x3D);
        // 11.2: nothing to skip; name[0] is a token code point.
        lemma_token_code_point(name[0]);
        assert(input[p as int + 1] == name[0]);
        lemma_collect_exact(Condition::HttpWhitespace, input, p + 1, p + 1);
        // 11.3: the name, up to "=".
        assert forall|k: int| p + 1 <= k < e implies meets(Condition::NotSemicolonOrEqualsSign, #[trigger] input[k]) by {
            assert(input[k] == name[k - p - 1]);
            lemma_token_code_point(name[k - p - 1]);
        }
        lemma_collect_exact(Condition::NotSemicolonOrEqualsSign, input, p + 1, e);
        // The next segment starts with ";", or the input ends.
        if rest.len() > 0 {
            lemma_holds_at(input, p_next as int, rest);
            assert(input[p_next as int] == 0x3B);
        }
        // 11.10 sets the parameter: the name is new.
        let before = parameters.subrange(0, i as int);
        lemma_map_exists(before, name);
        assert forall|j: int| 0 <= j < before.len() implies (#[trigger] before[j]).0 != name by {
            assert(before[j] == parameters[j]);
        }
        lemma_map_set_new(before, name, value);
        assert(before.push((name, value)) =~= parameters.subrange(0, i as int + 1));
        let next = MimeTypeRecord { parameters: parameters.subrange(0, i as int + 1), ..mime_type };
        assert(set_parameter_if_valid(mime_type, name, value) == next);
        if solely_http_token_code_points(value) && value.len() != 0 {
            // 11.9: an unquoted token value, up to ";" or the end.
            assert(sv == value);
            lemma_solely_token(value);
            lemma_token_code_point(value[0]);
            assert(input[e as int + 1] == value[0]);
            assert forall|k: int| e + 1 <= k < p_next implies meets(Condition::NotSemicolon, #[trigger] input[k]) by {
                assert(input[k] == value[k - e - 1]);
                lemma_token_code_point(value[k - e - 1]);
            }
            lemma_collect_exact(Condition::NotSemicolon, input, e + 1, p_next);
            lemma_token_code_point(value.last());
            lemma_trim_nothing(value);
        } else {
            // 11.8: a quoted value.
            let esc = precede_quotes_and_backslashes(value);
            assert(sv == seq![0x22u32] + (esc + seq![0x22u32]));
            lemma_holds_at_split(input, e as int + 1, seq![0x22u32], esc + seq![0x22u32]);
            lemma_holds_at(input, e as int + 1, seq![0x22u32]);
            assert(input[e as int + 1] == 0x22);
            lemma_quoted_string_loop_escaped(input, e + 2, seq![], value);
            assert(seq![] + value =~= value);
            assert(e + 2 + esc.len() + 1 == p_next);
            lemma_collect_exact(Condition::NotSemicolon, input, p_next, p_next);
        }
        lemma_parse_segments(input, parameters, i + 1, next);
    }
}

/// Parse a MIME type's steps 1 to 10 on a serialization: they read back
/// the type and subtype, and leave the position at the parameters.
proof fn lemma_parse_head(s: Seq<u32>, t: Seq<u32>, st: Seq<u32>, segs: Seq<u32>)
    requires
        s == t + seq![0x2Fu32] + st + segs,
        is_lowercase_token(t),
        is_lowercase_token(st),
        segs.len() > 0 ==> segs[0] == 0x3B && !is_http_whitespace(segs.last()),
    ensures
        parse_a_mime_type(s) == Some(parse_parameters(
            s,
            (t.len() + 1 + st.len()) as nat,
            MimeTypeRecord { type_: t, subtype: st, parameters: seq![] },
        )),
{
    let head = t + seq![0x2Fu32] + st;
    let h = head.len();
    lemma_solely_token(t);
    lemma_solely_token(st);
    lemma_token_code_point(t[0]);
    lemma_token_code_point(st.last());
    // Step 1 removes nothing.
    assert(s[0] == t[0]);
    if segs.len() > 0 {
        assert(s.last() == segs.last());
    } else {
        assert(s.last() == st.last());
    }
    lemma_trim_nothing(s);
    assert(remove_leading_and_trailing_http_whitespace(s) == s);
    assert(holds_at(s, 0, head + segs)) by {
        assert(s.subrange(0, s.len() as int) =~= s);
    }
    lemma_holds_at_split(s, 0, head, segs);
    lemma_holds_at_split(s, 0, t + seq![0x2Fu32], st);
    lemma_holds_at_split(s, 0, t, seq![0x2Fu32]);
    lemma_holds_at(s, 0, t);
    lemma_holds_at(s, t.len() as int, seq![0x2Fu32]);
    lemma_holds_at(s, t.len() as int + 1, st);
    assert(seq![0x2Fu32][0] == 0x2F);
    assert(s[t.len() as int] == 0x2F);
    // Step 3: the type, up to "/".
    assert forall|k: int| 0 <= k < t.len() implies meets(Condition::NotSolidus, #[trigger] s[k]) by {
        assert(s[k] == t[k]);
        lemma_token_code_point(t[k]);
    }
    lemma_collect_exact(Condition::NotSolidus, s, 0, t.len());
    assert(collect(Condition::NotSolidus, s, 0) == (t, t.len()));
    // Step 7: the subtype, up to ";" or the end.
    assert forall|k: int| t.len() + 1 <= k < h implies meets(Condition::NotSemicolon, #[trigger] s[k]) by {
        assert(s[k] == st[k - t.len() - 1]);
        lemma_token_code_point(st[k - t.len() - 1]);
    }
    if segs.len() > 0 {
        lemma_holds_at(s, h as int, segs);
        assert(s[h as int] == 0x3B);
    }
    lemma_collect_exact(Condition::NotSemicolon, s, t.len() + 1, h);
    assert(collect(Condition::NotSemicolon, s, t.len() + 1) == (st, h));
    // Step 8 removes nothing; step 10 lowercases nothing.
    lemma_trim_nothing(st);
}

/// Round trip: parsing the serialization of a record in parsed form gives
/// the record back.
pub proof fn lemma_parse_serialize(mime_type: MimeTypeRecord)
    requires
        parsed_form(mime_type),
    ensures
        parse_a_mime_type(serialize_a_mime_type(mime_type)) == Some(mime_type),
{
    let t = mime_type.type_;
    let st = mime_type.subtype;
    let parameters = mime_type.parameters;
    let head = t + seq![0x2Fu32] + st;
    let segs = segments(parameters, 0);
    let s = serialize_a_mime_type(mime_type);
    lemma_serialize_parameters(parameters, 0, head);
    assert(s == head + segs);
    lemma_segments_ends(parameters, 0);
    lemma_parse_head(s, t, st, segs);
    assert(holds_at(s, s.len() - segs.len(), segs)) by {
        assert(s.subrange(head.len() as int, s.len() as int) =~= segs);
    }
    let m0 = MimeTypeRecord { type_: t, subtype: st, parameters: seq![] };
    assert(parameters.subrange(0, 0) =~= seq![]);
    lemma_parse_segments(s, parameters, 0, m0);
}

/// Parsing is idempotent through serialization: whatever parse a MIME type
/// returns, parsing its serialization returns the same record.
pub proof fn lemma_parse_serialize_parse(input: Seq<u32>)
    ensures
        parse_a_mime_type(input) matches Some(m) ==> parse_a_mime_type(serialize_a_mime_type(m)) == Some(m),
{
    lemma_parse_form(input);
    if let Some(m) = parse_a_mime_type(input) {
        lemma_parse_serialize(m);
    }
}

// ===========================================================================
// Serializing to bytes is defined on every parsed record.
// ===========================================================================

/// Escaping keeps code points at most U+00FF.
proof fn lemma_escape_at_most_ff(v: Seq<u32>)
    requires
        super::contract::all_at_most_ff(v),
    ensures
        super::contract::all_at_most_ff(precede_quotes_and_backslashes(v)),
    decreases v.len()
{
    if v.len() > 0 {
        let rest = v.drop_first();
        assert forall|k: int| 0 <= k < rest.len() implies #[trigger] rest[k] <= 0xFF by {
            assert(rest[k] == v[k + 1]);
        }
        lemma_escape_at_most_ff(rest);
        let e = precede_quotes_and_backslashes(v);
        let er = precede_quotes_and_backslashes(rest);
        let first = if v[0] == 0x22 || v[0] == 0x5C { seq![0x5Cu32, v[0]] } else { seq![v[0]] };
        assert(e == first + er);
        assert forall|k: int| 0 <= k < e.len() implies #[trigger] e[k] <= 0xFF by {
            if k >= first.len() {
                assert(e[k] == er[k - first.len()]);
            }
        }
    }
}

/// A concatenation of strings with code points at most U+00FF.
proof fn lemma_concat_at_most_ff(a: Seq<u32>, b: Seq<u32>)
    requires
        super::contract::all_at_most_ff(a),
        super::contract::all_at_most_ff(b),
    ensures
        super::contract::all_at_most_ff(a + b),
{
    assert forall|k: int| 0 <= k < (a + b).len() implies #[trigger] (a + b)[k] <= 0xFF by {
        if k >= a.len() {
            assert((a + b)[k] == b[k - a.len()]);
        }
    }
}

/// HTTP quoted-string token code points are at most U+00FF.
proof fn lemma_quoted_string_token_at_most_ff(v: Seq<u32>)
    requires
        solely_http_quoted_string_token_code_points(v),
    ensures
        super::contract::all_at_most_ff(v),
{
    lemma_solely_quoted_string_token(v);
}

/// The serialized parameters from entry `i` on have code points at most
/// U+00FF.
proof fn lemma_segments_at_most_ff(parameters: OrderedMap, i: nat)
    requires
        parsed_parameters(parameters),
    ensures
        super::contract::all_at_most_ff(segments(parameters, i)),
    decreases parameters.len() - i
{
    if i < parameters.len() {
        let (name, value) = parameters[i as int];
        assert(is_lowercase_token(parameters[i as int].0));
        assert(solely_http_quoted_string_token_code_points(parameters[i as int].1));
        lemma_segments_at_most_ff(parameters, i + 1);
        lemma_solely_token(name);
        assert forall|k: int| 0 <= k < name.len() implies #[trigger] name[k] <= 0xFF by {
            lemma_token_code_point(name[k]);
        }
        lemma_quoted_string_token_at_most_ff(value);
        lemma_escape_at_most_ff(value);
        let sv = serialize_value(value);
        let q = seq![0x22u32];
        if !(solely_http_token_code_points(value) && value.len() != 0) {
            lemma_concat_at_most_ff(q, precede_quotes_and_backslashes(value));
            lemma_concat_at_most_ff(q + precede_quotes_and_backslashes(value), q);
        }
        lemma_concat_at_most_ff(seq![0x3Bu32], name);
        lemma_concat_at_most_ff(seq![0x3Bu32] + name, seq![0x3Du32]);
        lemma_concat_at_most_ff(seq![0x3Bu32] + name + seq![0x3Du32], sv);
        lemma_concat_at_most_ff(segment(name, value), segments(parameters, i + 1));
    }
}

/// Every record in parsed form (so every record parsing returns, by
/// [`lemma_parse_form`]) meets `serialize_to_bytes`'s precondition.
pub proof fn lemma_parse_serializable(mime_type: MimeTypeRecord)
    requires
        parsed_form(mime_type),
    ensures
        super::contract::serialize_to_bytes_requires(mime_type),
{
    let t = mime_type.type_;
    let st = mime_type.subtype;
    lemma_solely_token(t);
    lemma_solely_token(st);
    assert forall|k: int| 0 <= k < t.len() implies #[trigger] t[k] <= 0xFF by {
        lemma_token_code_point(t[k]);
    }
    assert forall|k: int| 0 <= k < st.len() implies #[trigger] st[k] <= 0xFF by {
        lemma_token_code_point(st[k]);
    }
    lemma_concat_at_most_ff(t, seq![0x2Fu32]);
    lemma_concat_at_most_ff(t + seq![0x2Fu32], st);
    lemma_segments_at_most_ff(mime_type.parameters, 0);
    lemma_concat_at_most_ff(t + seq![0x2Fu32] + st, segments(mime_type.parameters, 0));
    lemma_serialize_parameters(mime_type.parameters, 0, t + seq![0x2Fu32] + st);
}

} // verus!
