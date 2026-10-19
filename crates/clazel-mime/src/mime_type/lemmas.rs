//! Facts proven about the MIME type spec in [`super::spec`]. Some are the
//! working facts the implementation's proof uses (the recursive
//! definitions restated with quantifiers); the rest are evidence that the
//! transcription behaves as the standard says.

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

} // verus!
