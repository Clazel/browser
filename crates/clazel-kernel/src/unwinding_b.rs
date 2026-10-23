//! `lemma_local_respect` and `lemma_navigate_declassify` of item 2.11: an
//! event of a renderer of another domain than the observer's.

#[allow(unused_imports)]
use super::cookie_theorems::*;
#[allow(unused_imports)]
use super::domain::*;
#[allow(unused_imports)]
use super::invariant::*;
#[allow(unused_imports)]
use super::lock::*;
#[allow(unused_imports)]
use super::noninterference::*;
#[allow(unused_imports)]
use super::projection::*;
#[allow(unused_imports)]
use super::retrieval_projection::*;
#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use super::statements::*;
#[allow(unused_imports)]
use super::store_projection::*;
#[allow(unused_imports)]
use super::theorems::*;
#[allow(unused_imports)]
use super::unwind_base::*;
#[allow(unused_imports)]
use super::unwinding::*;
#[allow(unused_imports)]
use super::unwinding_d::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The sender of another domain, found in `s1` (and `s2`).
pub proof fn lemma_b_sender(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, d: Domain, s1: State, s2: State, id: nat, bytes: Seq<u8>, d2: Domain)
    requires
        rel(rules, urls, d, s1, s2),
        event_domain(rules, s1, Event::FromRenderer { id, bytes }) == Some(d2),
        d2 != d,
    ensures
        find_by_id(s1.renderers, id, 0) is Some,
        0 <= find_by_id(s1.renderers, id, 0)->Some_0 < s1.renderers.len(),
        s1.renderers[find_by_id(s1.renderers, id, 0)->Some_0].id == id,
        domain_of_renderer(rules, s1.renderers[find_by_id(s1.renderers, id, 0)->Some_0]) == d2,
        s2.renderers.contains(s1.renderers[find_by_id(s1.renderers, id, 0)->Some_0]),
{
    lemma_found_contained(s1, id);
    let i1 = find_by_id(s1.renderers, id, 0)->Some_0;
    assert(s2.renderers.contains(s1.renderers[i1]));
}

/// A step of a renderer of another domain, that does not navigate, only
/// addresses its sender (the only renderer it can name).
pub proof fn lemma_local_outputs(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, s: State, id: nat, bytes: Seq<u8>)
    requires
        find_by_id(s.renderers, id, 0) is Some,
        declassified(urls, s, Event::FromRenderer { id, bytes }) is None,
    ensures
        forall|k: int|
            0 <= k < step(rules, urls, s, Event::FromRenderer { id, bytes }).1.len() ==> output_id(#[trigger] step(rules, urls, s, Event::FromRenderer { id, bytes }).1[k]) == id,
{
    lemma_found_contained(s, id);
    let i = find_by_id(s.renderers, id, 0)->Some_0;
    let r = s.renderers[i];
    let out = step(rules, urls, s, Event::FromRenderer { id, bytes }).1;
    if let Some(m) = decode_renderer_frame(bytes) {
        lemma_storage_call_frame(s, r, m);
        if let clazel_ipc::message::spec::Message::Navigate { url } = m {
            if let Some(relative) = clazel_encoding::utf8::spec::utf8_decode_without_bom_or_fail(url) {
                if let Some(resolved) = (urls.resolve)(r.url, relative) {
                    assert(false);
                }
            }
        }
    }
}

/// After such a step, the state's renderers are among the old ones.
pub proof fn lemma_local_table(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, s: State, id: nat, bytes: Seq<u8>)
    requires
        find_by_id(s.renderers, id, 0) is Some,
        declassified(urls, s, Event::FromRenderer { id, bytes }) is None,
    ensures
        ({
            let s1b = step(rules, urls, s, Event::FromRenderer { id, bytes }).0;
            s1b.renderers == s.renderers || s1b.renderers == s.renderers.remove(find_by_id(s.renderers, id, 0)->Some_0)
        }),
{
    lemma_found_contained(s, id);
    let i = find_by_id(s.renderers, id, 0)->Some_0;
    let r = s.renderers[i];
    if let Some(m) = decode_renderer_frame(bytes) {
        lemma_storage_call_frame(s, r, m);
        if let clazel_ipc::message::spec::Message::Navigate { url } = m {
            if let Some(relative) = clazel_encoding::utf8::spec::utf8_decode_without_bom_or_fail(url) {
                if let Some(resolved) = (urls.resolve)(r.url, relative) {
                    assert(false);
                }
            }
        }
    }
}

/// **`lemma_local_respect`.**
pub proof fn lemma_local_respect(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, d: Domain, s1: State, s2: State, e: Event)
    requires
        rel(rules, urls, d, s1, s2),
        other_domain_local(rules, urls, d, s1, e),
        state_ps_free(rules, step(rules, urls, s1, e).0),
    ensures
        local_respect_statement(rules, urls, d, s1, s2, e),
{
    let id = e->FromRenderer_id;
    let bytes = e->FromRenderer_bytes;
    assert(e == (Event::FromRenderer { id, bytes }));
    let d2 = event_domain(rules, s1, e)->Some_0;
    lemma_b_sender(rules, urls, d, s1, s2, id, bytes, d2);
    let i1 = find_by_id(s1.renderers, id, 0)->Some_0;
    let r = s1.renderers[i1];
    lemma_step_preserves_wf(rules, urls, s1, e);
    lemma_jar_no_public_suffix_step(rules, urls, s1, e);
    lemma_local_outputs(rules, urls, s1, id, bytes);
    lemma_local_table(rules, urls, s1, id, bytes);
    let (s1b, out1) = step(rules, urls, s1, e);
    // Nothing is addressed to d: the outputs name the sender, who is in d2, and no renderer
    // of s1b with that id is in d.
    assert forall|k: int| 0 <= k < out1.len() implies !addressed_to(rules, d, s1, s1b, #[trigger] out1[k]) by {
        if addressed_to(rules, d, s1, s1b, out1[k]) {
            let q = choose|q: Renderer| (s1.renderers.contains(q) || s1b.renderers.contains(q)) && q.id == output_id(out1[k]) && domain_of_renderer(rules, q) == d;
            if s1b.renderers == s1.renderers.remove(i1) {
                lemma_remove_contains(urls, s1.renderers, s1.next_id, i1, q);
            }
            assert(s1.renderers.contains(q));
            assert(s1.renderers.contains(r));
            lemma_same_id_same_renderer(urls, s1.renderers, s1.next_id, q, r);
        }
    }
    lemma_filter_none(out1, |o: Output| addressed_to(rules, d, s1, s1b, o));
    // The state.
    if s1b.renderers == s1.renderers.remove(i1) && s1b.renderers != s1.renderers {
        assert forall|x: Renderer| s1b.renderers.contains(x) implies s2.renderers.contains(x) by {
            lemma_remove_contains(urls, s1.renderers, s1.next_id, i1, x);
            let k = choose|k: int| 0 <= k < s1.renderers.len() && s1.renderers[k] == x;
        }
        assert forall|x: Renderer| s2.renderers.contains(x) && domain_of_renderer(rules, x) == d implies s1b.renderers.contains(x) by {
            lemma_remove_contains(urls, s1.renderers, s1.next_id, i1, x);
            assert(s1.renderers.contains(x));
            if x.id == r.id {
                lemma_same_id_same_renderer(urls, s1.renderers, s1.next_id, x, r);
            }
        }
        assert forall|x: Renderer| s1b.renderers.contains(x) implies lock_not_public_suffix(rules, x.lock) by {
            lemma_remove_contains(urls, s1.renderers, s1.next_id, i1, x);
            lemma_ps_free_elem(rules, s1, x);
        }
        assert forall|x: Renderer| s2.renderers.contains(x) implies lock_not_public_suffix(rules, x.lock) by {
            lemma_ps_free_elem(rules, s2, x);
        }
        assert(s1b.jar == s1.jar && s1b.storage == s1.storage && s1b.now == s1.now && s1b.next_id == s1.next_id);
        lemma_rel_from_sets(rules, urls, d, s1b, s2);
    } else {
        // The renderers are as before; only the jar or the storage may change.
        assert(s1b.renderers == s1.renderers);
        if let Some(m) = decode_renderer_frame(bytes) {
            lemma_storage_call_frame(s1, r, m);
            lemma_storage_call_local(s1, s1, r, r, m);
            assert(s1b.next_id == s1.next_id && s1b.now == s1.now);
            match m {
                clazel_ipc::message::spec::Message::CookieGet => {
                    if !cookie_averse(r.lock) {
                        lemma_domain_of_tuple(rules, urls, s1, i1, d2);
                        let h = lock_host(r.lock)->Some_0;
                        let url = request_url_of(urls, r);
                        assert(url.host == Some(h));
                        if let Domain::Root(rootd) = d {
                            assert(rootd != clazel_cookie::storage::spec::cookie_root(rules, h));
                            lemma_foreign_retrieval(rules, s1.jar, url, document_context(r.lock), s1.now, h, rootd);
                        }
                    }
                },
                clazel_ipc::message::spec::Message::CookieSet { cookie_string } => {
                    if !cookie_averse(r.lock) {
                        lemma_domain_of_tuple(rules, urls, s1, i1, d2);
                        let h = lock_host(r.lock)->Some_0;
                        let url = request_url_of(urls, r);
                        if let Domain::Root(rootd) = d {
                            lemma_foreign_store(rules, s1.jar, cookie_string, url, document_context(r.lock), s1.now, h, rootd);
                        }
                    }
                },
                _ => {},
            }
        }
        assert forall|o: clazel_origin::spec::Origin| o is Tuple && domain_of_lock(rules, o) == d implies storage_of(s1b, o) == storage_of(s2, o) by {
            if let Some(m) = decode_renderer_frame(bytes) {
                if is_storage_message(m) && r.lock is Tuple {
                    assert(domain_of_lock(rules, r.lock) == d2);
                    assert(o != r.lock);
                }
            }
        }
        lemma_rel_same_table(rules, urls, d, s1, s2, s1b, s2);
    }
}

} // verus!
