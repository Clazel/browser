//! `lemma_output_consistency` and `lemma_step_consistency` of item 2.11 for a
//! `FromRenderer` event of the observed domain `d`: per message kind.

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
use vstd::prelude::*;

verus! {

/// A frame of an observed domain's renderer: `r` is in both states.
pub proof fn lemma_d_sender(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, d: Domain, s1: State, s2: State, id: nat, bytes: Seq<u8>)
    requires
        rel(rules, urls, d, s1, s2),
        event_domain(rules, s1, Event::FromRenderer { id, bytes }) == Some(d),
    ensures
        find_by_id(s1.renderers, id, 0) is Some,
        find_by_id(s2.renderers, id, 0) is Some,
        s1.renderers[find_by_id(s1.renderers, id, 0)->Some_0] == s2.renderers[find_by_id(s2.renderers, id, 0)->Some_0],
        0 <= find_by_id(s1.renderers, id, 0)->Some_0 < s1.renderers.len(),
        0 <= find_by_id(s2.renderers, id, 0)->Some_0 < s2.renderers.len(),
        domain_of_renderer(rules, s1.renderers[find_by_id(s1.renderers, id, 0)->Some_0]) == d,
        s1.renderers[find_by_id(s1.renderers, id, 0)->Some_0].id == id,
{
    lemma_found_contained(s1, id);
    let i1 = find_by_id(s1.renderers, id, 0)->Some_0;
    let r = s1.renderers[i1];
    assert(s2.renderers.contains(r));
    lemma_find_contained(urls, s2, r);
    lemma_found_contained(s2, id);
}

/// The part of `rel` that does not mention the renderer table, for a step that
/// leaves the renderers, counter and time alone.
pub proof fn lemma_rel_same_table(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, d: Domain, s1: State, s2: State, s1b: State, s2b: State)
    requires
        rel(rules, urls, d, s1, s2),
        kernel_wf(rules, urls, s1b),
        kernel_wf(rules, urls, s2b),
        s1b.renderers == s1.renderers,
        s2b.renderers == s2.renderers,
        s1b.next_id == s1.next_id,
        s2b.next_id == s2.next_id,
        s1b.now == s1.now,
        s2b.now == s2.now,
        cookies_agree(rules, d, s1b, s2b),
        forall|o: clazel_origin::spec::Origin| o is Tuple && domain_of_lock(rules, o) == d ==> storage_of(s1b, o) == storage_of(s2b, o),
        jar_no_public_suffix(rules, s1b.jar),
        jar_no_public_suffix(rules, s2b.jar),
    ensures
        rel(rules, urls, d, s1b, s2b),
{
    assert forall|x: Renderer| s1b.renderers.contains(x) implies lock_not_public_suffix(rules, x.lock) by {
        lemma_ps_free_elem(rules, s1, x);
    }
    assert forall|x: Renderer| s2b.renderers.contains(x) implies lock_not_public_suffix(rules, x.lock) by {
        lemma_ps_free_elem(rules, s2, x);
    }
    assert forall|x: Renderer| s1b.renderers.contains(x) implies s2b.renderers.contains(x) by {
        let k = choose|k: int| 0 <= k < s1.renderers.len() && s1.renderers[k] == x;
    }
    lemma_rel_from_sets(rules, urls, d, s1b, s2b);
}

/// The domain of a tuple lock with a host is the root of the host.
pub proof fn lemma_domain_of_tuple(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, s: State, i: int, d: Domain)
    requires
        renderers_wf(urls, s.renderers, s.next_id),
        0 <= i < s.renderers.len(),
        s.renderers[i].lock is Tuple,
        domain_of_renderer(rules, s.renderers[i]) == d,
    ensures
        lock_host(s.renderers[i].lock) is Some,
        d == Domain::Root(clazel_cookie::storage::spec::cookie_root(rules, lock_host(s.renderers[i].lock)->Some_0)),
{
    lemma_tuple_lock_host(urls, s.renderers, s.next_id, i);
}

/// `CookieGet` by a renderer of `d`.
pub proof fn lemma_d_cookie_get(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, d: Domain, s1: State, s2: State, id: nat, bytes: Seq<u8>)
    requires
        rel(rules, urls, d, s1, s2),
        event_domain(rules, s1, Event::FromRenderer { id, bytes }) == Some(d),
        decode_renderer_frame(bytes) == Some(clazel_ipc::message::spec::Message::CookieGet),
        state_ps_free(rules, step(rules, urls, s1, Event::FromRenderer { id, bytes }).0),
    ensures
        step(rules, urls, s1, Event::FromRenderer { id, bytes }).1 == step(rules, urls, s2, Event::FromRenderer { id, bytes }).1,
        rel(rules, urls, d, step(rules, urls, s1, Event::FromRenderer { id, bytes }).0, step(rules, urls, s2, Event::FromRenderer { id, bytes }).0),
{
    let e = Event::FromRenderer { id, bytes };
    lemma_d_sender(rules, urls, d, s1, s2, id, bytes);
    let i1 = find_by_id(s1.renderers, id, 0)->Some_0;
    let i2 = find_by_id(s2.renderers, id, 0)->Some_0;
    let r = s1.renderers[i1];
    lemma_step_preserves_wf(rules, urls, s1, e);
    lemma_step_preserves_wf(rules, urls, s2, e);
    lemma_jar_no_public_suffix_step(rules, urls, s1, e);
    lemma_jar_no_public_suffix_step(rules, urls, s2, e);
    let (s1b, o1) = step(rules, urls, s1, e);
    let (s2b, o2) = step(rules, urls, s2, e);
    if !cookie_averse(r.lock) {
        lemma_domain_of_tuple(rules, urls, s1, i1, d);
        let h = lock_host(r.lock)->Some_0;
        let root = clazel_cookie::storage::spec::cookie_root(rules, h);
        let url = request_url_of(urls, r);
        let ctx = document_context(r.lock);
        assert(url.host == Some(h));
        assert(live_root(rules, s1.jar, s1.now, root) == live_root(rules, s2.jar, s2.now, root));
        lemma_retrieval_agree(rules, s1.jar, s2.jar, url, ctx, s1.now, h, root);
        lemma_retrieval_jar_agree(rules, s1.jar, s2.jar, url, ctx, s1.now, h, root);
    }
    lemma_rel_same_table(rules, urls, d, s1, s2, s1b, s2b);
}

/// `CookieSet` by a renderer of `d`.
pub proof fn lemma_d_cookie_set(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, d: Domain, s1: State, s2: State, id: nat, bytes: Seq<u8>, cs: Seq<u8>)
    requires
        rel(rules, urls, d, s1, s2),
        event_domain(rules, s1, Event::FromRenderer { id, bytes }) == Some(d),
        decode_renderer_frame(bytes) == Some(clazel_ipc::message::spec::Message::CookieSet { cookie_string: cs }),
        state_ps_free(rules, step(rules, urls, s1, Event::FromRenderer { id, bytes }).0),
    ensures
        step(rules, urls, s1, Event::FromRenderer { id, bytes }).1 == step(rules, urls, s2, Event::FromRenderer { id, bytes }).1,
        rel(rules, urls, d, step(rules, urls, s1, Event::FromRenderer { id, bytes }).0, step(rules, urls, s2, Event::FromRenderer { id, bytes }).0),
{
    let e = Event::FromRenderer { id, bytes };
    lemma_d_sender(rules, urls, d, s1, s2, id, bytes);
    let i1 = find_by_id(s1.renderers, id, 0)->Some_0;
    let r = s1.renderers[i1];
    lemma_step_preserves_wf(rules, urls, s1, e);
    lemma_step_preserves_wf(rules, urls, s2, e);
    lemma_jar_no_public_suffix_step(rules, urls, s1, e);
    lemma_jar_no_public_suffix_step(rules, urls, s2, e);
    let (s1b, o1) = step(rules, urls, s1, e);
    let (s2b, o2) = step(rules, urls, s2, e);
    if !cookie_averse(r.lock) {
        lemma_domain_of_tuple(rules, urls, s1, i1, d);
        lemma_request_url_host_nonempty(urls, r);
        let h = lock_host(r.lock)->Some_0;
        let root = clazel_cookie::storage::spec::cookie_root(rules, h);
        let url = request_url_of(urls, r);
        let ctx = document_context(r.lock);
        assert(s1.renderers.contains(r));
        lemma_ps_free_elem(rules, s1, r);
        assert(live_root(rules, s1.jar, s1.now, root) == live_root(rules, s2.jar, s2.now, root));
        lemma_store_agree(rules, s1.jar, s2.jar, cs, url, ctx, s1.now, h, root);
    }
    lemma_rel_same_table(rules, urls, d, s1, s2, s1b, s2b);
}

/// A `localStorage` call by a renderer of `d`.
pub proof fn lemma_d_storage(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, d: Domain, s1: State, s2: State, id: nat, bytes: Seq<u8>, m: clazel_ipc::message::spec::Message)
    requires
        rel(rules, urls, d, s1, s2),
        event_domain(rules, s1, Event::FromRenderer { id, bytes }) == Some(d),
        decode_renderer_frame(bytes) == Some(m),
        is_storage_message(m),
        state_ps_free(rules, step(rules, urls, s1, Event::FromRenderer { id, bytes }).0),
    ensures
        step(rules, urls, s1, Event::FromRenderer { id, bytes }).1 == step(rules, urls, s2, Event::FromRenderer { id, bytes }).1,
        rel(rules, urls, d, step(rules, urls, s1, Event::FromRenderer { id, bytes }).0, step(rules, urls, s2, Event::FromRenderer { id, bytes }).0),
{
    let e = Event::FromRenderer { id, bytes };
    lemma_d_sender(rules, urls, d, s1, s2, id, bytes);
    let i1 = find_by_id(s1.renderers, id, 0)->Some_0;
    let r = s1.renderers[i1];
    lemma_step_preserves_wf(rules, urls, s1, e);
    lemma_step_preserves_wf(rules, urls, s2, e);
    lemma_jar_no_public_suffix_step(rules, urls, s1, e);
    lemma_jar_no_public_suffix_step(rules, urls, s2, e);
    let (s1b, o1) = step(rules, urls, s1, e);
    let (s2b, o2) = step(rules, urls, s2, e);
    if r.lock is Tuple {
        assert(domain_of_lock(rules, r.lock) == d);
        assert(storage_of(s1, r.lock) == storage_of(s2, r.lock));
        lemma_storage_call_local(s1, s2, r, r, m);
        lemma_storage_call_frame(s1, r, m);
        lemma_storage_call_frame(s2, r, m);
        assert forall|o: clazel_origin::spec::Origin| o is Tuple && domain_of_lock(rules, o) == d implies storage_of(s1b, o) == storage_of(s2b, o) by {
            if o != r.lock {
            }
        }
    }
    lemma_rel_same_table(rules, urls, d, s1, s2, s1b, s2b);
}

/// Anything else a renderer of `d` sends, or a frame from a renderer that
/// is not the observed one's table: the state is unchanged and the outputs
/// are the sender's reply, equal in both.
pub proof fn lemma_d_navigate(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, d: Domain, s1: State, s2: State, id: nat, bytes: Seq<u8>, url: Seq<u8>)
    requires
        rel(rules, urls, d, s1, s2),
        event_domain(rules, s1, Event::FromRenderer { id, bytes }) == Some(d),
        decode_renderer_frame(bytes) == Some(clazel_ipc::message::spec::Message::Navigate { url }),
        state_ps_free(rules, step(rules, urls, s1, Event::FromRenderer { id, bytes }).0),
    ensures
        step(rules, urls, s1, Event::FromRenderer { id, bytes }).1 == step(rules, urls, s2, Event::FromRenderer { id, bytes }).1,
        rel(rules, urls, d, step(rules, urls, s1, Event::FromRenderer { id, bytes }).0, step(rules, urls, s2, Event::FromRenderer { id, bytes }).0),
{
    let e = Event::FromRenderer { id, bytes };
    lemma_d_sender(rules, urls, d, s1, s2, id, bytes);
    let i1 = find_by_id(s1.renderers, id, 0)->Some_0;
    let r = s1.renderers[i1];
    let (s1b, o1) = step(rules, urls, s1, e);
    let (s2b, o2) = step(rules, urls, s2, e);
    match clazel_encoding::utf8::spec::utf8_decode_without_bom_or_fail(url) {
        None => {
            assert(s1b == s1 && s2b == s2);
        },
        Some(relative) => match (urls.resolve)(r.url, relative) {
            None => {
                assert(s1b == s1 && s2b == s2);
            },
            Some(resolved) => {
                if lock_of_url(urls, resolved, s1.next_id) is None {
                    assert(s1b == s1 && s2b == s2);
                } else {
                    assert(s1.renderers.contains(r));
                    lemma_found_contained(s1, r.tab);
                    lemma_find_contained(urls, s1, r);
                    lemma_navigate_tab_consistency(rules, urls, d, s1, s2, r.tab, resolved, no_script());
                }
            },
        },
    }
}

/// A frame that does not decode kills the sender: for a renderer of `d`.
pub proof fn lemma_d_kill(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, d: Domain, s1: State, s2: State, id: nat, bytes: Seq<u8>)
    requires
        rel(rules, urls, d, s1, s2),
        event_domain(rules, s1, Event::FromRenderer { id, bytes }) == Some(d),
        decode_renderer_frame(bytes) is None,
    ensures
        step(rules, urls, s1, Event::FromRenderer { id, bytes }).1 == step(rules, urls, s2, Event::FromRenderer { id, bytes }).1,
        rel(rules, urls, d, step(rules, urls, s1, Event::FromRenderer { id, bytes }).0, step(rules, urls, s2, Event::FromRenderer { id, bytes }).0),
{
    let e = Event::FromRenderer { id, bytes };
    lemma_d_sender(rules, urls, d, s1, s2, id, bytes);
    let i1 = find_by_id(s1.renderers, id, 0)->Some_0;
    let i2 = find_by_id(s2.renderers, id, 0)->Some_0;
    let r = s1.renderers[i1];
    lemma_step_preserves_wf(rules, urls, s1, e);
    lemma_step_preserves_wf(rules, urls, s2, e);
    let (s1b, o1) = step(rules, urls, s1, e);
    let (s2b, o2) = step(rules, urls, s2, e);
    assert(s1b.renderers == s1.renderers.remove(i1));
    assert(s2b.renderers == s2.renderers.remove(i2));
    assert forall|x: Renderer| s1b.renderers.contains(x) implies s2b.renderers.contains(x) by {
        lemma_remove_contains(urls, s1.renderers, s1.next_id, i1, x);
        lemma_remove_contains(urls, s2.renderers, s2.next_id, i2, x);
        let k = choose|k: int| 0 <= k < s1.renderers.len() && s1.renderers[k] == x;
    }
    assert forall|x: Renderer| s2b.renderers.contains(x) && domain_of_renderer(rules, x) == d implies s1b.renderers.contains(x) by {
        lemma_remove_contains(urls, s1.renderers, s1.next_id, i1, x);
        lemma_remove_contains(urls, s2.renderers, s2.next_id, i2, x);
    }
    assert forall|x: Renderer| s1b.renderers.contains(x) implies lock_not_public_suffix(rules, x.lock) by {
        lemma_remove_contains(urls, s1.renderers, s1.next_id, i1, x);
        lemma_ps_free_elem(rules, s1, x);
    }
    assert forall|x: Renderer| s2b.renderers.contains(x) implies lock_not_public_suffix(rules, x.lock) by {
        lemma_remove_contains(urls, s2.renderers, s2.next_id, i2, x);
        lemma_ps_free_elem(rules, s2, x);
    }
    lemma_rel_from_sets(rules, urls, d, s1b, s2b);
}

/// Any other message a renderer may send is not served: nothing changes.
pub proof fn lemma_d_event(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, d: Domain, s1: State, s2: State, id: nat, bytes: Seq<u8>)
    requires
        rel(rules, urls, d, s1, s2),
        event_domain(rules, s1, Event::FromRenderer { id, bytes }) == Some(d),
        state_ps_free(rules, step(rules, urls, s1, Event::FromRenderer { id, bytes }).0),
    ensures
        step(rules, urls, s1, Event::FromRenderer { id, bytes }).1 == step(rules, urls, s2, Event::FromRenderer { id, bytes }).1,
        rel(rules, urls, d, step(rules, urls, s1, Event::FromRenderer { id, bytes }).0, step(rules, urls, s2, Event::FromRenderer { id, bytes }).0),
{
    let e = Event::FromRenderer { id, bytes };
    lemma_d_sender(rules, urls, d, s1, s2, id, bytes);
    match decode_renderer_frame(bytes) {
        None => lemma_d_kill(rules, urls, d, s1, s2, id, bytes),
        Some(m) => match m {
            clazel_ipc::message::spec::Message::CookieGet => lemma_d_cookie_get(rules, urls, d, s1, s2, id, bytes),
            clazel_ipc::message::spec::Message::CookieSet { cookie_string } => lemma_d_cookie_set(rules, urls, d, s1, s2, id, bytes, cookie_string),
            clazel_ipc::message::spec::Message::Navigate { url } => lemma_d_navigate(rules, urls, d, s1, s2, id, bytes, url),
            _ => {
                if is_storage_message(m) {
                    lemma_d_storage(rules, urls, d, s1, s2, id, bytes, m);
                } else {
                    let (s1b, o1) = step(rules, urls, s1, e);
                    let (s2b, o2) = step(rules, urls, s2, e);
                    lemma_step_preserves_wf(rules, urls, s1, e);
                    lemma_step_preserves_wf(rules, urls, s2, e);
                    assert(s1b == s1 && s2b == s2);
                }
            },
        },
    }
}

} // verus!
