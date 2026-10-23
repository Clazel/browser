//! The unwinding lemmas of item 2.11 (Rushby 1992, §5, intransitive policies)
//! and `theorem_cookie_noninterference`, proven from them by induction over
//! traces. See `noninterference.rs` for the statements and the two
//! hypotheses, `projection.rs` and `store_projection.rs` for the cookie
//! facts.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The cookie part of `rel` is unchanged when the jar and time are.
pub open spec fn cookies_agree(rules: Seq<clazel_psl::spec::Rule>, d: crate::domain::Domain, s1: State, s2: State) -> bool {
    d is Root ==> crate::domain::cookies_of_domain(rules, clazel_cookie::storage::spec::evict_expired(s1.jar, s1.now), d) == crate::domain::cookies_of_domain(rules, clazel_cookie::storage::spec::evict_expired(s2.jar, s2.now), d)
}

/// `navigate_tab` from related states, for a tab open in the first: the same
/// outputs, and related states.
pub proof fn lemma_navigate_tab_consistency(
    rules: Seq<clazel_psl::spec::Rule>,
    urls: UrlFns,
    d: crate::domain::Domain,
    s1: State,
    s2: State,
    tab: nat,
    url: Seq<u32>,
    script: Seq<u8>,
)
    requires
        crate::noninterference::rel(rules, urls, d, s1, s2),
        find_by_tab(s1.renderers, tab, 0) is Some,
    ensures
        navigate_tab(urls, s1, tab, url, script).1 == navigate_tab(urls, s2, tab, url, script).1,
        crate::noninterference::rel(rules, urls, d, navigate_tab(urls, s1, tab, url, script).0, navigate_tab(urls, s2, tab, url, script).0),
{
    crate::unwind_base::lemma_found_contained(s1, tab);
    let i1 = find_by_tab(s1.renderers, tab, 0)->Some_0;
    let old = s1.renderers[i1];
    assert(s2.renderers.contains(old));
    crate::unwind_base::lemma_find_contained(urls, s2, old);
    crate::unwind_base::lemma_found_contained(s2, tab);
    let i2 = find_by_tab(s2.renderers, tab, 0)->Some_0;
    assert(s2.renderers[i2] == old);
    crate::invariant::lemma_navigate_tab_wf(rules, urls, s1, tab, url, script);
    crate::invariant::lemma_navigate_tab_wf(rules, urls, s2, tab, url, script);
    let (s1b, o1) = navigate_tab(urls, s1, tab, url, script);
    let (s2b, o2) = navigate_tab(urls, s2, tab, url, script);
    match lock_of_url(urls, url, s1.next_id) {
        None => {},
        Some(lock) => {
            let r = if lock is Tuple && lock == old.lock {
                Renderer { url, ..old }
            } else {
                Renderer { id: s1.next_id, tab, url, lock }
            };
            assert(s1b.renderers == s1.renderers.update(i1, r));
            assert(s2b.renderers == s2.renderers.update(i2, r));
            assert(s1b.jar == s1.jar && s2b.jar == s2.jar && s1b.storage == s1.storage && s2b.storage == s2.storage);
            assert(s1b.now == s1.now && s2b.now == s2.now);
            assert(s1b.next_id == s2b.next_id);
            assert forall|x: Renderer| s1b.renderers.contains(x) implies s2b.renderers.contains(x) by {
                crate::unwind_base::lemma_update_contains(urls, s1.renderers, s1.next_id, i1, r, x);
                crate::unwind_base::lemma_update_contains(urls, s2.renderers, s2.next_id, i2, r, x);
                if s1.renderers.contains(x) {
                    let k = choose|k: int| 0 <= k < s1.renderers.len() && s1.renderers[k] == x;
                    assert(s2.renderers.contains(x));
                }
            }
            assert forall|x: Renderer| s2b.renderers.contains(x) && crate::domain::domain_of_renderer(rules, x) == d implies s1b.renderers.contains(x) by {
                crate::unwind_base::lemma_update_contains(urls, s1.renderers, s1.next_id, i1, r, x);
                crate::unwind_base::lemma_update_contains(urls, s2.renderers, s2.next_id, i2, r, x);
                if s2.renderers.contains(x) && x != r {
                    let k = choose|k: int| 0 <= k < s2.renderers.len() && s2.renderers[k] == x;
                    assert(s1.renderers.contains(x));
                }
            }
            assert forall|i: int| 0 <= i < s1b.renderers.len() implies s2b.renderers.contains(#[trigger] s1b.renderers[i]) by {
                assert(s1b.renderers.contains(s1b.renderers[i]));
            }
            assert forall|i: int| 0 <= i < s2b.renderers.len() && crate::domain::domain_of_renderer(rules, #[trigger] s2b.renderers[i]) == d implies s1b.renderers.contains(
                s2b.renderers[i],
            ) by {
                assert(s2b.renderers.contains(s2b.renderers[i]));
            }
        },
    }
}

/// `rel`, from facts about sets of renderers.
pub proof fn lemma_rel_from_sets(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, d: crate::domain::Domain, s1: State, s2: State)
    requires
        crate::invariant::kernel_wf(rules, urls, s1),
        crate::invariant::kernel_wf(rules, urls, s2),
        forall|x: Renderer| s1.renderers.contains(x) ==> s2.renderers.contains(x),
        forall|x: Renderer| s2.renderers.contains(x) && crate::domain::domain_of_renderer(rules, x) == d ==> s1.renderers.contains(x),
        s1.next_id == s2.next_id,
        s1.now == s2.now,
        cookies_agree(rules, d, s1, s2),
        forall|o: clazel_origin::spec::Origin| o is Tuple && crate::domain::domain_of_lock(rules, o) == d ==> storage_of(s1, o) == storage_of(s2, o),
    ensures
        crate::noninterference::rel(rules, urls, d, s1, s2),
{
    assert forall|i: int| 0 <= i < s1.renderers.len() implies s2.renderers.contains(#[trigger] s1.renderers[i]) by {
        assert(s1.renderers.contains(s1.renderers[i]));
    }
    assert forall|i: int| 0 <= i < s2.renderers.len() && crate::domain::domain_of_renderer(rules, #[trigger] s2.renderers[i]) == d implies s1.renderers.contains(
        s2.renderers[i],
    ) by {
        assert(s2.renderers.contains(s2.renderers[i]));
    }
}

/// `OpenTab` from related states: the same outputs, and related states.
pub proof fn lemma_open_tab_consistency(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, d: crate::domain::Domain, s1: State, s2: State, url: Seq<u32>, script: Seq<u8>)
    requires
        crate::noninterference::rel(rules, urls, d, s1, s2),
    ensures
        open_tab(urls, s1, url, script).1 == open_tab(urls, s2, url, script).1,
        crate::noninterference::rel(rules, urls, d, open_tab(urls, s1, url, script).0, open_tab(urls, s2, url, script).0),
{
    let e = Event::OpenTab { url, script };
    crate::invariant::lemma_step_preserves_wf(rules, urls, s1, e);
    crate::invariant::lemma_step_preserves_wf(rules, urls, s2, e);
    let (s1b, o1) = open_tab(urls, s1, url, script);
    let (s2b, o2) = open_tab(urls, s2, url, script);
    if let Some(lock) = lock_of_url(urls, url, s1.next_id) {
        let rn = Renderer { id: s1.next_id, tab: s1.next_id, url, lock };
        assert forall|x: Renderer| s1b.renderers.contains(x) implies s2b.renderers.contains(x) by {
            crate::unwind_base::lemma_push_contains(s1.renderers, rn, x);
            crate::unwind_base::lemma_push_contains(s2.renderers, rn, x);
            if s1.renderers.contains(x) {
                let k = choose|k: int| 0 <= k < s1.renderers.len() && s1.renderers[k] == x;
            }
        }
        assert forall|x: Renderer| s2b.renderers.contains(x) && crate::domain::domain_of_renderer(rules, x) == d implies s1b.renderers.contains(x) by {
            crate::unwind_base::lemma_push_contains(s1.renderers, rn, x);
            crate::unwind_base::lemma_push_contains(s2.renderers, rn, x);
            if s2.renderers.contains(x) {
                let k = choose|k: int| 0 <= k < s2.renderers.len() && s2.renderers[k] == x;
                assert(s1.renderers.contains(s2.renderers[k]));
            }
        }
        lemma_rel_from_sets(rules, urls, d, s1b, s2b);
    }
}

/// `RendererExited` from related states.
pub proof fn lemma_exited_consistency(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, d: crate::domain::Domain, s1: State, s2: State, id: nat)
    requires
        crate::noninterference::rel(rules, urls, d, s1, s2),
    ensures
        renderer_exited(s1, id).1 == renderer_exited(s2, id).1,
        crate::noninterference::rel(rules, urls, d, renderer_exited(s1, id).0, renderer_exited(s2, id).0),
{
    let e = Event::RendererExited { id };
    crate::invariant::lemma_step_preserves_wf(rules, urls, s1, e);
    crate::invariant::lemma_step_preserves_wf(rules, urls, s2, e);
    let (s1b, o1) = renderer_exited(s1, id);
    let (s2b, o2) = renderer_exited(s2, id);
    crate::unwind_base::lemma_found_contained(s1, id);
    crate::unwind_base::lemma_found_contained(s2, id);
    if let Some(i1) = find_by_id(s1.renderers, id, 0) {
        let x1 = s1.renderers[i1];
        assert(s2.renderers.contains(x1));
        crate::unwind_base::lemma_find_contained(urls, s2, x1);
        let i2 = find_by_id(s2.renderers, id, 0)->Some_0;
        assert(s2.renderers[i2] == x1);
        assert forall|x: Renderer| s1b.renderers.contains(x) implies s2b.renderers.contains(x) by {
            crate::unwind_base::lemma_remove_contains(urls, s1.renderers, s1.next_id, i1, x);
            crate::unwind_base::lemma_remove_contains(urls, s2.renderers, s2.next_id, i2, x);
            let k = choose|k: int| 0 <= k < s1.renderers.len() && s1.renderers[k] == x;
        }
        assert forall|x: Renderer| s2b.renderers.contains(x) && crate::domain::domain_of_renderer(rules, x) == d implies s1b.renderers.contains(x) by {
            crate::unwind_base::lemma_remove_contains(urls, s1.renderers, s1.next_id, i1, x);
            crate::unwind_base::lemma_remove_contains(urls, s2.renderers, s2.next_id, i2, x);
        }
        lemma_rel_from_sets(rules, urls, d, s1b, s2b);
    } else {
        assert(s1b == s1);
        if let Some(i2) = find_by_id(s2.renderers, id, 0) {
            let x2 = s2.renderers[i2];
            assert forall|x: Renderer| s1b.renderers.contains(x) implies s2b.renderers.contains(x) by {
                crate::unwind_base::lemma_remove_contains(urls, s2.renderers, s2.next_id, i2, x);
                let k = choose|k: int| 0 <= k < s1.renderers.len() && s1.renderers[k] == x;
                assert(s2.renderers.contains(x));
                if x.id == x2.id {
                    crate::invariant::lemma_find_by_id(s1.renderers, id, 0);
                    assert(s1.renderers[k].id != id);
                }
            }
            assert forall|x: Renderer| s2b.renderers.contains(x) && crate::domain::domain_of_renderer(rules, x) == d implies s1b.renderers.contains(x) by {
                crate::unwind_base::lemma_remove_contains(urls, s2.renderers, s2.next_id, i2, x);
            }
            lemma_rel_from_sets(rules, urls, d, s1b, s2b);
        }
    }
}

/// `Tick` from related states.
pub proof fn lemma_tick_consistency(rules: Seq<clazel_psl::spec::Rule>, urls: UrlFns, d: crate::domain::Domain, s1: State, s2: State, time: int)
    requires
        crate::noninterference::rel(rules, urls, d, s1, s2),
    ensures
        crate::noninterference::rel(rules, urls, d, tick(s1, time).0, tick(s2, time).0),
{
    let e = Event::Tick { time };
    crate::invariant::lemma_step_preserves_wf(rules, urls, s1, e);
    crate::invariant::lemma_step_preserves_wf(rules, urls, s2, e);
    crate::unwind_base::lemma_jar_no_public_suffix_step(rules, urls, s1, e);
    crate::unwind_base::lemma_jar_no_public_suffix_step(rules, urls, s2, e);
    let (s1b, o1) = tick(s1, time);
    let (s2b, o2) = tick(s2, time);
    let now2 = if time > s1.now { time } else { s1.now };
    if let crate::domain::Domain::Root(root) = d {
        crate::projection::lemma_tick_agree(rules, s1.jar, s2.jar, s1.now, now2, root);
    }
    assert forall|x: Renderer| s1b.renderers.contains(x) implies s2b.renderers.contains(x) by {
        let k = choose|k: int| 0 <= k < s1.renderers.len() && s1.renderers[k] == x;
    }
    lemma_rel_from_sets(rules, urls, d, s1b, s2b);
}

} // verus!
