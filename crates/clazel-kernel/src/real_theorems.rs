//! The isolation theorems of item 2.11 stated for the shipped kernel (item
//! 2.13): the Public Suffix List the kernel runs with ([`crate::contract::psl`]) and the real
//! URL functions ([`crate::urls::real_urls`]), whose exec counterpart is
//! `exec::real_urls::RealUrls`.
//!
//! None of these needs a proof of its own: each theorem is proven for every
//! `rules` and every [`UrlFns`], and a corollary is that theorem at
//! `real_urls()`. They exist so that the guarantee of the shipped kernel is
//! stated, with the real parser, in one place. Each is also the guarantee
//! of `exec::real_urls::step_real`, which is proven to equal `step(psl(),
//! real_urls(), ..)`.
//!
//! What they say of URLs, for the real parser: a renderer's lock is the
//! URL §4.7 origin of the URL parsed from the string the kernel committed
//! (an opaque one replaced by the renderer's id); a `Navigate` from a
//! renderer is resolved by the basic URL parser against the committed URL
//! and committed only by `navigate_tab`; and document.cookie is answered for
//! the lock's scheme and host and the committed URL's path.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// Reachable states of the shipped kernel: from `init_state` by `step` over
/// the Public Suffix List and the real URL functions.
pub open spec fn real_reachable(s: State) -> bool {
    reachable(crate::contract::psl(), crate::urls::real_urls(), s)
}

/// Theorem `theorem_reply_only_to_sender` for the shipped kernel.
pub proof fn corollary_real_reply_only_to_sender(s: State, id: nat, bytes: Seq<u8>)
    requires
        real_reachable(s),
    ensures
        crate::statements::reply_only_to_sender_statement(crate::contract::psl(), crate::urls::real_urls(), s, id, bytes),
{
    crate::theorems::theorem_reply_only_to_sender(crate::contract::psl(), crate::urls::real_urls(), s, id, bytes);
}

/// Theorems `theorem_lock_is_committed_origin` and
/// `theorem_lock_set_only_by_navigation` for the shipped kernel: every
/// renderer's lock is the origin of the URL string it committed, as the real
/// URL parser reads it, and only a navigation sets one.
pub proof fn corollary_real_lock_is_committed_origin(s: State)
    requires
        real_reachable(s),
    ensures
        crate::statements::lock_is_committed_origin_statement(crate::urls::real_urls(), s),
        forall|e: Event| #[trigger] crate::statements::lock_set_only_by_navigation_statement(crate::contract::psl(), crate::urls::real_urls(), s, e),
{
    crate::lock::theorem_lock_is_committed_origin(crate::contract::psl(), crate::urls::real_urls(), s);
}

/// Theorem `theorem_cookie_confidentiality` for the shipped kernel.
pub proof fn corollary_real_cookie_confidentiality(s: State, id: nat, bytes: Seq<u8>)
    requires
        real_reachable(s),
    ensures
        crate::statements::cookie_confidentiality_statement(crate::contract::psl(), crate::urls::real_urls(), s, id, bytes),
{
    crate::cookie_theorems::theorem_cookie_confidentiality(crate::contract::psl(), crate::urls::real_urls(), s, id, bytes);
}

/// Theorem `theorem_cookie_integrity` for the shipped kernel.
pub proof fn corollary_real_cookie_integrity(s: State, e: Event)
    requires
        real_reachable(s),
    ensures
        crate::statements::cookie_integrity_statement(crate::contract::psl(), crate::urls::real_urls(), s, e),
{
    crate::cookie_theorems::theorem_cookie_integrity(crate::contract::psl(), crate::urls::real_urls(), s, e);
}

/// Theorem `theorem_storage_same_origin` for the shipped kernel.
pub proof fn corollary_real_storage_same_origin(s: State, s2: State, id: nat, bytes: Seq<u8>)
    requires
        real_reachable(s),
    ensures
        crate::statements::storage_same_origin_statement(crate::contract::psl(), crate::urls::real_urls(), s, s2, id, bytes),
{
    crate::cookie_theorems::theorem_storage_same_origin(crate::contract::psl(), crate::urls::real_urls(), s, s2, id, bytes);
}

/// Theorem `theorem_cookie_noninterference` for the shipped kernel: the
/// outputs a domain `d` sees from the initial state on a trace in which the
/// user opens the tabs are those of the trace with every event `d` may not
/// see purged.
pub proof fn corollary_real_cookie_noninterference(d: crate::domain::Domain, t: Seq<Event>)
    requires
        crate::noninterference::user_tabs_open(crate::contract::psl(), crate::urls::real_urls(), init_state(), t),
    ensures
        crate::noninterference::run_outputs_for(crate::contract::psl(), crate::urls::real_urls(), d, init_state(), t) == crate::noninterference::run_outputs_for(
            crate::contract::psl(),
            crate::urls::real_urls(),
            d,
            init_state(),
            crate::domain::purge(crate::contract::psl(), crate::urls::real_urls(), d, t),
        ),
{
    crate::ni_theorem::theorem_cookie_noninterference(crate::contract::psl(), crate::urls::real_urls(), d, t);
}

} // verus!
