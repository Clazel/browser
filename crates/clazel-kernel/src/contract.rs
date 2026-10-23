//! Contracts the executable kernel (item 2.12, not yet written) must be
//! proven to meet. Each exec function's `ensures` clause is exactly one of
//! these predicates, so reviewing these (and [`super::spec`]) is enough to
//! know what the implementation guarantees.
//!
//! The exec `step` is pure: no I/O, no clock, no processes. Bytes, renderer
//! ids and the time come in as arguments, as the host shell (item 2.15)
//! gets them, and the outputs go out as a value for the host to act on. An
//! exec `State` is viewed as a [`State`] (renderers, jar, storage maps,
//! counter, time) and an exec event and output as an [`Event`] and
//! [`Output`]; the exec jar is the view of `clazel-cookie`'s (item 2.9),
//! with its times `u64`s, hence `jar_in_range`. Ids are `u64`s, hence
//! `next_id` below `u64::MAX`.
//!
//! Every contract is about the Public Suffix List the generated tables hold
//! (`clazel_psl::table::psl_rules()`), as `clazel-cookie`'s are, and for a
//! given [`UrlFns`] `urls`: the spec view of the exec URL functions. Item
//! 2.12 proves the exec `step` for any implementation of them whose view is
//! `urls` (so the kernel proofs never unfold the URL parser), and item 2.13
//! supplies the real one. The isolation theorems hold for every `urls`, so
//! the contract assumes nothing about them.
//!
//! The exec `step` also needs the facts of [`super::spec`] that are not
//! about a single call and that its caller keeps: `kernel_wf` of the state it
//! passes, which `lemma_step_preserves_wf` shows `step` preserves, so the
//! host loop establishes it once, from [`super::spec::init_state`]
//! (`lemma_init_wf`). `jar_in_range` and `now_in_range` of the state hold of
//! every state the exec `step` returns because its jar and time are `u64`s
//! that the exec cookie functions keep in range (their contracts); 2.12
//! proves it. One more obligation falls to 2.12: the spec casts a storage
//! map's length to `u64` (`StorageLength`), which is exact because a map
//! within its quota (`within_quota`) has far fewer than 2^64 entries.

#[allow(unused_imports)]
use super::spec::*;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

/// The Public Suffix List the kernel runs with.
pub open spec fn psl() -> Seq<clazel_psl::spec::Rule> {
    clazel_psl::table::psl_rules()
}

/// Precondition of `step(&State, &Event) -> (State, Vec<Output>)`: the state
/// is well formed (`kernel_wf`); its jar and time are in the range of the
/// exec cookie functions; the next id fits a `u64` with room for one more;
/// and a `Tick` carries a time in that range. (The id in `FromRenderer` and
/// the tab in `NavigateTab` are `u64`s, so they fit.)
pub open spec fn step_requires(urls: UrlFns, s: State, e: Event) -> bool {
    &&& super::invariant::kernel_wf(psl(), urls, s)
    &&& clazel_cookie::storage::contract::jar_in_range(s.jar)
    &&& clazel_cookie::set_cookie::contract::now_in_range(s.now)
    &&& s.next_id < 0xFFFF_FFFF_FFFF_FFFFnat
    &&& (e is Tick ==> clazel_cookie::set_cookie::contract::now_in_range(e->Tick_time))
}

/// Contract for `step(&State, &Event) -> (State, Vec<Output>)`: the state
/// and outputs of the spec's `step`.
pub open spec fn step_ensures(urls: UrlFns, s: State, e: Event, output: (State, Seq<Output>)) -> bool {
    output == step(psl(), urls, s, e)
}

/// Contract for `decode_renderer_frame(&[u8]) -> Option<Message>`: the
/// message in a frame a renderer sent, or `None` if the frame does not decode
/// or holds a message only the kernel may send. Whole frames, header
/// included.
pub open spec fn decode_renderer_frame_ensures(bytes: Seq<u8>, output: Option<clazel_ipc::message::spec::Message>) -> bool {
    output == decode_renderer_frame(bytes)
}

/// Contract for `reply_frame(&Message) -> Vec<u8>`: the frame of the
/// message, or the frame of `Error { error_encode }` if the message cannot
/// be sent (a text that is not UTF-8, or a payload over `MAX_FRAME`). Always
/// a whole frame within `MAX_FRAME`.
pub open spec fn reply_frame_ensures(m: clazel_ipc::message::spec::Message, output: Seq<u8>) -> bool {
    output == reply_frame(m)
}

/// Contract for `commit_frame(&[u32], &[u8]) -> Vec<u8>`: the frame of a
/// `Commit` of the URL (encoded as UTF-8) running the script.
pub open spec fn commit_frame_ensures(url: Seq<u32>, script: Seq<u8>, output: Seq<u8>) -> bool {
    output == commit_frame(url, script)
}

} // verus!
