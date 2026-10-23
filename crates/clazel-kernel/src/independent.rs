//! An independent transcription of two HTML Standard pieces: the
//! `document.cookie` getter and setter (A), and the Web Storage `Storage`
//! interface methods and the `localStorage` getter (B). It was written
//! without reading the kernel's own `spec.rs`, so that comparing the two is a
//! comparison of two readings of the standard.
//!
//! # Sources (read on 23 October 2026)
//!
//! Both fetched as HTML on that date; each carries "Last Updated 22 October
//! 2026":
//! - HTML Standard, <https://html.spec.whatwg.org/multipage/dom.html>,
//!   "The `cookie` attribute" (`#dom-document-cookie`): the definition of a
//!   cookie-averse `Document` and the getter and setter paragraphs.
//! - HTML Standard, <https://html.spec.whatwg.org/multipage/webstorage.html>,
//!   §12.2.1 "The `Storage` interface" (`#the-storage-interface`) and §12.2.3
//!   "The `localStorage` getter" (`#the-localstorage-attribute`).
//! - The cookie algorithms themselves are RFC 6265bis, transcribed in
//!   `clazel_cookie::storage::spec`; they are called, not repeated here.
//!
//! The standard's text carries no step numbers for the `cookie` attribute, so
//! its sentences are numbered `A1.`, `A2.` ... in reading order below. The
//! `Storage` methods are numbered lists in the standard, and the numbers
//! follow it (nested steps as `3.1.`).
//!
//! # Modelling choices
//!
//! - **Strings are octet sequences.** HTML strings are UTF-16 code unit
//!   sequences; the cookie algorithms and this file use `Seq<u8>`. The
//!   getter's "decoded using UTF-8 decode without BOM" and the setter's "the
//!   new value encoded as UTF-8" are the identity on a `Seq<u8>` that already
//!   is UTF-8, which is what the octet model holds. Storage keys and values
//!   are likewise octets; key equality is octet equality, which is the
//!   standard's string equality on UTF-8 images (UTF-8 is injective).
//! - **Exceptions are result values.** "Throw a SecurityError" and "throw a
//!   QuotaExceededError" are the `SecurityError` / `QuotaExceeded` variants of
//!   the result enums below; a call that throws leaves the jar or the map
//!   unchanged. A method that returns nothing returns the new state only.
//! - **`null` is `None`.** `getItem` and `key` return `Option<Seq<u8>>`.
//! - **A top-level document with a browsing context.** The standard lists
//!   "a `Document` object whose browsing context is null" as cookie-averse.
//!   [`Document`] models a document that has one, so only the second
//!   condition, "a `Document` whose URL's scheme is not an HTTP(S) scheme",
//!   is decided ([`cookie_averse`]), from the URL scheme and not the origin.
//!   "An HTTP(S) scheme" is "http" or "https" (Fetch); URL schemes are
//!   already lower case in the octets of `RequestUrl`.
//! - **Top-level document.** `document.cookie` hands RFC 6265bis the
//!   document's "site for cookies" and the "top-level origin"
//!   (`DocumentCall`). For a top-level document both are the document's own
//!   origin, so [`Document`] stores one origin and [`document_call`] uses it
//!   for both.
//! - **The `Document`'s state is just what is read**: its URL as a
//!   `RequestUrl` (scheme, optional canonical host, path) and its origin.
//!   Nothing else of a `Document` is read by the getter or setter.
//! - **Time and eviction come from the cookie model.** The "current date and
//!   time" is the `now: int` argument; the getter's jar update (expired
//!   cookies evicted, last-access times updated) is `jar_after_retrieval`
//!   and the setter's jar is `store_a_set_cookie_string`. Both are the
//!   cookie crate's definitions, called with a `NonHttp` context.
//! - **The map is an ordered list of entries.** An Infra ordered map is "a
//!   map whose keys are ordered"; [`StorageMap`] is a `Seq<Entry>` with
//!   unique keys ([`map_keys_unique`]), the sequence order being the map
//!   order. `map[key]` exists iff some entry has that key. "Set map[key] to
//!   value" replaces the value in place if the key exists and appends a new
//!   entry otherwise (Infra "set"); "remove map[key]" deletes that entry; "get
//!   the keys" lists the keys in map order; "size" is the number of entries.
//! - **"Reorder" is the identity.** "To reorder a Storage object storage,
//!   reorder storage's map's entries in an implementation-defined manner."
//!   Keeping the order is one allowed implementation, so [`reorder`] is the
//!   identity, and the lemmas about order hold for it. A kernel may choose
//!   any other permutation; the standard says iteration order "is not defined
//!   and can change upon most mutations".
//! - **"Cannot be stored" is a size limit.** The standard leaves it
//!   implementation-defined. Here a map can be stored iff the total octet
//!   length of all keys plus all values is at most `limit` ([`can_be_stored`]),
//!   tested on the map as it would be after the change, at the step the
//!   standard tests it.
//! - **Broadcast is not modelled.** The "Broadcast this with key, oldValue,
//!   and newValue" steps (setItem step 7, removeItem step 5, clear step 3)
//!   queue `storage` events on other Windows; they change no `Storage`'s map,
//!   so the map-and-result functions are unaffected. `oldValue` is therefore
//!   only used for the step 3.2 comparison.
//! - **`localStorage` access is origin-only.** The getter throws a
//!   SecurityError "if the Document's origin is an opaque origin"
//!   ([`local_storage_access`]); the other cause the standard names, a user
//!   agent policy decision, and the "local storage holder" caching (the same
//!   Storage object returned each time) are not modelled: which map an
//!   allowed origin gets is the caller's business (a map keyed by origin).
//! - **The `sessionStorage` getter and the `Storage` named-property
//!   behaviour** (supported property names, `storage[key]`) are not modelled;
//!   the former is the same shape as `localStorage`, the latter reduces to
//!   `getItem`/`setItem`/`removeItem`.

#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// =====================================================================
// A. The `cookie` attribute of `Document`.
// https://html.spec.whatwg.org/multipage/dom.html#dom-document-cookie
// =====================================================================

/// What the `cookie` getter and setter read of a top-level `Document`.
pub struct Document {
    /// "the document's URL" (scheme octets, canonical host if any, path).
    pub url: clazel_cookie::storage::spec::RequestUrl,
    /// "the Document's origin".
    pub origin: clazel_origin::spec::Origin,
}

/// The getter's outcome: a string, or a thrown exception.
pub enum CookieGetResult {
    /// The returned string (an octet sequence, see the modelling choices).
    Value(Seq<u8>),
    /// "the user agent must throw a "SecurityError" DOMException".
    SecurityError,
}

/// The setter's outcome: it returns nothing, or throws.
pub enum CookieSetResult {
    /// The setter completed (possibly "do nothing").
    Done,
    /// "the user agent must throw a "SecurityError" DOMException".
    SecurityError,
}

/// The octets of "http".
pub open spec fn scheme_http() -> Seq<u8> {
    seq![0x68u8, 0x74, 0x74, 0x70]
}

/// The octets of "https".
pub open spec fn scheme_https() -> Seq<u8> {
    seq![0x68u8, 0x74, 0x74, 0x70, 0x73]
}

/// "An HTTP(S) scheme is "http" or "https"."
pub open spec fn is_http_or_https_scheme(scheme: Seq<u8>) -> bool {
    scheme == scheme_http() || scheme == scheme_https()
}

/// "A `Document` object that falls into one of the following conditions is a
/// cookie-averse `Document` object: A `Document` object whose browsing
/// context is null. A `Document` whose URL's scheme is not an HTTP(S)
/// scheme." (The first condition is false for [`Document`], see the header.)
pub open spec fn cookie_averse(doc: Document) -> bool {
    !is_http_or_https_scheme(doc.url.scheme)
}

/// "the Document's origin is an opaque origin".
pub open spec fn origin_is_opaque(origin: clazel_origin::spec::Origin) -> bool {
    origin is Opaque
}

/// The `DocumentCall` for a top-level document: its site for cookies and
/// the top-level origin are both its own origin.
pub open spec fn document_call(doc: Document) -> clazel_cookie::storage::spec::DocumentCall {
    clazel_cookie::storage::spec::DocumentCall { site_for_cookies: doc.origin, top_level_origin: doc.origin }
}

/// The context of "a "non-HTTP" API" call from `doc`.
pub open spec fn non_http_context(doc: Document) -> clazel_cookie::storage::spec::RequestContext {
    clazel_cookie::storage::spec::RequestContext::NonHttp(document_call(doc))
}

/// The `document.cookie` getter, with the jar after the call.
///
/// A1. "On getting, if the document is a cookie-averse Document object, then
///     the user agent must return the empty string."
/// A2. "Otherwise, if the Document's origin is an opaque origin, the user
///     agent must throw a "SecurityError" DOMException."
/// A3. "Otherwise, the user agent must return the cookie-string for the
///     document's URL for a "non-HTTP" API, decoded using UTF-8 decode
///     without BOM."
///
/// In A1 and A2 the jar is unchanged. In A3 the retrieval (RFC 6265bis §5.8)
/// also updates last-access times and drops expired cookies.
pub open spec fn document_cookie_get(
    rules: Seq<clazel_psl::spec::Rule>,
    doc: Document,
    jar: Seq<clazel_cookie::storage::spec::Cookie>,
    now: int,
) -> (CookieGetResult, Seq<clazel_cookie::storage::spec::Cookie>) {
    if cookie_averse(doc) {
        // A1.
        (CookieGetResult::Value(seq![]), jar)
    } else if origin_is_opaque(doc.origin) {
        // A2.
        (CookieGetResult::SecurityError, jar)
    } else {
        // A3. (UTF-8 decode of octets that are UTF-8: the identity.)
        (
            CookieGetResult::Value(clazel_cookie::storage::spec::retrieve_cookie_string(rules, jar, doc.url, non_http_context(doc), now)),
            clazel_cookie::storage::spec::jar_after_retrieval(rules, jar, doc.url, non_http_context(doc), now),
        )
    }
}

/// The `document.cookie` setter, with the jar after the call.
///
/// A4. "On setting, if the document is a cookie-averse Document object, then
///     the user agent must do nothing."
/// A5. "Otherwise, if the Document's origin is an opaque origin, the user
///     agent must throw a "SecurityError" DOMException."
/// A6. "Otherwise, the user agent must act as it would when receiving a
///     set-cookie-string for the document's URL via a "non-HTTP" API,
///     consisting of the new value encoded as UTF-8."
pub open spec fn document_cookie_set(
    rules: Seq<clazel_psl::spec::Rule>,
    doc: Document,
    jar: Seq<clazel_cookie::storage::spec::Cookie>,
    new_value: Seq<u8>,
    now: int,
) -> (CookieSetResult, Seq<clazel_cookie::storage::spec::Cookie>) {
    if cookie_averse(doc) {
        // A4.
        (CookieSetResult::Done, jar)
    } else if origin_is_opaque(doc.origin) {
        // A5.
        (CookieSetResult::SecurityError, jar)
    } else {
        // A6. (UTF-8 encode of octets that are UTF-8: the identity.)
        (
            CookieSetResult::Done,
            clazel_cookie::storage::spec::store_a_set_cookie_string(rules, jar, new_value, doc.url, non_http_context(doc), now),
        )
    }
}

// =====================================================================
// B. Web Storage.
// https://html.spec.whatwg.org/multipage/webstorage.html#the-storage-interface
// =====================================================================

/// One entry of a Storage object's map: a string key and a string value.
pub struct Entry {
    /// The key.
    pub key: Seq<u8>,
    /// The value.
    pub value: Seq<u8>,
}

/// A Storage object's "map": "A storage proxy map" (an ordered map of
/// string keys to string values), as its entries in map order.
pub struct StorageMap {
    /// The entries, in order.
    pub entries: Seq<Entry>,
}

/// The outcome of `setItem`.
pub enum SetItemResult {
    /// The call returned (including the early return of step 3.2).
    Done,
    /// "throw a QuotaExceededError"; the map is unchanged.
    QuotaExceeded,
}

/// Infra ordered map invariant: no two entries have the same key.
pub open spec fn map_keys_unique(map: StorageMap) -> bool {
    forall|i: int, j: int| #![auto]
        0 <= i < map.entries.len() && 0 <= j < map.entries.len() && i != j ==> map.entries[i].key
            != map.entries[j].key
}

/// The index of the entry with `key`, searching from `i`.
pub open spec fn find_key_from(entries: Seq<Entry>, key: Seq<u8>, i: nat) -> Option<nat>
    decreases entries.len() - i,
{
    if i >= entries.len() {
        None
    } else if entries[i as int].key == key {
        Some(i)
    } else {
        find_key_from(entries, key, (i + 1) as nat)
    }
}

/// The index of the entry with `key`, if any.
pub open spec fn find_key(map: StorageMap, key: Seq<u8>) -> Option<nat> {
    find_key_from(map.entries, key, 0)
}

/// Infra: "map[key] exists" is "map contains key".
pub open spec fn map_exists(map: StorageMap, key: Seq<u8>) -> bool {
    find_key(map, key) is Some
}

/// Infra: "map[key]", for a key that exists.
pub open spec fn map_get(map: StorageMap, key: Seq<u8>) -> Seq<u8>
    recommends
        map_exists(map, key),
{
    map.entries[find_key(map, key).unwrap() as int].value
}

/// Infra "set": "map[key] = value": update the value if the key exists,
/// else append.
pub open spec fn map_set(map: StorageMap, key: Seq<u8>, value: Seq<u8>) -> StorageMap {
    match find_key(map, key) {
        Some(i) => StorageMap { entries: map.entries.update(i as int, Entry { key, value }) },
        None => StorageMap { entries: map.entries.push(Entry { key, value }) },
    }
}

/// Infra "remove": "remove map[key]".
pub open spec fn map_remove(map: StorageMap, key: Seq<u8>) -> StorageMap {
    match find_key(map, key) {
        Some(i) => StorageMap { entries: map.entries.remove(i as int) },
        None => map,
    }
}

/// Infra "get the keys": "the keys of map, in order".
pub open spec fn get_the_keys(map: StorageMap) -> Seq<Seq<u8>> {
    map.entries.map_values(|e: Entry| e.key)
}

/// "To reorder a Storage object storage, reorder storage's map's entries in
/// an implementation-defined manner." Modelled as the identity (see the
/// header).
pub open spec fn reorder(map: StorageMap) -> StorageMap {
    map
}

/// The total octet length of every key and value in `entries`.
pub open spec fn entries_size(entries: Seq<Entry>) -> nat
    decreases entries.len(),
{
    if entries.len() == 0 {
        0
    } else {
        let last = entries[entries.len() - 1];
        entries_size(entries.drop_last()) + last.key.len() + last.value.len()
    }
}

/// "value cannot be stored" (implementation-defined, see the header): the
/// map after the change would be over `limit` octets.
pub open spec fn map_over_limit(map: StorageMap, limit: nat) -> bool {
    entries_size(map.entries) > limit
}

/// "can be stored": the total octet length of keys and values is at most
/// `limit`.
pub open spec fn can_be_stored(map: StorageMap, limit: nat) -> bool {
    !map_over_limit(map, limit)
}

/// The `length` getter. "The length getter steps are to return this's map's
/// size."
pub open spec fn storage_length(map: StorageMap) -> nat {
    map.entries.len()
}

/// The `key(index)` method.
///
/// 1. "If index is greater than or equal to this's map's size, then return
///    null."
/// 2. "Let keys be the result of running get the keys on this's map."
/// 3. "Return keys[index]."
pub open spec fn storage_key(map: StorageMap, index: nat) -> Option<Seq<u8>> {
    if index >= map.entries.len() {
        // 1.
        None
    } else {
        // 2.
        let keys = get_the_keys(map);
        // 3.
        Some(keys[index as int])
    }
}

/// The `getItem(key)` method.
///
/// 1. "If this's map[key] does not exist, then return null."
/// 2. "Return this's map[key]."
pub open spec fn storage_get_item(map: StorageMap, key: Seq<u8>) -> Option<Seq<u8>> {
    if !map_exists(map, key) {
        // 1.
        None
    } else {
        // 2.
        Some(map_get(map, key))
    }
}

/// `setItem` from step 4 on, given the `reorder` variable fixed by steps 2
/// and 3.
///
/// 4. "If value cannot be stored, then throw a QuotaExceededError."
/// 5. "Set this's map[key] to value."
/// 6. "If reorder is true, then reorder this."
/// 7. "Broadcast this with key, oldValue, and value." (Not modelled.)
pub open spec fn set_item_from_step_4(
    map: StorageMap,
    key: Seq<u8>,
    value: Seq<u8>,
    limit: nat,
    reorder_flag: bool,
) -> (StorageMap, SetItemResult) {
    // The map step 5 would produce, computed first so that step 4 can test
    // it (a throw leaves `map` as it was).
    let after = map_set(map, key, value);
    if !can_be_stored(after, limit) {
        // 4.
        (map, SetItemResult::QuotaExceeded)
    } else if reorder_flag {
        // 5, 6.
        (reorder(after), SetItemResult::Done)
    } else {
        // 5.
        (after, SetItemResult::Done)
    }
}

/// The `setItem(key, value)` method.
///
/// 1. "Let oldValue be null."
/// 2. "Let reorder be true."
/// 3. "If this's map[key] exists:"
///    3.1. "Set oldValue to this's map[key]."
///    3.2. "If oldValue is value, then return."
///    3.3. "Set reorder to false."
/// 4-7. see [`set_item_from_step_4`].
pub open spec fn storage_set_item(
    map: StorageMap,
    key: Seq<u8>,
    value: Seq<u8>,
    limit: nat,
) -> (StorageMap, SetItemResult) {
    // 1. oldValue = null (None).
    // 2. reorder = true.
    if map_exists(map, key) {
        // 3.1.
        let old_value = map_get(map, key);
        if old_value == value {
            // 3.2.
            (map, SetItemResult::Done)
        } else {
            // 3.3. reorder = false.
            set_item_from_step_4(map, key, value, limit, false)
        }
    } else {
        set_item_from_step_4(map, key, value, limit, true)
    }
}

/// The `removeItem(key)` method.
///
/// 1. "If this's map[key] does not exist, then return."
/// 2. "Set oldValue to this's map[key]."
/// 3. "Remove this's map[key]."
/// 4. "Reorder this."
/// 5. "Broadcast this with key, oldValue, and null." (Not modelled.)
pub open spec fn storage_remove_item(map: StorageMap, key: Seq<u8>) -> StorageMap {
    if !map_exists(map, key) {
        // 1.
        map
    } else {
        // 2. oldValue = map[key] (only used by the broadcast).
        // 3.
        let removed = map_remove(map, key);
        // 4.
        reorder(removed)
    }
}

/// The `clear()` method.
///
/// 1. "If this's map is empty, then return."
/// 2. "Clear this's map."
/// 3. "Broadcast this with null, null, and null." (Not modelled.)
pub open spec fn storage_clear(map: StorageMap) -> StorageMap {
    if map.entries.len() == 0 {
        // 1.
        map
    } else {
        // 2.
        StorageMap { entries: seq![] }
    }
}

/// The outcome of the `localStorage` getter.
pub enum StorageAccess {
    /// The Storage object for the origin is returned.
    Allowed,
    /// "throw a "SecurityError" DOMException".
    SecurityError,
}

/// The `localStorage` getter's origin check (§12.2.3): "Throws a
/// "SecurityError" DOMException if the Document's origin is an opaque
/// origin".
pub open spec fn local_storage_access(origin: clazel_origin::spec::Origin) -> StorageAccess {
    if origin_is_opaque(origin) {
        StorageAccess::SecurityError
    } else {
        StorageAccess::Allowed
    }
}

// =====================================================================
// Examples.
// =====================================================================

/// The octets "a".
pub open spec fn k_a() -> Seq<u8> {
    seq![0x61u8]
}

/// The octets "b".
pub open spec fn k_b() -> Seq<u8> {
    seq![0x62u8]
}

/// The octets "1".
pub open spec fn v_1() -> Seq<u8> {
    seq![0x31u8]
}

/// The octets "2".
pub open spec fn v_2() -> Seq<u8> {
    seq![0x32u8]
}

/// The empty map.
pub open spec fn empty_map() -> StorageMap {
    StorageMap { entries: seq![] }
}

/// No entry from `i` on has `key`, so the search finds nothing.
pub proof fn lemma_find_key_absent(entries: Seq<Entry>, key: Seq<u8>, i: nat)
    requires
        forall|j: int| #![auto] i <= j < entries.len() ==> entries[j].key != key,
    ensures
        find_key_from(entries, key, i) is None,
    decreases entries.len() - i,
{
    if i < entries.len() {
        lemma_find_key_absent(entries, key, (i + 1) as nat);
    }
}

/// "a" and "b" differ.
pub proof fn lemma_ka_ne_kb()
    ensures
        k_a() != k_b(),
{
    assert(k_a()[0] != k_b()[0]);
}

/// setItem then getItem returns the value, and the length grows.
pub proof fn example_set_then_get()
    ensures
        ({
            let (m, r) = storage_set_item(empty_map(), k_a(), v_1(), 10);
            r is Done && storage_get_item(m, k_a()) == Some(v_1()) && storage_length(m) == 1
                && storage_get_item(m, k_b()) is None
        }),
{
    let (m, r) = storage_set_item(empty_map(), k_a(), v_1(), 10);
    reveal_with_fuel(entries_size, 3);
    assert(m.entries =~= seq![Entry { key: k_a(), value: v_1() }]);
    assert(find_key(m, k_a()) == Some(0nat));
    lemma_ka_ne_kb();
    assert(forall|j: int| #![auto] 0 <= j < m.entries.len() ==> m.entries[j].key != k_b());
    lemma_find_key_absent(m.entries, k_b(), 0);
}

/// setItem on an existing key keeps its position and replaces the value.
pub proof fn example_set_existing_keeps_position()
    ensures
        ({
            let (m1, _) = storage_set_item(empty_map(), k_a(), v_1(), 10);
            let (m2, _) = storage_set_item(m1, k_b(), v_1(), 10);
            let (m3, r) = storage_set_item(m2, k_a(), v_2(), 10);
            r is Done && get_the_keys(m3) =~= seq![k_a(), k_b()] && storage_get_item(m3, k_a())
                == Some(v_2()) && storage_key(m3, 0) == Some(k_a()) && storage_key(m3, 1) == Some(
                k_b(),
            ) && storage_key(m3, 2) is None
        }),
{
    reveal_with_fuel(entries_size, 4);
    let (m1, _) = storage_set_item(empty_map(), k_a(), v_1(), 10);
    assert(m1.entries =~= seq![Entry { key: k_a(), value: v_1() }]);
    lemma_ka_ne_kb();
    assert(forall|j: int| #![auto] 0 <= j < m1.entries.len() ==> m1.entries[j].key != k_b());
    lemma_find_key_absent(m1.entries, k_b(), 0);
    let (m2, _) = storage_set_item(m1, k_b(), v_1(), 10);
    assert(m2.entries =~= seq![Entry { key: k_a(), value: v_1() }, Entry { key: k_b(), value: v_1() }]);
    assert(find_key(m2, k_a()) == Some(0nat));
    let (m3, r) = storage_set_item(m2, k_a(), v_2(), 10);
    assert(m3.entries =~= seq![Entry { key: k_a(), value: v_2() }, Entry { key: k_b(), value: v_1() }]);
    assert(find_key(m3, k_a()) == Some(0nat));
    assert(get_the_keys(m3) =~= seq![k_a(), k_b()]);
}

/// Setting the value a key already has changes nothing (step 3.2), even when
/// the map is exactly at the limit.
pub proof fn example_set_same_value_is_noop()
    ensures
        ({
            let (m1, _) = storage_set_item(empty_map(), k_a(), v_1(), 2);
            let (m2, r) = storage_set_item(m1, k_a(), v_1(), 0);
            r is Done && m2 == m1
        }),
{
    reveal_with_fuel(entries_size, 3);
    let (m1, _) = storage_set_item(empty_map(), k_a(), v_1(), 2);
    assert(m1.entries =~= seq![Entry { key: k_a(), value: v_1() }]);
    assert(find_key(m1, k_a()) == Some(0nat));
}

/// A setItem that would exceed the limit throws and leaves the map alone.
pub proof fn example_quota_exceeded()
    ensures
        ({
            let (m1, _) = storage_set_item(empty_map(), k_a(), v_1(), 3);
            let (m2, r) = storage_set_item(m1, k_b(), v_1(), 3);
            r is QuotaExceeded && m2 == m1
        }),
{
    reveal_with_fuel(entries_size, 4);
    let (m1, _) = storage_set_item(empty_map(), k_a(), v_1(), 3);
    assert(m1.entries =~= seq![Entry { key: k_a(), value: v_1() }]);
    lemma_ka_ne_kb();
    assert(forall|j: int| #![auto] 0 <= j < m1.entries.len() ==> m1.entries[j].key != k_b());
    lemma_find_key_absent(m1.entries, k_b(), 0);
    let after = map_set(m1, k_b(), v_1());
    assert(after.entries =~= seq![Entry { key: k_a(), value: v_1() }, Entry { key: k_b(), value: v_1() }]);
    assert(after.entries.drop_last() =~= m1.entries);
    assert(m1.entries.drop_last() =~= seq![]);
    assert(entries_size(after.entries) == 4);
}

/// removeItem deletes the entry and keeps the others in order; removing a
/// missing key and clearing an empty map are no-ops; clear empties.
pub proof fn example_remove_and_clear()
    ensures
        ({
            let (m1, _) = storage_set_item(empty_map(), k_a(), v_1(), 10);
            let (m2, _) = storage_set_item(m1, k_b(), v_2(), 10);
            let m3 = storage_remove_item(m2, k_a());
            storage_get_item(m3, k_a()) is None && storage_get_item(m3, k_b()) == Some(v_2())
                && storage_length(m3) == 1 && storage_remove_item(m3, k_a()) == m3
                && storage_clear(m3) == empty_map() && storage_clear(empty_map()) == empty_map()
        }),
{
    reveal_with_fuel(entries_size, 4);
    let (m1, _) = storage_set_item(empty_map(), k_a(), v_1(), 10);
    assert(m1.entries =~= seq![Entry { key: k_a(), value: v_1() }]);
    lemma_ka_ne_kb();
    assert(forall|j: int| #![auto] 0 <= j < m1.entries.len() ==> m1.entries[j].key != k_b());
    lemma_find_key_absent(m1.entries, k_b(), 0);
    let (m2, _) = storage_set_item(m1, k_b(), v_2(), 10);
    assert(m2.entries =~= seq![Entry { key: k_a(), value: v_1() }, Entry { key: k_b(), value: v_2() }]);
    assert(find_key(m2, k_a()) == Some(0nat));
    let m3 = storage_remove_item(m2, k_a());
    assert(m3.entries =~= seq![Entry { key: k_b(), value: v_2() }]);
    lemma_ka_ne_kb();
    assert(forall|j: int| #![auto] 0 <= j < m3.entries.len() ==> m3.entries[j].key != k_a());
    lemma_find_key_absent(m3.entries, k_a(), 0);
    assert(find_key(m3, k_b()) == Some(0nat));
    assert(storage_clear(m3).entries =~= seq![]);
}

/// A document with a `file` URL is cookie-averse: the getter returns the
/// empty string and the setter does nothing, even with an opaque origin.
pub proof fn example_cookie_averse(
    rules: Seq<clazel_psl::spec::Rule>,
    jar: Seq<clazel_cookie::storage::spec::Cookie>,
    new_value: Seq<u8>,
    now: int,
)
    ensures
        ({
            let doc = Document {
                url: clazel_cookie::storage::spec::RequestUrl { scheme: seq![0x66u8, 0x69, 0x6C, 0x65], host: None, path: seq![0x2Fu8] },
                origin: clazel_origin::spec::Origin::Opaque(0),
            };
            document_cookie_get(rules, doc, jar, now) == (CookieGetResult::Value(seq![]), jar)
                && document_cookie_set(rules, doc, jar, new_value, now) == (CookieSetResult::Done, jar)
        }),
{
    let scheme = seq![0x66u8, 0x69, 0x6C, 0x65];
    assert(scheme != scheme_http() && scheme != scheme_https()) by {
        assert(scheme[0] != scheme_http()[0]);
        assert(scheme[0] != scheme_https()[0]);
    }
}

/// An `https` document with an opaque origin throws a SecurityError from both
/// the getter and the setter, and leaves the jar alone.
pub proof fn example_opaque_origin_throws(
    rules: Seq<clazel_psl::spec::Rule>,
    jar: Seq<clazel_cookie::storage::spec::Cookie>,
    new_value: Seq<u8>,
    now: int,
)
    ensures
        ({
            let doc = Document {
                url: clazel_cookie::storage::spec::RequestUrl { scheme: scheme_https(), host: None, path: seq![0x2Fu8] },
                origin: clazel_origin::spec::Origin::Opaque(7),
            };
            document_cookie_get(rules, doc, jar, now) == (CookieGetResult::SecurityError, jar)
                && document_cookie_set(rules, doc, jar, new_value, now) == (CookieSetResult::SecurityError, jar)
                && local_storage_access(doc.origin) == StorageAccess::SecurityError
        }),
{
}

} // verus!
