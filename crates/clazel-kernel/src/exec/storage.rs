//! Web Storage over the exec buckets (HTML §12.2.1): `setItem`, `removeItem`
//! and `clear` as functions of the bucket vector, each proven equal to the
//! corresponding case of [`crate::spec::storage_call`] on the view.

use super::locks::*;
use super::records::*;
#[allow(unused_imports)]
use super::spec::*;
use clazel_cookie::strings::slice_eq;
use clazel_origin::exec::ParsedOrigin;
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------
// Spec: the storage calls as functions of the map.
// ---------------------------------------------------------------------

/// The octets of one entry.
pub open spec fn entry_size(e: StorageEntry) -> nat {
    e.key.len() + e.value.len()
}

/// The map of `lock` in the storage map `m` (empty if it has none).
pub open spec fn list_in(m: Map<clazel_origin::spec::Origin, Seq<StorageEntry>>, lock: clazel_origin::spec::Origin) -> Seq<StorageEntry> {
    if m.dom().contains(lock) {
        m[lock]
    } else {
        seq![]
    }
}

/// The storage map `m` with the list of `lock` replaced by `list` (an empty
/// list removes it): the storage field of [`set_storage`].
pub open spec fn set_map(m: Map<clazel_origin::spec::Origin, Seq<StorageEntry>>, lock: clazel_origin::spec::Origin, list: Seq<StorageEntry>) -> Map<
    clazel_origin::spec::Origin,
    Seq<StorageEntry>,
> {
    if list.len() == 0 {
        m.remove(lock)
    } else {
        m.insert(lock, list)
    }
}

/// `setItem(key, value)` on the storage map `m`: the new map, and whether the
/// quota is exceeded (then the map is unchanged).
pub open spec fn set_item_map(m: Map<clazel_origin::spec::Origin, Seq<StorageEntry>>, lock: clazel_origin::spec::Origin, key: Seq<u8>, value: Seq<u8>) -> (Map<
    clazel_origin::spec::Origin,
    Seq<StorageEntry>,
>, bool) {
    let list = list_in(m, lock);
    match find_key(list, key, 0) {
        Some(i) => if list[i].value == value {
            (m, false)
        } else {
            let new_list = list.update(i, StorageEntry { key, value });
            if within_quota(new_list) {
                (set_map(m, lock, new_list), false)
            } else {
                (m, true)
            }
        },
        None => {
            let new_list = list.push(StorageEntry { key, value });
            if within_quota(new_list) {
                (set_map(m, lock, new_list), false)
            } else {
                (m, true)
            }
        },
    }
}

/// `removeItem(key)` on the storage map `m`.
pub open spec fn remove_item_map(m: Map<clazel_origin::spec::Origin, Seq<StorageEntry>>, lock: clazel_origin::spec::Origin, key: Seq<u8>) -> Map<
    clazel_origin::spec::Origin,
    Seq<StorageEntry>,
> {
    let list = list_in(m, lock);
    match find_key(list, key, 0) {
        None => m,
        Some(i) => set_map(m, lock, list.remove(i)),
    }
}

// ---------------------------------------------------------------------
// Lemmas on sizes.
// ---------------------------------------------------------------------

/// The size of a prefix depends only on the entries in it.
pub proof fn lemma_size_prefix(a: Seq<StorageEntry>, b: Seq<StorageEntry>, n: nat)
    requires
        n <= a.len(),
        n <= b.len(),
        forall|i: int| 0 <= i < n ==> a[i] == b[i],
    ensures
        entries_size(a, n) == entries_size(b, n),
    decreases n,
{
    if n > 0 {
        lemma_size_prefix(a, b, (n - 1) as nat);
    }
}

/// A prefix is no larger than a longer prefix.
pub proof fn lemma_size_mono(list: Seq<StorageEntry>, n: nat, m: nat)
    requires
        n <= m <= list.len(),
    ensures
        entries_size(list, n) <= entries_size(list, m),
    decreases m,
{
    if n < m {
        lemma_size_mono(list, n, (m - 1) as nat);
    }
}

/// An entry's octets are within the size of any prefix containing it.
pub proof fn lemma_size_ge_entry(list: Seq<StorageEntry>, n: nat, i: int)
    requires
        0 <= i < n <= list.len(),
    ensures
        entries_size(list, n) >= entry_size(list[i]),
    decreases n,
{
    if i < n - 1 {
        lemma_size_ge_entry(list, (n - 1) as nat, i);
    }
}

/// Pushing an entry adds its size.
pub proof fn lemma_size_push(list: Seq<StorageEntry>, e: StorageEntry)
    ensures
        entries_size(list.push(e), list.len() + 1) == entries_size(list, list.len()) + entry_size(e),
{
    let p = list.push(e);
    lemma_size_prefix(p, list, list.len());
    assert(p[list.len() as int] == e);
}

/// Updating entry `i` swaps its size.
pub proof fn lemma_size_update(list: Seq<StorageEntry>, i: int, e: StorageEntry, n: nat)
    requires
        0 <= i < list.len(),
        n <= list.len(),
    ensures
        entries_size(list.update(i, e), n) + (if i < n { entry_size(list[i]) } else { 0 }) == entries_size(list, n) + (if i
            < n { entry_size(e) } else { 0 }),
    decreases n,
{
    if n > 0 {
        lemma_size_update(list, i, e, (n - 1) as nat);
        assert(list.update(i, e)[n - 1] == if n - 1 == i { e } else { list[n - 1 as int] });
    }
}

/// Pushing a key that fits keeps the list in quota exactly when the sum is.
pub proof fn lemma_quota_push(list: Seq<StorageEntry>, e: StorageEntry)
    ensures
        within_quota(list.push(e)) == (entries_size(list, list.len()) + entry_size(e) <= max_storage_size()),
{
    lemma_size_push(list, e);
}

/// Updating an entry: the new size.
pub proof fn lemma_quota_update(list: Seq<StorageEntry>, i: int, e: StorageEntry)
    requires
        0 <= i < list.len(),
    ensures
        within_quota(list.update(i, e)) == (entries_size(list, list.len()) + entry_size(e) <= max_storage_size() + entry_size(
            list[i],
        )),
{
    lemma_size_update(list, i, e, list.len());
}

// ---------------------------------------------------------------------
// Exec: lookups.
// ---------------------------------------------------------------------

/// The index of the bucket of `lock`.
pub fn find_bucket(storage: &[StorageBucket], lock: &ParsedOrigin) -> (r: Option<usize>)
    ensures
        match r {
            Some(i) => i < storage.len() && storage@[i as int].origin@ == lock@,
            None => forall|i: int| 0 <= i < storage.len() ==> (#[trigger] storage@[i]).origin@ != lock@,
        },
{
    let mut i: usize = 0;
    while i < storage.len()
        invariant
            i <= storage.len(),
            forall|k: int| 0 <= k < i ==> (#[trigger] storage@[k]).origin@ != lock@,
        decreases storage.len() - i,
    {
        let hit = match storage.get(i) {
            Some(b) => origin_eq_exec(&b.origin, lock),
            None => false,
        };
        if hit {
            return Some(i);
        }
        // Never saturates: i < storage.len().
        i = i.saturating_add(1);
    }
    None
}

/// Skipping entries that do not have the key does not change [`find_key`].
proof fn lemma_find_key_skip(list: Seq<StorageEntry>, key: Seq<u8>, i: nat, k: nat)
    requires
        i <= k <= list.len(),
        forall|j: int| i <= j < k ==> (#[trigger] list[j]).key != key,
    ensures
        find_key(list, key, i) == find_key(list, key, k),
    decreases k - i,
{
    if i < k {
        lemma_find_key_skip(list, key, i + 1, k);
    }
}

/// [`find_key`] from the start.
pub fn find_key_exec(list: &[StorageEntryRecord], key: &[u8]) -> (r: Option<usize>)
    ensures
        match r {
            Some(k) => k < list.len() && find_key(entries_view(list@), key@, 0) == Some(k as int),
            None => find_key(entries_view(list@), key@, 0) == None::<int>,
        },
{
    let ghost lv = entries_view(list@);
    let mut i: usize = 0;
    while i < list.len()
        invariant
            i <= list.len(),
            lv == entries_view(list@),
            forall|j: int| 0 <= j < i ==> (#[trigger] lv[j]).key != key@,
        decreases list.len() - i,
    {
        if let Some(e) = list.get(i) {
            proof {
                assert(lv[i as int] == list@[i as int]@);
            }
            if slice_eq(e.key.as_slice(), key) {
                proof {
                    lemma_find_key_skip(lv, key@, 0, i as nat);
                }
                return Some(i);
            }
        }
        // Never saturates: i < list.len().
        i = i.saturating_add(1);
    }
    proof {
        lemma_find_key_skip(lv, key@, 0, list.len() as nat);
    }
    None
}

/// The sum of the octets of the keys and values ([`entries_size`] of the
/// whole list), for a list within the quota.
pub fn entries_size_exec(list: &[StorageEntryRecord]) -> (r: u64)
    requires
        within_quota(entries_view(list@)),
    ensures
        r as nat == entries_size(entries_view(list@), list.len() as nat),
        r <= 5242880,
{
    let ghost lv = entries_view(list@);
    let mut acc: u64 = 0;
    let mut i: usize = 0;
    while i < list.len()
        invariant
            i <= list.len(),
            lv == entries_view(list@),
            within_quota(lv),
            acc as nat == entries_size(lv, i as nat),
            acc <= 5242880,
        decreases list.len() - i,
    {
        if let Some(e) = list.get(i) {
            let k = e.key.len() as u64;
            let v = e.value.len() as u64;
            proof {
                lemma_size_mono(lv, (i + 1) as nat, lv.len());
                assert(lv[i as int] == list@[i as int]@);
                assert(entries_size(lv, (i + 1) as nat) == entries_size(lv, i as nat) + entry_size(lv[i as int]));
            }
            acc = acc.saturating_add(k).saturating_add(v);
        }
        // Never saturates: i < list.len().
        i = i.saturating_add(1);
    }
    acc
}

// ---------------------------------------------------------------------
// Exec: the buckets as a map.
// ---------------------------------------------------------------------

/// A bucket with no entries, to take the place of one being changed.
fn placeholder_bucket() -> (b: StorageBucket) {
    StorageBucket { origin: ParsedOrigin::Opaque(0), entries: Vec::new() }
}

/// `list_in` of the view, for the bucket found by [`find_bucket`].
pub proof fn lemma_list_in_bucket(v: Seq<StorageBucket>, lock: clazel_origin::spec::Origin, r: Option<usize>)
    requires
        buckets_wf(v),
        match r {
            Some(i) => i < v.len() && v[i as int].origin@ == lock,
            None => forall|i: int| 0 <= i < v.len() ==> (#[trigger] v[i]).origin@ != lock,
        },
    ensures
        match r {
            Some(i) => list_in(storage_view(v), lock) == entries_view(v[i as int].entries@),
            None => list_in(storage_view(v), lock) == Seq::<StorageEntry>::empty(),
        },
{
    match r {
        Some(i) => lemma_storage_view_at(v, i as int),
        None => lemma_storage_view_none(v, lock),
    }
}

/// The quota bound on every bucket, from `storage_wf`.
pub open spec fn buckets_within_quota(v: Seq<StorageBucket>) -> bool {
    forall|i: int| 0 <= i < v.len() ==> within_quota(entries_view((#[trigger] v[i]).entries@))
}

/// The state's `storage_wf` gives the quota bound on every bucket.
pub proof fn lemma_buckets_quota(v: Seq<StorageBucket>)
    requires
        buckets_wf(v),
        crate::invariant::storage_wf(storage_view(v)),
    ensures
        buckets_within_quota(v),
{
    assert forall|i: int| 0 <= i < v.len() implies within_quota(entries_view((#[trigger] v[i]).entries@)) by {
        lemma_storage_view_at(v, i);
        let o = v[i].origin@;
        assert(storage_view(v).dom().contains(o));
        assert(within_quota(storage_view(v)[o]));
    }
}

/// The octets of entry `k` of a list within the quota.
fn entry_size_at(list: &[StorageEntryRecord], k: usize) -> (r: u64)
    requires
        k < list.len(),
        within_quota(entries_view(list@)),
    ensures
        r as nat == entry_size(entries_view(list@)[k as int]),
{
    proof {
        lemma_size_ge_entry(entries_view(list@), entries_view(list@).len(), k as int);
    }
    match list.get(k) {
        Some(e) => (e.key.len() as u64).saturating_add(e.value.len() as u64),
        None => 0,
    }
}

/// `setItem(key, value)` ([`set_item_map`]); the result says whether the
/// quota is exceeded, in which case the buckets are unchanged.
pub fn set_item_exec(storage: &mut Vec<StorageBucket>, lock: &ParsedOrigin, key: &[u8], value: &[u8]) -> (quota: bool)
    requires
        buckets_wf(old(storage)@),
        buckets_within_quota(old(storage)@),
    ensures
        buckets_wf(final(storage)@),
        (storage_view(final(storage)@), quota) == set_item_map(storage_view(old(storage)@), lock@, key@, value@),
{
    let ghost old_v = storage@;
    let idx = find_bucket(storage.as_slice(), lock);
    proof {
        lemma_list_in_bucket(old_v, lock@, idx);
    }
    let ghost m = storage_view(old_v);
    let ghost list = list_in(m, lock@);
    let total = key.len().saturating_add(value.len());
    let new_entry = StorageEntryRecord { key: clazel_cookie::strings::copy(key), value: clazel_cookie::strings::copy(value) };
    let ghost ne = StorageEntry { key: key@, value: value@ };
    assert(new_entry@ == ne);
    match idx {
        None => {
            assert(list =~= Seq::<StorageEntry>::empty());
            assert(find_key(list, key@, 0) == None::<int>);
            let ghost nl = list.push(ne);
            proof {
                lemma_quota_push(list, ne);
                assert(entries_size(list, list.len()) == 0);
            }
            if total > 5242880 {
                return true;
            }
            let entries = vec![new_entry];
            let bucket = StorageBucket { origin: clone_origin(lock), entries };
            proof {
                assert(entries_view(bucket.entries@) =~= seq![ne]);
                assert(nl =~= seq![ne]);
                lemma_storage_view_push(old_v, bucket);
            }
            storage.push(bucket);
            false
        },
        Some(bi) => {
            let found;
            let old_size;
            let cur_size;
            match storage.get(bi) {
                Some(b) => {
                    proof {
                        assert(within_quota(entries_view(old_v[bi as int].entries@)));
                    }
                    found = find_key_exec(b.entries.as_slice(), key);
                    old_size = entries_size_exec(b.entries.as_slice());
                    cur_size = match found {
                        Some(ki) => entry_size_at(b.entries.as_slice(), ki),
                        None => 0,
                    };
                    // An existing entry with this key and the same value:
                    // nothing changes.
                    let same_value = match found {
                        Some(ki) => match b.entries.get(ki) {
                            Some(e) => slice_eq(e.value.as_slice(), value),
                            None => false,
                        },
                        None => false,
                    };
                    if same_value {
                        proof {
                            if let Some(ki) = found {
                                assert(list[ki as int].value == value@);
                            }
                        }
                        return false;
                    }
                },
                None => {
                    return false;
                },
            }
            proof {
                assert(list == entries_view(old_v[bi as int].entries@));
                assert(old_size as nat == entries_size(list, list.len()));
                if let Some(ki) = found {
                    assert(list[ki as int] == old_v[bi as int].entries@[ki as int]@);
                    assert(cur_size as nat == entry_size(list[ki as int]));
                    lemma_size_ge_entry(list, list.len(), ki as int);
                    lemma_quota_update(list, ki as int, ne);
                } else {
                    lemma_quota_push(list, ne);
                }
            }
            match found {
                Some(ki) => {
                    // The value differs. The new size is old_size - cur_size + total.
                    if total > 5242880 || old_size.saturating_add(total as u64) > 5242880u64.saturating_add(cur_size) {
                        return true;
                    }
                    let mut tmp = placeholder_bucket();
                    storage.set_and_swap(bi, &mut tmp);
                    tmp.entries.set(ki, new_entry);
                    let ghost nb = tmp;
                    proof {
                        assert(entries_view(tmp.entries@) =~= list.update(ki as int, ne));
                        assert(tmp.origin@ == lock@);
                    }
                    storage.set(bi, tmp);
                    proof {
                        lemma_storage_view_update(old_v, bi as int, nb);
                        assert(storage@ =~= old_v.update(bi as int, nb));
                    }
                    false
                },
                None => {
                    if total > 5242880 || old_size.saturating_add(total as u64) > 5242880 {
                        return true;
                    }
                    let mut tmp = placeholder_bucket();
                    storage.set_and_swap(bi, &mut tmp);
                    tmp.entries.push(new_entry);
                    let ghost nb = tmp;
                    proof {
                        assert(entries_view(tmp.entries@) =~= list.push(ne));
                        assert(tmp.origin@ == lock@);
                    }
                    storage.set(bi, tmp);
                    proof {
                        lemma_storage_view_update(old_v, bi as int, nb);
                        assert(storage@ =~= old_v.update(bi as int, nb));
                    }
                    false
                },
            }
        },
    }
}

/// `removeItem(key)` ([`remove_item_map`]).
pub fn remove_item_exec(storage: &mut Vec<StorageBucket>, lock: &ParsedOrigin, key: &[u8])
    requires
        buckets_wf(old(storage)@),
    ensures
        buckets_wf(final(storage)@),
        storage_view(final(storage)@) == remove_item_map(storage_view(old(storage)@), lock@, key@),
{
    let ghost old_v = storage@;
    let idx = find_bucket(storage.as_slice(), lock);
    proof {
        lemma_list_in_bucket(old_v, lock@, idx);
    }
    let ghost m = storage_view(old_v);
    let ghost list = list_in(m, lock@);
    match idx {
        None => {
            assert(find_key(list, key@, 0) == None::<int>);
        },
        Some(bi) => {
            let found = match storage.get(bi) {
                Some(b) => {
                    proof {
                        assert(b == old_v[bi as int]);
                    }
                    find_key_exec(b.entries.as_slice(), key)
                },
                None => None,
            };
            match found {
                None => {},
                Some(ki) => {
                    let entries_len = match storage.get(bi) {
                        Some(b) => b.entries.len(),
                        None => 0,
                    };
                    if entries_len == 1 {
                        proof {
                            assert(list.remove(ki as int).len() == 0);
                            lemma_storage_view_remove(old_v, bi as int);
                        }
                        let _removed = storage.remove(bi);
                    } else {
                        let mut tmp = placeholder_bucket();
                        storage.set_and_swap(bi, &mut tmp);
                        let _entry = tmp.entries.remove(ki);
                        let ghost nb = tmp;
                        proof {
                            assert(entries_view(tmp.entries@) =~= list.remove(ki as int));
                            assert(list.remove(ki as int).len() > 0);
                            assert(tmp.origin@ == lock@);
                        }
                        storage.set(bi, tmp);
                        proof {
                            lemma_storage_view_update(old_v, bi as int, nb);
                            assert(storage@ =~= old_v.update(bi as int, nb));
                        }
                    }
                },
            }
        },
    }
}

/// `clear()`: the storage map with `lock`'s list emptied.
pub fn clear_exec(storage: &mut Vec<StorageBucket>, lock: &ParsedOrigin)
    requires
        buckets_wf(old(storage)@),
    ensures
        buckets_wf(final(storage)@),
        storage_view(final(storage)@) == set_map(storage_view(old(storage)@), lock@, Seq::empty()),
{
    let ghost old_v = storage@;
    let idx = find_bucket(storage.as_slice(), lock);
    proof {
        lemma_list_in_bucket(old_v, lock@, idx);
    }
    let ghost m = storage_view(old_v);
    match idx {
        None => {
            proof {
                lemma_storage_view_none(old_v, lock@);
                assert(m.remove(lock@) =~= m);
            }
        },
        Some(bi) => {
            proof {
                lemma_storage_view_remove(old_v, bi as int);
            }
            let _removed = storage.remove(bi);
        },
    }
}

// ---------------------------------------------------------------------
// The length of a map fits a u64.
// ---------------------------------------------------------------------

/// If no key in the first `n` entries is empty, each entry has at least one
/// octet.
proof fn lemma_size_ge_count_nonempty(list: Seq<StorageEntry>, n: nat)
    requires
        n <= list.len(),
        forall|j: int| 0 <= j < n ==> (#[trigger] list[j]).key.len() > 0,
    ensures
        entries_size(list, n) >= n,
    decreases n,
{
    if n > 0 {
        lemma_size_ge_count_nonempty(list, (n - 1) as nat);
    }
}

/// With unique keys, at most one entry is empty, so the octets are at least
/// the number of entries less one.
proof fn lemma_size_ge_count(list: Seq<StorageEntry>, n: nat)
    requires
        n <= list.len(),
        crate::invariant::storage_keys_unique(list),
    ensures
        entries_size(list, n) + 1 >= n,
    decreases n,
{
    if n > 0 {
        lemma_size_ge_count(list, (n - 1) as nat);
        let last = list[n - 1];
        if last.key.len() == 0 {
            // Every earlier key differs from the empty key.
            assert forall|j: int| 0 <= j < n - 1 implies (#[trigger] list[j]).key.len() > 0 by {
                assert(list[j].key != list[n - 1 as int].key);
                if list[j].key.len() == 0 {
                    assert(list[j].key =~= list[n - 1 as int].key);
                }
            }
            lemma_size_ge_count_nonempty(list, (n - 1) as nat);
        }
    }
}

/// The open obligation of item 2.10's contract, `StorageLength`'s cast of a
/// map's length to `u64`: a map with unique keys within the quota has at
/// most `max_storage_size() + 1` entries (each entry but one has an octet),
/// so its length is below 2^64 and the cast is exact. (The exec `step`
/// does not need this: its map is a `Vec`, whose length is a `usize`.)
pub proof fn lemma_storage_length_exact(list: Seq<StorageEntry>)
    requires
        crate::invariant::storage_keys_unique(list),
        within_quota(list),
    ensures
        list.len() <= max_storage_size() + 1,
        list.len() as u64 as nat == list.len(),
{
    lemma_size_ge_count(list, list.len());
}

} // verus!
