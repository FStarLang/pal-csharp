# Findings

What verifying dotnet/runtime's collections in place turned up. Each entry names where the
full account lives: a section of `doc/translation.md`, and the member whose contract
records it.

The upstream commit is the one [`README.md`](README.md) names. "Reproduced" means a
program against the shipped .NET 10 runtime shows the behaviour. The other entries are
read off the source and pinned by the verified contracts.

## 1. Wrong results

### 1.1 `SortedSet<T>.SetEquals` / `IsSubsetOf` miscount (`InternalIndexOf` vs `BitHelper`)

**Reproduced on .NET 10.** §27.3, R27.14. Open upstream as dotnet/runtime#102118; a
walk-through with the failing proof is in [SORTEDSET-PR133116.md](SORTEDSET-PR133116.md) §2-§3.

* `CheckUniqueAndUnfoundElements` marks each element of `other` it finds in a `BitHelper`
  bitmap. The bitmap is sized from `Count`.
* The bit index comes from `InternalIndexOf`, which is a node's breadth-first position:
  root 0, children `2k+1` and `2k+2`. That is bounded by `2^height`, not by `Count`.
* `BitHelper.MarkBit` silently ignores an index past its capacity. So a repeated
  occurrence of such an element is counted as a new unique element.
* As a result, for `s = new SortedSet<int>(0..n-1)` and `xs` listing every element twice,
  `s.SetEquals(xs)` and `s.IsSubsetOf(xs)` return `false`:

  | n | max index | bitmap bits | result |
  |---|---|---|---|
  | 4, 10 | 6, 30 | 32 | correct |
  | 40 | 254 | 64 | wrong |
  | 100 | 510 | 128 | wrong |
  | 1000 | 65534 | 1024 | wrong |
  | 100000 | 33554430 | 100000 | wrong |

* Separately, `2 * index + 2` overflows `int` in a tree deeper than about 30 levels.

The verified `InternalIndexOf` requires `Height <= 30`, and ensures its result is at most
`2^Height - 2`. It does not ensure it is less than `Count`.

### 1.2 `SortedSet<T>` views go stale when the version counter wraps

§32 (R32.14).

* `TreeSubSet`'s constructor sets its `version` and `_countVersion` to `-1`, meaning "never
  checked". The set's own `version` is wrapping, so it can be `-1` too.
* If the set's version is `-1` when the view is made, `Count` skips the recount and returns
  0, however many elements are in range.
* If the set's version is `-2`, one write through the view makes the two versions equal.
  The view then keeps the root it found before the write, which may be a removed node, and
  later `Contains`/`FindNode` calls search the wrong subtree.
* The same happens to a view last re-synchronised exactly 2^32 writes earlier.

Each case needs about 2^32 modifications first. The verified writes through a view require
`version != underlying.version + 1`, which is exactly what keeping the view coherent needs.

### 1.3 dotnet/runtime#133116's fix for 1.1 is wrong at a view

**Reproduced** with the PR's code. §37. The full account, with the counterexample, the
patch and the proof, is [SORTEDSET-PR133116.md](SORTEDSET-PR133116.md).

* dotnet/runtime#133116 sizes the bitmap from the tree's height, which fixes 1.1 at the
  set. At a view, it makes `InternalIndexOf` search from the view's root.
* That root is the node the range search stops at. Its subtree can hold nodes outside the
  range, and `InternalIndexOf` finds them, so an out-of-range item counts as found.
* For `s = {0..9}` and `v = s.GetViewBetween(2, 5)`, `v.SetEquals([2, 3, 4, 9])` and
  `v.IsSubsetOf([2, 3, 4, 9])` return `true`. Both are `false` on .NET 10.

The proof fails only there: the method verifies at the set, and at the view it fails to
re-establish its loop invariant where it marks an item as found. With
`int index = IsWithinRange(item) ? InternalIndexOf(item) : -1;` it verifies at both, against
the counts of items of `other` in the set (in the view's range, at a view). The proof also
shows that the PR's bitmap-growth branch is dead.

## 2. Arithmetic that can overflow

Each of these is unchecked `int` arithmetic that wraps for some state the types allow.
None is reachable at ordinary sizes. The verified contract states the bound that rules it
out.

| Where | Expression | Bound in the contract | Section |
|---|---|---|---|
| `PriorityQueue.GetFirstChildIndex` / `MoveDown` | `(index << 2) + 1` wraps once `index >= 2^29`; a queue of more than `2^29+1` nodes then reads at a negative index | `Count <= 2^29` on `MoveDown`, `Dequeue`, … | §26.2 |
| `PriorityQueue.Enqueue` | `_size + 1` | `Count < int.MaxValue` | §26.2 |
| `SortedSet.ConstructRootFromSortedArray` | midpoint `(startIndex + endIndex) / 2`; `start + (end - start) / 2` would not need the bound | `arr.Length <= 2^30`; also on `UnionWith`/`IntersectWith`, which rebuild through it | §27.3 |
| `SortedSet.AddIfNotPresent` | `++count` | `Count < int.MaxValue` | §27.3 |
| `SortedSet.InternalIndexOf` | `2 * index + 2` | `Height <= 30` | §27.3 |
| `Queue<T>.Enumerator.MoveNext` | `_q._head + _i`, possible when capacity exceeds 2^30 | `head + Count <= int.MaxValue` | §28 |
| `SortedList` enumerators | `_index = Count + 1` at the end; also `IEnumerator.Current` and the `IDictionaryEnumerator` members | `Count < int.MaxValue` | §28, §29 |
| `PriorityQueue.Remove` | sifts down from an arbitrary index, so it has the same `(index << 2) + 1` wrap | `Count <= 2^29` | §33 |
| `PriorityQueue` `Heapify`, `EnqueueRange(IEnumerable<(E, P)>)` and the `IEnumerable` constructors | the same `(index << 2) + 1`, now from bulk loads with no size check | resulting `Count <= 2^29` | §34 |
| `SortedSet(IEnumerable<T>, IComparer)` with a different comparer | `EnumerableHelpers.ToArray` may double the array, and `ConstructRootFromSortedArray` needs its length within 2^30 | `2 * count + 2 <= 2^30` | §34 |
| `EnumerableHelpers.ToArray` | growth `count << 1` wraps, and the `(uint)` comparison that follows catches it; correct, but only under wrapping semantics | verified as `[Wrapping]` | §34 |
| `Queue<T>.CopyTo` | `arrayIndex + _array.Length - _head` overflows in its first addition, and is correct only because the wrap cancels | verified as `[Wrapping]` | §23 |

## 3. Behaviour that is easy to misread

* **Fail-fast enumeration is incomplete.** Every collection's version counter wraps. After
  exactly 2^32 modifications an enumerator's stored version matches again, and `MoveNext`
  carries on over the modified collection. The BCL documents fail-fast as "best effort".
  The verified `MoveNext` contracts compare versions, not histories. §28 (R28.8).
* **`SortedSet.UnionWith` keeps a representative that depends on sizes.** When an element
  of `other` compares equal to one already in the set, the merge branch keeps `other`'s
  and the `Add` branch keeps the set's own. With a comparer that identifies distinct
  values (such as case-insensitive strings), which one survives depends on the two sizes.
  The contract states the branch condition. §27.3.
* **`SortedSet` trusts `IComparer<T>.Equals`.** The copy constructor, `UnionWith`,
  `Overlaps` and `ExceptWith` treat `other`'s tree as ordered by this set's comparer when
  the two comparers are `Equals`. A comparer whose `Equals` is true for a different order
  yields a set that is not sorted under its own comparer, or a wrong `Overlaps`. The
  verified contracts require the two comparers to be the same object. §27.3 (R27.47,
  R27.51, R27.52). The constructor `SortedSet(collection, comparer)` has the same
  hazard: it clones `collection`'s tree whenever the comparers are `Equals`. §34.
* **`List<T>.FindIndex`/`FindLastIndex` check the window before `match`.** A bad window
  with a `null` `match` throws `ArgumentOutOfRangeException`, not `ArgumentNullException`.
  `FindLastIndex` on an empty list accepts `startIndex == -1` (and only that) with
  `count == 0`. §26.2.
* **`Stack<T>.Enumerator.MoveNext` bounds its step by `_array.Length`, not `Count`.** It is
  correct only because the version check has already passed, as a `Debug.Assert` notes.
  §28.
* **`PriorityQueue`'s heap property is a precondition, not an invariant.** Every reading
  member needs it, and every writing member re-establishes it. §26.2.

* **Equality is not always symmetric, and the code assumes it is in places.**
  `OrderedDictionary.SetAt(int, TKey, TValue)` calls `Equals(key, e.Key)`, while `IndexOf`
  calls `Equals(entry.Key, key)`. The two agree only for a symmetric comparer, which
  `IEqualityComparer<T>` does not require. Without symmetry and transitivity, the hashed
  collections do not even keep their keys distinct, so the `OrderedDictionary` model does
  not claim distinctness. §33.
* **Some writes do not bump the version.** `OrderedDictionary`'s indexer setter,
  `TryInsert` with overwrite, and `SetAt(int, TValue)` replace a value without
  incrementing `_version`. So an enumerator in progress does not fail. `Dictionary` behaves
  the same way. §33.
* **`SortedDictionary`'s `ICollection<KeyValuePair>.Contains` and `Remove` treat null values
  differently.** `Contains` tests a null value with `== null`, while `Remove` always calls
  `EqualityComparer<TValue>.Default.Equals`. They agree only under the default comparer.
  §32.
* **`LinkedList.Find(null)`** tests `item == null` rather than using the comparer. §31.
* **`PriorityQueue.Remove` is deterministic.** Its documentation says that with
  duplicates, which match is removed is "non-deterministic". For a given heap layout it is
  the first match in array order. §33.
* **`OrderedDictionary.IndexOf(TKey)` passes one local by `ref` to two `out` parameters.**
  This is harmless only because the callee never reads them. §33.
* **`List<T>.InsertRange(index, this)`** copies the list into itself in two `Array.Copy`
  steps. A caller cannot lend the list as an enumerable while owning it as the receiver, so
  this branch is unreachable in the model and is not verified. §34.
* **`Dictionary.Resize(forceNewHashCodes: true)`** calls `comparer.GetHashCode(entry.key)`
  without the null case the default hashing has. It is correct only because a key is never
  null, which is now part of the verified invariant. §30.
* **`HashHelpers.ExpandPrime` depends on an erased assertion.** When doubling would pass
  `MaxPrimeArrayLength` it returns that constant, which is a valid table size only because
  it is prime. The code checks this only with `Debug.Assert`, which Release builds erase.
  The proof states it as a lemma (`MaxPrimeIsPrime`, proved). §30 (R30.31).
* **`HashHelpers.ExpandPrime` throws.** It raises `ArgumentException` once the size
  reaches `MaxPrimeArrayLength`, rather than saturating. §33.

## 4. Nullability annotations that are not true

Null-forgiving `!` operators and non-nullable parameters that do receive `null`. Each
callee handles `null` correctly, so these are annotation errors, not crashes. The verified
source marks the parameters `[AllowNull]`. §27.3 (R27.28).

* `SortedSet.AddIfNotPresent` passes `greatGrandParent!` to `InsertionBalance`. It is
  `null` whenever the red parent is a child of the root.
* `SortedSet.DoRemove` passes `parentOfMatch!` and `grandParent!` to `ReplaceNode`. The
  first is `null` when the match is the root, and the second when the descent ends at the
  root's child.
* In `ReplaceNode`, `successor = match.Left!` is `null` when the match is a leaf, and
  `ReplaceChild`/`ReplaceChildOrRoot` then receive a `null` `newChild`.

## 5. Contracts the code cannot meet as written

* **`SortedDictionary.Add`/`CopyTo` cannot declare the throw they pass on.** When
  `_set.Add` throws, its throw path does not say the comparer is unchanged, so the
  dictionary's invariant cannot be restored for its own throw clause. The verified
  contracts require the conditions that rule the throw out. §27.3.
* **`SortedSet.Reverse` is specified without fail-fast.** Its contract describes an
  enumeration over an unchanged set. The version check inside the iterator is the
  run-time behaviour of R28.8, and is not stated. §27.3.

* **`Dictionary.Remove(key, out value)` cannot say which value it returns.** C#'s definite
  assignment rejects naming an `out` parameter in a loop invariant before it is assigned,
  so the contract states only what `Remove(key)` does. §30.
* **A `SortedSet` view's `Count` and `Clear` need a precondition the view's constructor
  cannot establish.** It is that the cached count is current whenever the cached version
  matches. §1.2's sentinel collision is the reason it cannot be established. §35.
* **`LinkedList` node arguments from another list.** The code throws
  `InvalidOperationException` for such a node. The model specifies that exception only
  for a node in this list's region, so a caller passing another list's node is outside
  the contract. §31.

## 6. Defects found in pal-csharp and its toolchain

Found because a proof that should have failed passed, or failed for the wrong reason.

* **Unsound:** at `object`, `ThrowIfNull(key)` was dropped, because a non-nullable
  reference was assumed non-null. That assumption does not hold for callers of a
  non-generic `IDictionary`, so the `[Throws(ArgumentNullException)]` contracts of those
  members were vacuous (R35.11).
* A `decreases` clause naming a spec member of `this` produced an ill-typed term in classes
  with array fields (R30.35).
* A diagnostic (PALCS0751) was missing from the catalog, and the lint caught it.
* Under `[TranslateAnnotatedOnly]`, a nested struct that an annotated method returned
  (`SortedSet<T>.ElementCount`) was skipped silently, and the method named a type that did
  not exist (R37.8).
* In a view's replica of a base method, a virtual `[Spec]` property of the base was read
  with the base's body applied to the view's record, not with the view's override (R37.7).
* A pattern lemma whose `unit` argument did not appear in its SMT pattern never fired. Z3
  only warned. §35.
* Copying the rest of a loop body into both arms of an `if` (R34.11) made one
  `SortedSet.DoRemove` query run more than 24 minutes; the split is now limited to
  straight-line code.
* `Dictionary.TryInsert` first took about 1h35m and 115 GB to check. Joining the branches,
  splitting the insertion tail into separately checked functions, and keeping the table's
  predicates opaque brought it to 7m22s and 10.6 GB, without changing the contract
  (R30.36–R30.40).
* Contracts on property `get` accessors were silently ignored (R27.12). Contracts on
  `set` accessors and on explicit interface members were dropped (§29). Those members had
  been "verified" against `true`.
* **Unsound:** `x is null` on an array was translated as the constant `false` (R33.6).
* **Unsound:** a write through a `ref` argument rooted at a `ref` local into a field's
  array was not counted as a write, so the method was classed as read-only (R33.24). A
  write through a local alias of an array was missed in the same way (R33.10).
* An annotated indexer with an expression body was silently skipped, and a constructor's
  expression body was dropped (R33.13).
* A constructor with an expression body crashed the borrowing analysis (§29).
* A call among later operands refolded the owner, so an array permission was stated
  about a stale record (R29.5).
* Roslyn reports `object` as the converted type at several nested positions, which first
  produced double boxing (§29).
* An `[SMTPat (Seq.index s j)]` lemma fires in every module that loads it. One made an
  unrelated proof time out (§27.3).
* Pulse keeps no facts from a skipped `if` arm at a join. This needed several emitter
  workarounds (R27.10, R25.10, R27.40). It is worth raising with Pulse.
