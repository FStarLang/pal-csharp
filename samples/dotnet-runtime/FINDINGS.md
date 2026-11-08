# Findings

What verifying dotnet/runtime's collections in place turned up. Each entry names where the
full account lives: a section of `doc/translation.md`, and the member whose contract
records it.

The upstream commit is the one [`README.md`](README.md) names. "Reproduced" means a
program against the shipped .NET 10 runtime shows the behaviour. The other entries are
read off the source and pinned by the verified contracts.

## 1. Wrong results

### 1.1 `SortedSet<T>.SetEquals` / `IsSubsetOf` miscount (`InternalIndexOf` vs `BitHelper`)

**Reproduced on .NET 10.** §27.3, R27.14.

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
  R27.51, R27.52).
* **`List<T>.FindIndex`/`FindLastIndex` check the window before `match`.** A bad window
  with a `null` `match` throws `ArgumentOutOfRangeException`, not `ArgumentNullException`.
  `FindLastIndex` on an empty list accepts `startIndex == -1` (and only that) with
  `count == 0`. §26.2.
* **`Stack<T>.Enumerator.MoveNext` bounds its step by `_array.Length`, not `Count`.** It is
  correct only because the version check has already passed, as a `Debug.Assert` notes.
  §28.
* **`PriorityQueue`'s heap property is a precondition, not an invariant.** Every reading
  member needs it, and every writing member re-establishes it. §26.2.

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

## 6. Defects found in pal-csharp and its toolchain

Found because a proof that should have failed passed, or failed for the wrong reason.

* Contracts on property `get` accessors were silently ignored (R27.12). Contracts on
  `set` accessors and on explicit interface members were dropped (§29). Those members had
  been "verified" against `true`.
* A constructor with an expression body crashed the borrowing analysis (§29).
* A call among later operands refolded the owner, so an array permission was stated
  about a stale record (R29.5).
* Roslyn reports `object` as the converted type at several nested positions, which first
  produced double boxing (§29).
* An `[SMTPat (Seq.index s j)]` lemma fires in every module that loads it. One made an
  unrelated proof time out (§27.3).
* Pulse keeps no facts from a skipped `if` arm at a join. This needed several emitter
  workarounds (R27.10, R25.10, R27.40). It is worth raising with Pulse.
