# `SortedSet<T>` set comparisons: a bug, a proposed fix, a bug in the fix, and a proof

This document follows one method of `System.Collections.Generic.SortedSet<T>` through
these steps:

1. The method miscounts, which is the open issue
   [dotnet/runtime#102118](https://github.com/dotnet/runtime/issues/102118).
2. A proof of the original method fails at exactly that miscount.
3. The pull request [dotnet/runtime#133116](https://github.com/dotnet/runtime/pull/133116)
   proposes a fix. The fix is correct for a set but wrong for a view.
4. A one-line patch makes the PR's method verify for both a set and a view.

All paths below are relative to the repository root. Line numbers refer to the
commit this document was added in. `SortedSet.cs` stands for
`samples/dotnet-runtime/src/libraries/System.Collections/src/System/Collections/Generic/SortedSet.cs`.
`TreeSubSet.cs` is `SortedSet.TreeSubSet.cs`, in the same directory. `harness/` stands for
`samples/dotnet-runtime/pal/SortedSet/`.

Upstream references:
* dotnet/runtime at `a69ba15b9c` is the base this repository's runtime sources are taken
  from (`samples/dotnet-runtime/README.md`).
* dotnet/runtime#133116 at head `254919ae80` (open, by @lilinus) is the PR's code
  analysed here.

Contents:
1. [`SortedSet<T>` and `CheckUniqueAndUnfoundElements`](#1-sortedsett-and-checkuniqueandunfoundelements)
2. [The original bug (dotnet/runtime#102118)](#2-the-original-bug-dotnetruntime102118)
3. [The proof of the original method fails](#3-the-proof-of-the-original-method-fails)
4. [The proposed fix: dotnet/runtime#133116](#4-the-proposed-fix-dotnetruntime133116)
5. [The counterexample: dotnet/runtime#133116 at a view](#5-the-counterexample-dotnetruntime133116-at-a-view)
6. [The patch](#6-the-patch)
7. [The revised proof](#7-the-revised-proof)
8. [Reproducing everything](#8-reproducing-everything)

---

## 1. `SortedSet<T>` and `CheckUniqueAndUnfoundElements`

### 1.1 The tree

A `SortedSet<T>` is a red-black binary search tree of `Node`s, ordered by `comparer`. The
verified model of a set is its tree, comparer, count and version (`SortedSetModel`). The
set's `[Refine]` invariants (`SortedSet.cs:77-81`) state:
* the keys are strictly sorted;
* the tree is red-black (`SpecSearchTree.IsRedBlack`);
* `Count` equals the tree's size.

### 1.2 Views

`GetViewBetween(lo, hi)` returns a `TreeSubSet`, a live view of the elements in `[lo, hi]`.
A view does not copy anything. Its `root` is the node at which a top-down range search
stops: the first node on the path from the set's root that lies within the bounds.
* `FindRange` (`SortedSet.cs:1215`) performs that search.
* A view's constructor calls it, at `TreeSubSet.cs:93`.

**The view's root subtree can hold nodes outside the range.** The search stops at the
first node in range, and that node's subtrees are not trimmed. A view therefore filters with
`IsWithinRange` (`TreeSubSet.cs:190`) whenever it walks its subtree. The base's
`IsWithinRange` is `true` (`SortedSet.cs:538`).

### 1.3 Breadth-first positions: `InternalIndexOf`

`InternalIndexOf(item)` (`SortedSet.cs:1174`) searches from `root` and returns the
item's breadth-first position, or -1 if the item is absent. The root is 0, and the
children of position `k` are `2k+1` and `2k+2`. A position is bounded by `2^height - 2`,
not by `Count`.

The verified contract (`SortedSet.cs:1162-1173`, doc/translation.md R27.14):
* it requires `Height <= 30`, which rules out `int` overflow of `2k+2`;
* it ensures `Result == HeapIndex(comparer, tree, item, 0)`;
* it ensures `Result <= Breadth(tree) - 2`, where `Breadth` is `2^height`.

### 1.4 `CheckUniqueAndUnfoundElements` and its callers

Four set comparisons use the method when `other` is not a `SortedSet<T>` with the same
comparer:

| caller | call | result |
|---|---|---|
| `IsSubsetOf` (`SortedSet.cs:1903`) | `:1927`, `returnIfUnfound = false` | `UniqueCount == Count` |
| `IsProperSubsetOf` (`:1971`) | `:1995`, `false` | `UniqueCount == Count && UnfoundCount > 0` |
| `IsProperSupersetOf` (`:2060`) | `:2110`, `true` | `UniqueCount < Count && UnfoundCount == 0` |
| `SetEquals` (`:2119`) | `:2171`, `true` | `UniqueCount == Count && UnfoundCount == 0` |

The method returns an `ElementCount` (`SortedSet.cs:3188`) with these fields:
* **`UniqueCount`**: the number of *distinct* items of `other` that are in the set;
* **`UnfoundCount`**: the number of items of `other` that are not. With
  `returnIfUnfound`, it may stop at the first such item, so the count is then only
  known to be positive.

Computing `UniqueCount` requires recognising an item seen before. The method marks the
item's node in a bitmap indexed by the node's breadth-first position, as follows:

```csharp
int index = InternalIndexOf(item);
if (index >= 0) {
    if (!bitHelper.IsMarked(index)) { bitHelper.MarkBit(index); uniqueFoundCount++; }
} else {
    unfoundCount++; if (returnIfUnfound) break;
}
```

That is correct exactly when the bitmap has a bit for every position the search can
return. §2 shows the original sizing does not.

At a view, `Count` is the number of elements in range. The method must therefore count only
in-range items as found, and every out-of-range item as unfound. §5 shows how the PR breaks
this.

---

## 2. The original bug (dotnet/runtime#102118)

### 2.1 The code

dotnet/runtime at `a69ba15b9c`, `SortedSet.cs` lines 1366-1421:

```csharp
int originalLastIndex = Count;
int intArrayLength = BitHelper.ToIntArrayLength(originalLastIndex);   // ceil(Count / 32)
Span<int> span = stackalloc int[StackAllocThreshold];
BitHelper bitHelper = (uint)intArrayLength <= StackAllocThreshold ?
    new BitHelper(span.Slice(0, intArrayLength), clear: true) :
    new BitHelper(new int[intArrayLength], clear: false);
...
foreach (T item in other)
{
    int index = InternalIndexOf(item);
    if (index >= 0)
    {
        if (!bitHelper.IsMarked(index)) { bitHelper.MarkBit(index); uniqueFoundCount++; }
    }
    else { UnfoundCount++; if (returnIfUnfound) break; }
}
```

The bitmap has `32 * ceil(Count / 32)` bits. `BitHelper` (upstream `BitHelper.cs:22-47`)
silently ignores a position past its span:
* **`MarkBit`** writes only `if (bitArrayIndex < (uint)span.Length)`.
* **`IsMarked`** returns `bitArrayIndex < (uint)span.Length && ...`, which is false past
  the end.

An element at a position `>= 32 * ceil(Count / 32)` is never marked. Each repeated occurrence
of it in `other` therefore counts as a *new* unique element. `UniqueCount` then exceeds the
number of distinct elements found, and `UniqueCount == Count` fails.

The upstream issue's reporter hit exactly this with a 100-element set and a list holding
each element two or three times: `ss.IsSubsetOf(l)` returned `False`, while `HashSet`
returned `True`.

### 2.2 A concrete instance (n = 18)

The following was run against the upstream base code:

```csharp
var s = new SortedSet<int>(); for (int i = 0; i < 18; i++) s.Add(i);
// tree:  7(3(1(0 2) 5(4 6)) 11(9(8 10) 13(12 15(14 16(. 17)))))
// positions: 0:7 1:3 2:8 3:1 4:9 5:4 6:10 7:0 8:11 9:5 10:12 11:2 12:13 13:6
//            14:29 15:14 16:30 17:62
var xs = Enumerable.Range(0, 18).Concat(Enumerable.Range(0, 18)).ToList();
s.SetEquals(xs);   // False (expected True)
s.IsSubsetOf(xs);  // False (expected True)
```

How the miscount arises:
* `Count = 18` gives one `int`, so the bitmap has 32 bits.
* Element 17 lies at position 62 (right, right, right, right, right of the root), past
  the bitmap.
* Both occurrences of 17 count as unique, so `UniqueCount = 19 ≠ 18`.

The same check on .NET 10.0.15 (`samples/dotnet-runtime/FINDINGS.md` §1.1):

| n | max position | bitmap bits | `SetEquals(each twice)` |
|---|---|---|---|
| 10 | 30 | 32 | correct |
| 18 | 62 | 32 | **wrong** |
| 40 | 254 | 64 | **wrong** |
| 100 | 510 | 128 | **wrong** |
| 1000 | 65534 | 1024 | **wrong** |

There is a separate defect: `2 * index + 2` overflows `int` in a tree deeper than about 30
levels. With n = 262144 sequential inserts, the last element's position comes out as -2, and
`SetEquals` of the set's own elements returns `False`. The verified `InternalIndexOf`
*requires* `Height <= 30` to exclude this case (§1.3). This document is about the
miscount.

---

## 3. The proof of the original method fails

### 3.1 The specification

The specification is in `harness/SortedSetCount.fst`, a pure F* module that nothing trusts.
It is bound to C# by `harness/Count.cs`. It counts over the keys `ks` of the set (or of
the set within a view's range), using an admit predicate `ok`:
* for a set, `ok` is `all_ok`;
* for a view, `ok` is `in_range lo hi la ua`.

| definition | `SortedSetCount.fst` | meaning |
|---|---|---|
| `found c ok ks s` | 196 | distinct keys of `ks` that `ok` admits and some item of `s` equals (under `c`) |
| `unfound c ok ks s` | 200 | items of `s` that are not an admitted key |
| `found_all`/`unfound_all` | 207-208 | the set's counts (`ok = all_ok`) |
| `found_range`/`unfound_range` | 211-214 | a view's counts (`ok = in_range ...`) |
| `index_of c ok tr x` | 220 | `heap_index` of `x` in `tr` if `ok x`, else -1: the position the loop marks |
| `phit c ok tr s p` | 224 | some item of `s` has position `p`: what bit `p` should hold |
| `marks c ok tr m s` | 412 | every bit `p < |m|` of the bitmap `m` equals `phit ... s p` |
| `loop_inv_g`/`loop_inv_s` | 633/639 | after `i` items: `marks` holds, `uniq == found(prefix)`, `unf == unfound(prefix)` |

The method's contract at the set (`SortedSet.cs:2248-2252`) states:
* `UnfoundCount > 0` exactly when `unfound_all > 0`;
* `UniqueCount == found_all`, unless the method returned early.

`found_all == Count` holds exactly when `other` contains every element of the set, so
the callers' tests in §1.4 are then right.

### 3.2 The experiment

The repository's method is dotnet/runtime#133116's (§6). The original body is checked
by applying `harness/experiments/original.patch` and running it through
`harness/experiments/run.sh original`. The patch differs from the repository's method only
in the following ways:
* The bitmap is `bool[intArrayLength * 32]`, with
  `intArrayLength = (Count - 1) / 32 + 1`, as `BitHelper.ToIntArrayLength` computes.
* The loop uses `BitHelper`'s semantics for a position past the bitmap:
  ```csharp
  if (index >= 0)
  {
      // BitHelper: `IsMarked` reads false and `MarkBit` does nothing past the bitmap.
      if (!(index < marked.Length && marked[index]))
      {
          if (index < marked.Length) marked[index] = true;
          uniqueFoundCount++;
      }
  }
  ```
* The step lemma is `loop_step_beyond_s` (`SortedSetCount.fst:701`), which is
  `LoopStepBeyond` in `Count.cs`. For a position `p` past the bitmap, it states what keeps
  the invariant: the found count may grow only if `not (phit ... prefix p)`, that is, only
  if no earlier item had position `p`. The bitmap cannot tell.
* There is one assumption, `Pal.Assume(Height <= 30 && Count < 2^30)`:
  * the height bound is `InternalIndexOf`'s precondition, assuming away the separate
    overflow defect (§2.2);
  * the count bound keeps `intArrayLength * 32` in range, which is an artifact of the
    `bool[]` model (`BitHelper` multiplies nothing).

  Neither bound touches the miscount.

### 3.3 The result

The proof fails at exactly one obligation:

```
SortedSet.cs(2297,13): error PALCS0600: ...
Failed to prove: SortedSetCount.loop_inv_s _r63.fld_comparer (...SpecRangeLo...) ...
  (match Prims.not t25 with
   | true -> (match FStar.Int32.lt t18 (arr_length var_marked) with
              | true -> FStar.Seq.Base.upd __vmarked (FStar.Int32.v t18) true
              | false -> __vmarked)
   | false -> __vmarked)
  pre_other (... item index + 1 ...)
  (FStar.Int32.v (match Prims.not t25 with
                  | true -> FStar.Int32.add __vuniqueFoundCount 1l
                  | false -> __vuniqueFoundCount))
  (FStar.Int32.v __vunfoundCount)
```

Line 2297 is the `foreach`, in the patched file. The failing branch is the one where
`IsMarked` said "not seen" (`not t25`). The bitmap is updated only `if index < marked.Length`,
and `uniqueFoundCount + 1` is the new count. The invariant `uniq == found(prefix)` cannot be
re-established. When `index >= marked.Length` and an earlier item had the same position, the
true count does not grow, but the code adds one.

The only gap is a position past the `Count`-sized bitmap. As a control, adding
`Pal.Assume(index < marked.Length)` in the found branch makes the module verify.
Everything else in the original method is correct.

The proof does not just fail to go through: it names the defect. A position can lie past
the bitmap because `InternalIndexOf`'s verified bound is `2^Height - 2` (§1.3), and
nothing relates `2^Height` to `Count`.

---

## 4. The proposed fix: dotnet/runtime#133116

The PR (head `254919ae80`) touches `SortedSet.cs`, `SortedSet.TreeSubSet.cs` and
`BitHelper.cs`, and adds a test. It sizes the bitmap from the tree's *height*:

```csharp
// SortedSet.cs (PR) 1387-1438
int maxHeight = GetApproximateMaxHeight();
// maxHeight = 12 needs 8kb for bitHelper, use fallback with HashSet if maxHeight > 12 ...
if (maxHeight > 12)
    return CheckUniqueAndUnfoundElementsFallback(other, returnIfUnfound);
int indexLimit = (1 << maxHeight);
... BitHelper over ToIntArrayLength(indexLimit) ints ...
foreach (T item in other)
{
    int index = InternalIndexOf(item);
    if ((uint)index < (uint)indexLimit) { if (!bitHelper.IsMarked(index)) { bitHelper.MarkBit(index); uniqueFoundCount++; } }
    else if (index < 0) { unfoundCount++; if (returnIfUnfound) break; }
    else
    {
        // Safe guard: since maxHeight isn't guaranteed, we might need to grow the bitHelper.
        indexLimit = (int)BitOperations.RoundUpToPowerOf2((uint)index);
        ... copy the span into a larger one ...
    }
}

// SortedSet.cs (PR) 2076
internal virtual int GetApproximateMaxHeight() => 2 * BitOperations.Log2((uint)count + 1);

// SortedSet.TreeSubSet.cs (PR) 324
internal override int GetApproximateMaxHeight()
    => Math.Max(_underlying.GetApproximateMaxHeight() - _rootLevel, 0);
```

Supporting changes:
* `FindRange(..., out int level)` returns the depth at which the range search stops. The
  view stores it as `_rootLevel` (`TreeSubSet.cs:27`, `:93`).
* `InternalIndexOf` was `virtual`. `TreeSubSet` overrode it with an in-order `foreach` over
  the view, counting only in-range elements. The PR makes it **non-virtual** and deletes
  the override, so a view now runs the base search from its own `root`.
* `CheckUniqueAndUnfoundElementsFallback` uses a `HashSet<Node>` of seen nodes.
* `BitHelper.Span` exposes the span for the growth branch.
* The new test `SortedSet_Generic_SetEquals_SameButAllElementsDuplicated` exercises sets
  only, not views.

At a set this is right, and §7 proves it. The height of a red-black tree of `n` nodes is at
most `2 * floor(log2(n + 1))`, so every position is below `1 << maxHeight`.

---

## 5. The counterexample: dotnet/runtime#133116 at a view

### 5.1 Why

At a view, the non-virtual `InternalIndexOf` searches the subtree under the view's `root`.
By §1.2, that subtree may hold nodes **outside** the view's range, and the search finds
them. An out-of-range item of `other` then gets a non-negative position, so it is counted as
*found* (`uniqueFoundCount++`) instead of *unfound*.

### 5.2 The instance

```csharp
var s = new SortedSet<int>(); for (int i = 0; i < 10; i++) s.Add(i);
// set tree: 3(1(0 2) 5(4 7(6 8(. 9))))      height 5
var v = s.GetViewBetween(2, 5);
// v = {2, 3, 4, 5}, Count = 4, v.root = 3 (the set's root: 3 is in range), _rootLevel = 0
var other = new List<int> { 2, 3, 4, 9 };
```

| step | value |
|---|---|
| `v.GetApproximateMaxHeight()` | `max(2*log2(11) - 0, 0) = 6`, so `indexLimit = 64` |
| `InternalIndexOf` for 2, 3, 4, 9 | 4, 0, 5, **30** (9 is reached via 3 → 5 → 7 → 8 → 9) |
| counts | `UniqueCount = 4` (2, 3, 4, **9**), `UnfoundCount = 0` |

The comparisons then give:

| call | PR | correct (.NET 10) |
|---|---|---|
| `v.SetEquals(other)` | **True** | False (9 ∉ v, 5 ∉ other) |
| `v.IsSubsetOf(other)` | **True** | False (5 ∉ other) |
| `v.IsProperSubsetOf(other)` | False | False |
| `v.IsProperSupersetOf(other)` | False | False |

A set built by the constructor (`new SortedSet<int>(Enumerable.Range(0, 10))`) has the tree
`4(1(0 3(2 .)) 7(6(5 .) 9(8 .)))`, and `v.SetEquals(other)` is again `True`.

These outputs come from the PR's sources compiled into a stand-alone harness. The same
harness found the bug by differential testing against `HashSet<T>` on random sets and
views.

### 5.3 The proof finds it

`harness/experiments/pr133116-unfixed.patch` reverts the one line in §6 to the PR's
`int index = InternalIndexOf(item);`. Running `run.sh pr133116-unfixed` checks the method
twice, as the translator replicates it at a view (doc/translation.md R32.13):

| module | result |
|---|---|
| `Func_SortedSet_CheckUniqueAndUnfoundElements` (set) | **verifies** |
| `Func_TreeSubSet_at_SortedSet_CheckUniqueAndUnfoundElements` (view) | **fails**, one error |

The single error is:

```
SortedSet.cs(2303,13): error PALCS0600: ...
Failed to prove: SortedSetCount.loop_inv_s ... (Seq.upd marked index true) ... (uniqueFoundCount + 1) ...
```

It is in the "found, not yet marked" branch. At the view, `ok` is `in_range`, so the
invariant's `uniq == found(prefix)` counts only in-range items. The code's `index` is
`heap_index` in the range-root subtree, which is non-negative for an out-of-range node
such as 9. `loop_step_s` requires the marked position to be
`index_s = index_of (ok_s ...) tr x`, which is -1 outside the range. The code's position is
not that, so the found count grows where the specification's does not.

---

## 6. The patch

The fix is one line in the loop (`SortedSet.cs:2318`):

```csharp
// pal: FIX for #133116. `InternalIndexOf` searches the view's range-root subtree, which may hold
// out-of-range nodes; without the range check, an out-of-range item counts as found.
int index = IsWithinRange(item) ? InternalIndexOf(item) : -1;
```

At a set, `IsWithinRange` is `true` and the line is the PR's. At a view, an out-of-range
item is unfound, as it was before the PR. An alternative fix would restore the virtual
override, but that brings back an O(Count) walk per item, which the PR wanted to remove.

For upstream, the change is to replace PR line 1412 `int index = InternalIndexOf(item);`
with the line above.

The annotations the proof needs alongside the fix:
* **`IsWithinRange` frame conditions.** The view's override (`TreeSubSet.cs:187-189`) now
  ensures that `root`, `comparer`, `_min` and `_max` are unchanged, so the loop's facts
  about the tree survive the call.
* **The range, named once for a set and a view** (`SortedSet.cs:113-122`, overridden at
  `TreeSubSet.cs:43-48`). The virtual `[Spec]` members `SpecRangeLo/Hi/La/Ua/Tree/Comparer`
  are bound as follows:
  * a set has no bound (`SortedSetCount.None`) and is its own tree;
  * a view has `One(_min)`, `One(_max)`, its flags, and the set's tree.

  A view's replica of the method reads the overrides (R37.7). One invariant then serves both
  copies of the method: `ok_s`/`root_s` reduce to `all_ok`/the whole tree for the set, and
  to `in_range`/`range_root` for the view.
* **The view's root depth.** `SpecRootOk` (`TreeSubSet.cs:54-58`) states that a non-null
  root is `_rootLevel == RangeDepth(...)` below the set's root. It holds after the
  constructor and after every re-synchronisation. `FindRange` ensures
  `level == RangeDepth(...)` (`SortedSet.cs:1210`).

---

## 7. The revised proof

### 7.1 What is proved

The method's contracts, at the set (`SortedSet.cs:2248-2252`):

```csharp
[Requires("Pal.Contents(other).Length <= int.MaxValue")]
[Ensures("(Result.UnfoundCount > 0) == (SortedSetCount.UnfoundAll(@this.SpecComparer, @this.SpecItems, Pal.Contents(other)) > 0)")]
[Ensures("Pal.Implies(!returnIfUnfound || Result.UnfoundCount == 0, Result.UniqueCount == SortedSetCount.FoundAll(@this.SpecComparer, @this.SpecItems, Pal.Contents(other)))")]
```

At a view (`SortedSet.cs:2253-2256`, `At = typeof(SortedSet<>.TreeSubSet)`), the same
contracts hold with `UnfoundRange`/`FoundRange` over `_min`, `_max`, `_lBoundActive` and
`_uBoundActive`.

`ViewCounts` (`Count.cs`, end of file, R37.5) is a client: `s.GetViewBetween(lo, hi)`
followed by the call. It verifies against the `found_range`/`unfound_range` contract, so a
fresh view does satisfy the replica's precondition.

The proof also establishes:
* **The bitmap is big enough, and its growth branch is dead.** `SortedSet.cs:2340-2346`
  is `Pal.Unreachable()` (R37.4).
* **`GetApproximateMaxHeight` is exact enough** (`SortedSet.cs:3238-3255`, override in
  `TreeSubSet.cs:505-511`). It ensures `Height <= Result` for the set's tree, and for the
  view's root subtree at a view.
* **No `int` overflow** occurs in the counters (by the precondition on `other`'s length),
  in `1 << maxHeight` (by `shift_one`, `maxHeight <= 12`), or in `InternalIndexOf`
  (`Height <= 12 <= 30`).

### 7.2 How: the lemmas

The method body's ghost calls are at `SortedSet.cs:2291-2350`. Each binds to a lemma in
`SortedSetCount.fst`:

| step | C# (`SortedSet.cs`) | lemma (`SortedSetCount.fst`) |
|---|---|---|
| height bound, set | `GetApproximateMaxHeight` (`:3250`) | `red_black_height` (373): a red-black tree of `n` nodes has height `<= 2*log2_nat(n+1)`, via `rb_height` (352) and `log2_ge` (363) |
| height bound, view | `TreeSubSet.cs:507` | `range_root_height` (394): `height(range_root) + range_depth <= height(tree)` |
| `1 << maxHeight` | `ShiftOne` (`:2291`) | `shift_one` (436): no overflow, equals `2^h` for `h <= 12` |
| every position fits | `FitsPow2` (`:2301`) | `fits_pow2` (449) from `pos_bound` (348) / `heap_index_bound`: `fits tr (2^h)` |
| set/view lookup facts | `LookupIntro` (`:2300`) | `lookup_intro_s` (647): the range root's search finds exactly the in-range keys (`range_lookup`) |
| invariant holds initially | `LoopStart` (`:2302`) | `loop_start_s` (658) |
| one item | `LoopStep` (`:2319`) | `loop_step_s` (686) → `loop_step_g` (664) → `step` (286) |
| early exit | `LoopDone` (`:2335`) | `loop_done_s` (724) |
| loop exit | `LoopEnd` (`:2350`) | `loop_end_s` (732) |
| contract form | `Counts` (`:2352`) | `counts_s` (750): `found_s` is `found_all` with no bound and `found_range` with `one lo`/`one hi` |
| empty set or range | `EmptyCounts` (`:2274`) | `empty_counts_s` (741) |

The key step is `loop_step_g`. If `p = index_of ok tr x` is below `|m|`, all three branches
preserve the invariant:
* when `p >= 0` and the bit is clear, set the bit and add one to the found count;
* when `p >= 0` and the bit is set, change nothing;
* when `p < 0`, add one to the unfound count.

The lemma relies on two facts:
* **`hit_phit`**: the bit is set exactly when an earlier equal item exists;
* **`heap_index_inj`/`heap_index_equiv`**: positions are injective on non-equivalent keys.

The loop invariant (`SortedSet.cs:2305-2315`) carries the following, among other facts:
* `Lookup`: the lookup facts;
* `Fits(root, indexLimit)`: every position fits;
* `Height <= 12`;
* `marked.Length == indexLimit`;
* `LoopInv`;
* the pins on the `SpecRange*` members, which keep a view's bounds unchanged across the
  loop.

With `Fits`, the precondition `index_s < |m|` of `loop_step_s` holds, and the third branch,
growth, is unreachable.

### 7.3 Trust base

These pieces are taken on trust:
* **`CheckUniqueAndUnfoundElementsFallback`** is `[Admit]` (`SortedSet.cs:2360`, R37.3).
  `HashSet<Node>` with reference equality on nodes is not modelled. Its contract is the
  bitmap version's.
* **Bindings.** `BitOperations.Log2` is bound to `log2_u32`, whose body proves it equals
  `log2_nat` (R21.5). `RoundUpToPowerOf2` is bound to `round_up_pow2`, which occurs only in
  the dead branch.
* **The bitmap is a `bool[]`, not a `BitHelper`** (R37.2). This is a change to the verified
  code. The `bool[]` has `1 << maxHeight` entries where `BitHelper` has
  `ceil(2^maxHeight / 32)` ints, but the bits mean the same.
* **The callers' count paths are not exercised by the verified callers.** The verified
  `IsSubsetOf`/`SetEquals`/... require `other` to be a `SortedSet<T>` with the same comparer
  (`[Exactly]`, R27.46-R27.49), so their call sites are `Pal.Unreachable()`. The method is
  verified against its own contract. The step "`found_all == Count` iff `other` contains
  every element" (§3.1) is not mechanised.

### 7.4 Translator changes

Accepting the PR's code as written needed four translator changes, each documented in
doc/translation.md §37:
* **R37.6**: `out _field` in a view's constructor (`FindRange(..., out _rootLevel)`).
* **R37.7**: a base's virtual `[Spec]` property read at a view's replica.
* **R37.8**: a nested struct named by a signature (`ElementCount`) under
  `[TranslateAnnotatedOnly]`.
* **R37.9**: a non-tail escaping `if` whose arm moves a node pointer (`FindRange`'s loop).

---

## 8. Reproducing everything

The F* toolchain is set up as described in the repository's README. Then:

```sh
cd samples/dotnet-runtime/pal/SortedSet

# The revised proof: the whole harness, including the referenced List/Queue/Stack units.
make -j$(nproc) -k          # rc=0

# §3: the original method fails at loop_inv_s.
experiments/run.sh original             # "verification failed (expected)"

# §5: the PR without the fix verifies at the set and fails at the view.
experiments/run.sh pr133116-unfixed     # "verification failed (expected)"
```

`run.sh` works as follows:
* it applies the patch to `SortedSet.cs`;
* it runs `make translate`, then checks only the method's modules;
* it reverts the patch on exit.

Run plain `make` first, so that the rest of the harness is checked.

The C# counterexamples in §2.2 and §5.2 need only a .NET SDK:
* §2.2 runs against .NET 10's own `SortedSet<T>`.
* §5.2 needs the PR's `SortedSet.cs`, `SortedSet.TreeSubSet.cs` and `BitHelper.cs`, compiled
  into a console project with `InternalsVisibleTo` or reflection to show positions.
  `SetEquals`/`IsSubsetOf` alone suffice to see the wrong answers.

Related documents:
* `samples/dotnet-runtime/FINDINGS.md` §1.1 (the original bug) and §1.3 (the PR's bug).
* doc/translation.md §27 (R27.14, `InternalIndexOf`) and §37 (this proof).
