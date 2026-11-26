# Root cause and correctness of the range guard

## 1. Two different bugs

The earlier issue, dotnet/runtime#102118, concerns duplicate counting in
`SortedSet<T>.CheckUniqueAndUnfoundElements`. The old implementation sized a
bitmap by `Count`, but `InternalIndexOf` returns a position in an implicit
complete binary tree:

```text
root: 0
left child of k:  2*k + 1
right child of k: 2*k + 2
```

Those positions are not dense ranks. A real tree can have only 18 nodes but a
node at position 62. One 32-bit bitmap word cannot remember that node.
`BitHelper.IsMarked` returns false beyond its span and `MarkBit` ignores the
out-of-bounds position, so duplicates can be counted as new distinct elements.

The proposed fix in
[dotnet/runtime#133116](https://github.com/dotnet/runtime/pull/133116) sizes the
bitmap using an estimated red-black-tree height and uses a `HashSet<Node>`
fallback above height bound 12. It also removes virtual dispatch from
`InternalIndexOf` and removes the `TreeSubSet` override, which previously
enumerated the range-filtered view to assign dense indexes.

The regression isolated here is **not another bitmap capacity failure**.
The newly shared raw lookup does not implement a view's membership semantics.
The one-line correction retains the PR's height-based bitmap sizing.

## 2. A view is not a physically trimmed tree

`GetViewBetween(lower, upper)` returns a live `TreeSubSet`. Its `root` is found
by descending to a node within the requested bounds. It shares the underlying
nodes; it does not prune or copy their child pointers. That root's descendants
can include keys below the lower bound and above the upper bound.

Consequently, these are different predicates:

```text
physically present: the item has a matching node below view.root
logically present:  physically present AND within the view's active bounds
```

`TreeSubSet.IsWithinRange` uses the set's comparer and inclusive active bounds.
Its `FindNode` override first rejects out-of-range items, so `Contains` already
has the right semantics. Its enumerator also filters the range. In contrast,
the now-nonvirtual `InternalIndexOf` searches child pointers without a range
test. Removing the old override silently discarded that filter.

The four bitmap-counting callers assume counts are relative to the logical
receiver. They do not know that the inherited lookup has counted nodes outside
the view, and they compare those counts to the view's range-filtered `Count`.

## 3. Minimal deterministic example

```csharp
var set = new SortedSet<int>();
for (int i = 0; i < 10; i++)
    set.Add(i);

var view = set.GetViewBetween(2, 5);
var other = new List<int> { 2, 3, 4, 9 };

Console.WriteLine(string.Join(", ", view)); // 2, 3, 4, 5
Console.WriteLine(view.Contains(9));        // False
Console.WriteLine(view.SetEquals(other));  // PR: True; correct: False
Console.WriteLine(view.IsSubsetOf(other)); // PR: True; correct: False
```

Use a `List<int>` (or another general enumerable) for `other`. A `SortedSet`
with the same comparer takes specialized comparison paths and can mask this
bug. This code must run against the pinned PR implementation, as the package
does, rather than whichever `SortedSet` happens to ship with an installed SDK.

Sequential insertion creates this physical tree (`.` means no child):

```text
3(1(0 2) 5(4 7(6 8(. 9))))
```

The root `3` is within `[2,5]`, so it is also the view's root. The view does not
cut off `0`, `1`, or `6` through `9`.

| Enumerated item | Raw `InternalIndexOf` | In view? | Unfixed classification |
|---|---:|---|---|
| 2 | 4 | yes | found |
| 3 | 0 | yes | found |
| 4 | 5 | yes | found |
| 9 | 30 | **no** | **found** |

The actual height bound is 6, giving an index limit of 64. Every listed index
fits: no overflow, ignored bit, resizing, or fallback explains this failure.
The unfixed counts are `(UniqueCount, UnfoundCount) = (4,0)`, while the correct
counts for this enumeration are `(3,1)`. Since `view.Count` is 4, both equality
and subset tests incorrectly succeed, even though `5` is missing.

The executable prints the actual raw index of `9` (30), `Contains(9)` (false),
and the height bound (6) in both variants. The fix deliberately leaves raw
lookup behavior unchanged and corrects its use by the counting loop.

## 4. All four callers are affected

For `V = {2,3,4,5}`, let `u` count distinct found elements and `f` count unfound
occurrences in the processed prefix.

| Caller | Its counting-path condition | Witness `other` | Unfixed `(u,f)` |
|---|---|---|---|
| `SetEquals` | `u == Count && f == 0` | `{2,3,4,9}` | `(4,0)` |
| `IsSubsetOf` | `u == Count` (also tests `f >= 0`) | `{2,3,4,9}` | `(4,0)` |
| `IsProperSubsetOf` | `u == Count && f > 0` | `{2,3,4,9,10}` | `(4,1)` |
| `IsProperSupersetOf` | `u < Count && f == 0` | `{2,3,9}` | `(3,0)` |

Every witness should return false, and every unfixed result is true.
`10` is absent even from the underlying tree, supplying the unfound element in
the proper-subset witness. For proper superset, `9` must instead cause failure.
`IsSupersetOf` is not a fifth caller: its general-enumerable path uses
`ContainsAllElements`, not this counting helper.

The defect can cause false negatives too. With `other = {9,2,3,4,5,9}`, the
view is a subset and a proper subset, but the unfixed helper counts five
distinct physical nodes against a logical count of four. Both tests return
false. This is included in the extra edge cases.

## 5. The production change

In the pinned source, `SortedSet.cs:1412`:

```diff
-                int index = InternalIndexOf(item);
+                int index = IsWithinRange(item) ? InternalIndexOf(item) : -1;
```

An out-of-range item now uses the existing absent sentinel. Converting `-1`
to `uint` fails the existing index-limit check; the following `index < 0`
branch increments `unfoundCount` and observes `returnIfUnfound`. No new
counting branch or special-case public API behavior is needed.

This does not restore the former virtual enumeration-based index lookup.
It keeps logarithmic tree lookup and the PR's sparse-index bitmap strategy.
It does not change tree shape, fields, allocation policy, count/version
maintenance, bitmap sizing, or the large-tree fallback.

## 6. Why this is the right membership test

Let `P` be the keys physically below the receiver's current root, interpreted
modulo equality induced by its comparer. Let `R(x)` be `IsWithinRange(x)`.
The logical receiver is `V = {x in P | R(x)}`. For an ordinary set, `R` is
always true; for a view it is the active inclusive bounds.

Under the existing search-tree and bitmap-bound invariants:

1. If `R(x)` is false, `x` cannot belong to `V`. Returning `-1` is correct,
   regardless of whether a physical node for `x` exists.
2. If `R(x)` is true, the existing lookup finds a node exactly when `x` belongs
   to `P`, equivalently to `V`. Its position and bitmap mark are unchanged.
3. Distinct in-range nodes retain distinct positions, while comparer-equal
   items find the same node. The same bitmap therefore still deduplicates
   found elements, including non-identical comparer-equal values.

Thus, for each processed prefix, the bitmap marks exactly its found nodes
in `V`, `uniqueFoundCount` counts distinct found comparer-equivalence classes,
and `unfoundCount` counts occurrences outside `V`. The guard repairs the
lookup/classification premise needed by this existing loop invariant.

For `returnIfUnfound == false`, processing completes normally. For
`returnIfUnfound == true`, encountering any item outside `V` is sufficient to
reject equality or proper superset, so the existing early exit remains sound.
We do not claim that early-return counts describe the unprocessed suffix.

For ordinary sets the guard returns true, preserving each lookup and count.
For views it adds at most two comparer calls per item and skips raw lookup
entirely for out-of-range items. This preserves the lookup path's asymptotic
complexity; it is not a claim of zero constant-factor cost or a benchmark.

The argument assumes a valid stable comparer, a well-formed current tree, and
no concurrent or reentrant mutation during enumeration. A view's `Count`
access at the start of the helper synchronizes its root/count through existing
version checks. The patch does not add synchronization or make guarantees for
arbitrary side-effecting comparers.

## 7. Fallback, scope, and evidence

The height-above-12 fallback already calls virtual `FindNode`; the view
override performs `IsWithinRange` before searching. That path is not changed.
The 130-node control prints height bound 14 to demonstrate that it actually
selects the fallback and passes both before and after the patch.

The standalone executable compiles the pinned upstream implementations, not a
reimplementation of their algorithms. Its 18-node duplicate control passes
in both variants, showing the original PR's intended correction is retained
for that witness. Construction modes, both sides of the range, duplicate
inputs, and non-default comparers give additional targeted coverage.

The proposed xUnit method is executed using minimal local test infrastructure.
The full runtime test project has not been run. This package does not prove
every property of the upstream PR: it isolates and repairs the missing range
filter, assuming the other search/indexing invariants above. It deliberately
does not modify the growth branch, integer-overflow behavior, or unrelated
Debug assertions. Earlier PAL proof work motivated this finding, but no PAL
changes or proof infrastructure are included in the proposed runtime diff.

## 8. Pinned source references

All line numbers below are in revision
`254919ae80190e850cbac0275b499915e018e681`; see [SOURCES.md](SOURCES.md).

| Location | Relevant behavior |
|---|---|
| `SortedSet.cs:293` | Base `IsWithinRange` returns true |
| `SortedSet.cs:690`, `:721` | Virtual node lookup versus nonvirtual raw index lookup |
| `SortedSet.cs:1191`, `:1227`, `:1286`, `:1314` | Four callers of the counting helper |
| `SortedSet.cs:1368-1444` | Bitmap counting loop and changed line |
| `SortedSet.cs:1446-1480` | Fallback uses `FindNode` |
| `SortedSet.TreeSubSet.cs:114` | Comparer-based inclusive bounds |
| `SortedSet.TreeSubSet.cs:278-289` | Range-aware `FindNode` override |
| `SortedSet.TreeSubSet.cs:299-326` | View synchronization and height bound |

## 9. Implementation-backed public-call proof

The surrounding PAL-csharp repository now contains a separate verified client,
`samples/dotnet-runtime/pal/SortedSet/PublicRegression.cs`:
`ViewSetEqualsListFalse`. It constructs the set by inserting 0 through 9,
obtains `GetViewBetween(2,5)`, allocates an actual List, adds exactly
`2,3,4,9`, and calls the public `view.SetEquals(other)`. Its postcondition is
`!Result`: the returned Boolean is false, not a derivation of logical False.
It does not first read the view's Count.

The active SetEquals contract no longer restricts `other` to another exact
SortedSet. It relates the result to two-way membership between the receiver's
logical sequence and `Pal.Contents(other)`, preserving both sequences.
Comparer consistency is required only when the source is a SortedSet whose
comparer reports equality with the receiver's comparer.

This is supported by implementation proofs, not just imported promises:

1. Ordinary and bounded-view enumeration implementations establish their logical
   contents and sortedness. The generic iterator interface exports these checked
   facts and retains the actual source resources.
2. The List's construction, source identity, contents, and failed SortedSet cast
   are checked. Successful ordinary/view casts are covered separately; the
   public implementation is not verified by assuming its fast path unreachable.
3. The actual counting helper proves counts over the range-filtered logical
   sequence. Since `9` is outside `[2,5]`, the actual public equality contract
   implies the client's false result.

From the repository root, run:

```sh
python3 samples/dotnet-runtime/pal/SortedSet/public_range_negative.py
```

This first clears the isolated positive cache and checks the public client's
implementation dependency closure. It then copies the sources and removes
**only** `IsWithinRange(item) ? ... : -1` from the counting loop. The affected
helper, SetEquals, and client checked artifacts are excluded from the reused
dependencies. The unguarded view helper must fail its own proof, with no checked
artifact produced. A translation error is not accepted as that failure.
The positive source remains untouched.
The fresh positive closure passes; the unguarded helper fails its
`SortedSetCount.loop_inv_s` obligation and produces no checked artifact.

Checking the client alone against an unchanged, imported helper contract would
not detect this mutation: modular verification would still let it conclude
false. The negative therefore checks the changed implementation, not a request
for the client to prove a contradiction. The executable experiment above
separately demonstrates that the unguarded implementation actually returns true
on this concrete witness.

**Scope and trust:** the view SetEquals proof requires at most 126 underlying
items, covering this ten-item construction and keeping execution on the checked
bitmap path. The existing admitted large-tree fallback is outside that proof;
its contract has not been strengthened. The proof also relies on the documented
trusted correspondence between the default Int32 comparer and mathematical
integer order, and the repository's compiler/runtime model. Other public set
comparisons have not had their enumerable preconditions generalized by this
work. This is not certification of the entire upstream PR or arbitrary C#
enumerables without checked source evidence.

The formal experiment uses the annotated repository sample, whereas this
directory's executable experiment uses the pinned upstream source snapshot.
No PAL annotations, compiler changes, toolchain patches, or proof infrastructure
belong in the proposed upstream one-line production patch.
