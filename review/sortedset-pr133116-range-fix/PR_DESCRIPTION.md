# Draft: Preserve SortedSet view bounds in unique-element counting

**Local draft only; not submitted.** Intended as a follow-up to
dotnet/runtime#133116 at `254919ae80190e850cbac0275b499915e018e681`.
The proposed code diff consists only of `fix.patch` and `regression.patch`.

## Summary

Apply the receiver's range predicate before using `InternalIndexOf` in
`CheckUniqueAndUnfoundElements`:

```diff
-                int index = InternalIndexOf(item);
+                int index = IsWithinRange(item) ? InternalIndexOf(item) : -1;
```

This preserves the height-based bitmap fix for dotnet/runtime#102118 while
correcting membership for bounded `SortedSet<T>` views.

## Root cause

dotnet/runtime#133116 makes `InternalIndexOf` nonvirtual and removes the
`TreeSubSet` override. The old override enumerated the range-filtered view;
the shared implementation searches raw child pointers.

A view's root subtree is not trimmed to the view's bounds. A node can be
reachable below that root while being excluded from the logical set.
Counting such a node as found breaks the relationship between `UniqueCount`
and the view's `Count`.

For example:

```csharp
var set = new SortedSet<int>();
for (int i = 0; i < 10; i++)
    set.Add(i);

var view = set.GetViewBetween(2, 5); // {2, 3, 4, 5}
var other = new List<int> { 2, 3, 4, 9 };

view.SetEquals(other);  // true on the pinned PR; should be false
view.IsSubsetOf(other); // true on the pinned PR; should be false
```

`9` is physically reachable but outside the view; `5` is missing from `other`.
The unguarded lookup yields index 30 for `9`, which fits the allocated
bitmap. The helper incorrectly reports four unique found elements and zero
unfound elements. This is a membership error, not another sizing failure.

`IsProperSubsetOf` and `IsProperSupersetOf` also use this helper and have
analogous counterexamples, included in the regression.

## Why the fix is correct

For ordinary sets, `IsWithinRange` always returns true, preserving the
existing lookup. For views it checks the active inclusive bounds with the
receiver's comparer. Out-of-range items get the existing absent sentinel,
which feeds the existing unfound/early-exit branch. In-range lookup positions,
bitmap deduplication, and sizing are unchanged.

The guard restores the distinction between physical subtree membership and
logical view membership without restoring an enumeration-based lookup.
The large-tree fallback is unchanged and already calls range-aware virtual
`FindNode`. There are no public API, layout, or PAL dependencies.

## Regression and validation

The proposed theory is added to the existing integer `TreeSubSet` fixture.
It uses both incremental insertion and construction from an enumerable, and
both lower- and upper-bound violations. `other` is a `List<int>` so the
general counting path is exercised, rather than the same-comparer SortedSet
fast path.

The accompanying local package compiles the actual pinned upstream sources
and runs identical tests against the unmodified PR and the one-line fix:

- All four proposed theory rows fail before the fix and pass afterward.
- All four direct API witnesses change from incorrect true to correct false.
- Twenty control assertions pass in both variants, including the original
  18-node duplicate example and the large-tree fallback.
- Twelve additional edge assertions cover outside-first duplicates,
  descending ordering, and case-insensitive equality; the six baseline
  failures are eliminated.

The proposed test body was executed with minimal local assertion/attribute
support, not the full runtime xUnit project. Full runtime-suite validation
remains to be done before submission. Both patches apply cleanly to the
pinned head. Unrelated Debug-only assertion signature issues in that head
are left untouched; the standalone runs use Release.

See `ROOT_CAUSE.md` in the local review package for the prefix-count invariant,
caller-by-caller witnesses, assumptions, and exact source references.
Its section 9 also records a separate implementation-backed public
`SetEquals(List)` proof: the guarded dependency chain verifies, while removing
the guard rejects the helper's implementation proof. That view theorem is
limited to at most 126 underlying items and retains the documented default-order
trust assumption; it is not a proof of the large-tree fallback or the entire PR.
None of that proof infrastructure is part of the proposed runtime diff.
