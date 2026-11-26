# Capability prerequisites: implemented scope

`SortedSetCapability.fst` verifies observation adapters calling the **actual
generated** ordinary and TreeSubSet `Count`/`Comparer` implementations.
`actual_view_dispatch` casts and dispatches through the generic
`Pulse.Lib.CSharp.Capability` descriptor. The view retains the complete underlying
tree model plus its own exclusive mutable cache cell and fixed bounds. Its
logical sequence is filtered; no ordinary SortedSet invariant is opened for the
view. Wrong base-count substitution and duplicate view ownership are negative
proofs.

The C# frontend installs checked scalar observations and resource-producing
iterator descriptors in `test/nominal_observations`. These connect the actual
public SetEquals implementation to its List-backed false-result client.
Nominal installation needs construction evidence or checked dynamic
capabilities; an arbitrary subclass must not inherit a static interface
protocol by assumption. Known borrowed-view iterator owners now have
a specialized representation and checked virtual dispatch. The shared active
iterator proof and actual view iterator client now check.

`CapabilityRegression.cs` independently verifies the actual static construction
of 0..9, local `GetViewBetween(2,5)`, and `Contains(9) == false`. This is an owner
binding regression, not a substitute for public SetEquals. Its numeric conclusion
uses the documented, trusted Int32 default-order correspondence.

Compiler prerequisites also exercised in `test/enumerable_protocol`:

* forwarding the same source descriptor across renamed parameters;
* lending its existing snapshot to a snapshot-only helper and restoring it;
* positive `as`/null/`&&` guards without an `else`, with normal-return cleanup;
* preserving original iterator domains and exceptions alongside protocol laws;
* explicitly typed mutable-struct postbinders on normal and exceptional exits.

Run from this directory:

```
python3 capability_checks.py fresh
python3 capability_checks.py negative-list
```

Both use isolated outputs under `obj/capability*`. The negative List experiment
removes only its first enumerator version-check block, translates the changed
C#, and requires the actual MoveNext implementation proof to fail. It never
edits List.cs or the positive target cache.

## Actual public-dispatch probes

```
python3 public_dispatch_checks.py view-iterator
python3 public_dispatch_checks.py exact-view
python3 public_dispatch_checks.py general-public
```

These are integration probes over the active source. Each writes isolated inputs
under `obj/public-dispatch`. Every successful translation is
followed by a fresh dependency-closure check; an unproved implementation makes
the probe fail.
The first demands the actual view's `GetEnumerator`; the second demands the
actual inherited `SetEquals` body on a view, even with an exact SortedSet input.
The third calls the persistent `PublicRegression.ViewSetEqualsListFalse` client.
Active SetEquals no longer requires Exactly: its result contracts and fallback
lemmas use `Pal.Contents(other)`, with comparer consistency conditional on nominal
assignability. The harness does not rewrite those contracts or runtime branches,
and no cast is assumed to fail.

Both SetEquals clients demand a false result and apply an out-of-range witness.
The focused exact-dispatch client uses a singleton SortedSet containing 9;
the required general-public regression still uses the exact List `[2,3,4,9]`.
It allocates that List directly, so factory-return exactness inference is not a
prerequisite for the regression.
The exact-SortedSet-input client's complete dependency closure now verifies.
Explicit view contracts for
HasEqualComparer and SetEquals expose comparator correspondence, logical set
equality, and preservation of both input sequences. `SpecCountOk` requires
correctness only when the cache version is current; it does not require reading
Count before the call. The short-circuit readonly-getter join and Current's
untouched-owner framing have been repaired. Iterator methods now preserve
walking readiness and conditional cached-count validity. Opaque suffix and
equality-progress lemmas keep recursive slice rewriting out of the comparison
loop. The loop's current-element observations are now tree-free:
`SpecCurrentItems` is empty or a singleton. Actual ordinary/view MoveNext and
Current prove its pending-head correspondence; no default element is needed
to define it. Legacy tree contracts remain available to existing callers.
The actual enumerator now carries `EnumerationState` metadata, and its additional
ordinary/view MoveNext, Current, and Dispose laws check. Initialize and both
constructor overloads expose their cleared-current state; the factories retain
their concrete readiness/pending facts and additionally guarantee null current.
The new ordinary `EnumerationProof` checks a real GetEnumerator/MoveNext/Current/
Dispose traversal against the complete logical sequence. An explicit prefix-step
lemma and branch join carry its yielded-prefix and termination facts.
The inherited view protocol specialization is now emitted and its complete
traversal proof checks too. Both authored protocols additionally establish
`Pal.StrictlySorted(SpecComparer, SpecItems)` using the checked range-filter lemma.
The checked sortedness facts are exported through the generic nominal interface,
not inferred from the collection's name or assumed on a successful cast.
The inherited two- and three-argument `CopyTo` implementations now have checked
view contracts with the original exception guards. The view traversal preserves
conditional count-cache validity, including across its three loops.
The inherited counting-helper call now lends and restores a checked
enumerable snapshot. Both ordinary and inherited-view SetEquals bodies verify.
HasEqualComparer uses logical sequence frames instead of redundant structural
frames; exact calls still preserve their full models in the spatial contract.
Its ordinary/view implementations also verify with abstract nominal arguments.

The view SetEquals contract has **no 126-item restriction**. The ordinary and
view HashSet fallbacks prove their counting and cache-preservation contracts,
using the actual lazy allocation, reference-key membership, insertion, and
early exit. The main helper therefore preserves view coherence and conditional
count validity on both paths. Capacity exhaustion is exposed as a possible
`ArgumentException` only for input lengths above `0x7FFFFFC3`, not hidden behind
a smaller input precondition.

`CreateLargeSet` constructs all 256 distinct keys with a proved exact sequence.
`LargeSetEqualsListTrue` constructs the matching List and proves public equality;
`LargeViewSetEqualsListFalse` supplies duplicates and an out-of-range key and
proves public view equality false. Runtime checks independently require the
height bound to exceed 12 and exercise duplicates, growth, misses, and empty
input against the same source. HashSet insertion/resizing snapshots use erased
`Pal.Capture` calls rather than executable specification-only initializers.

`SortedSetInductive.RangeCounts` proves that range-restricted found/unfound counts
are exactly the ordinary counts over the filtered logical sequence. This checked
bridge, including empty and disabled bounds, connects the actual counting helper
to SetEquals's two-way logical equality contract; it adds no assumptions.

`python3 public_range_negative.py` is the positive/negative gate.
It first demands a fresh public List-client dependency closure,
then removes only the actual range guard in isolated source and requires the
affected implementation proof to fail. A translation failure or missing positive
implementation artifact cannot count as the expected negative.
The fresh active-source client closure passes. Removing the guard rejects the
view helper's `SortedSetCount.loop_inv_s` obligation and produces no checked
helper artifact.

Disjoint List-source installation now verifies actual construction of
`[2,3,4,9]`, a failed SortedSet cast, and restoration of ownership and contents
(`make -C test/nominal_observations list-miss`). Resource-producing iterator
dispatch and checked source facts now support the public SetEquals proof.
`make -C test/nominal_observations iterators actual-iterators guard-dependency`
also covers actual ordinary/view successful casts and rejects nine invalid
iterator protocols. Implicit scope release reclaims cursor and snapshot storage
without inventing an executable Dispose call.
The former borrowed-receiver call failure also reproduces without C# classes or local allocation:
the pinned F* core checker's environment-local binder IDs collide with ordinary
global freshening IDs. `test/nominal_observations/CALL_DIAGNOSTIC.md` records the
class-free controls and failures. The core freshness repair passes those controls
and the unchanged generated call. It is packaged as
`tools/fstar-core-freshness.patch`, digest-pinned by `tools/fstar-source.txt`,
and installed locally. The original compiler is preserved for the before/after
experiment; no contract or allocation workaround is used.
The pinned patch also deep-compresses solved annotation unification nodes before
Pulse's return and bind-continuation freshness checks. This fixes a false
free-variable clash in stack-local cleanup posts without bypassing either check.
Its `ReturnPostCompression` regression and the compiler's generic optional-owner
regression retain inferred dictionary annotations. Both repairs must be included
in the same installed executable and native compiler artifacts.
The other three comparison methods retain their existing Exactly restriction.
Generalizing them also reaches the separately unsupported
nongeneric `ICollection` test. The logical `SpecItems` and `SpecComparer`
projections are now virtual, with explicit view overrides for filtered contents
and the actual comparer field (coherence equates it with the underlying comparer).
The concrete `ViewExcludesNine` client also proves
`!AllHit(view.SpecComparer, view.SpecItems, other.Items)` through those projections;
it no longer needs to expand an ordinary model for the view.

The generated view factory now calls a rechecked specialized constructor with
the underlying collection **and the view's mutable state-cell reference**.
The specialized iterator record retains that reference, not a base-class pointer.
Loop invariants preserve both ownership links and the view's readonly fields.
This is a generic borrowed-owner mechanism, not a SortedSet compiler intrinsic.
`test/borrowed_owner` checks it with a different collection, a cache-writing
virtual getter, a loop, and a client returning the view's value 7 rather than
the source's value 33. Reassigning the retained view, copying the held iterator,
and claiming the base-dispatch result are rejected.

### Checked shared iterator proof

The **active ordinary and view** constructor overloads, Initialize, MoveNext,
Current, Dispose, and factories have freshly checked artifacts under
`obj/public-dispatch/view-iterator/_cache`.
They use the same source-based loop proof; no executable iterator branch
was changed. The specifications use source observation/snapshot/version
projections, filtered logical pending contents, and underlying-tree capacity.
At an ordinary set the range constraints reduce to the previous predicates, including the
original stale-version MoveNext domain.
MoveNext additionally ensures `SpecFresh` on normal return. A `[Throws]`
allowance alone did not require the stale-version guard: its removal initially
verified. With this checked normal-return postcondition,
`python3 iterator_negative.py` rejects removing the actual guard at the
MoveNext implementation, with no positive target cache available to the mutant.

`public_dispatch_checks.py view-iterator` copies the active source unchanged.
The former proof-annotation rewriting function has been removed. It checks
the actual factory/constructor/Initialize/MoveNext/Current/Dispose chains.
Fresh checks prove:

* `Func_SortedSet_Enumerator_Current_owner_TreeSubSet`;
* `Func_SortedSet_Enumerator_Dispose_owner_TreeSubSet`;
* the actual view Initialize and MoveNext implementations;
* both view iterator constructor overloads, including reverse enumeration;
* the actual inherited view GetEnumerator factory;
* the actual client constructing the set and view, obtaining an iterator,
  calling MoveNext, conditionally reading Current, then calling Dispose;
* actual view TotalCount and VersionCheck(false) dependencies;
* `StateActive.active_node` and `StateOwnerRead.node_facts`, connecting any
  null/active source node to its observed subtree, not just the full-tree root.

The IsWithinRange handoff succeeds: the compiler emits a checked assertion of the known
readonly source model **after** evaluating the node argument. This also works
in loops over non-region owners; dirty receivers, mutating calls and mutating
arguments are not pinned. Generic straight-line/loop positives and wrong/stale
result negatives live in `test/borrowed_owner`.

The checked `StateOwnerRead.auto_read` opens a new child read window after that
call restores the owner. It requires membership and retains the exact source
model and permission through a restoration trade.

The range proof distinguishes two directional invariants. Initialize permits
an in-range root whose physical subtree extends beyond the view's bounds.
MoveNext starts in the far subtree of an in-range popped root and preserves a
bound on that **whole successor subtree**, including after an in-range push.
Filtered pop/push and both-direction pruning preserve the logical pending
sequence; the alternate executable branches remain present and are proved
unreachable when appropriate. Both invariants reduce to True for an unbounded
set, without requiring sortedness of arbitrary retired observation nodes.
An empty-pending lemma establishes the initial filtered sequence, and checked
filter/reversal correspondence connects both constructors to their contracts.

The factory preserves untouched inherited ghost state and exposes the
raw-pending capacity bound needed by MoveNext. The full view iterator client
dependency closure now checks: ownership-bearing branch joins retain the
view-to-source link across the optional Current read, allowing Dispose.
Eligible readonly ordinary owners remain closed between checked
unfold/read/fold brackets, including around source-based ghost operations.
Mutation and raw-owner proof protocols retain their existing handling.
No explicit Restore lemma or iterator-owner identity projection is needed.

The legacy view InOrderTreeWalk and its actual Count dependency also check.
Around the comparer call, erased NodeFacts/Open/Close operations use a
full-source read window, then explicitly return to the legacy cursor protocol
before following a child. This preserves the unchanged C# argument evaluation
order. An overlapping automatic active-tree read rule was removed: its
membership refinement interfered with observation-based iterator reads, and
its restoration trade hid resources needed by legacy CloseRead.

The runtime check independently exercises the cached-count distinction.
`make runtime` constructs 0..9, obtains the 2..5 view without reading Count, and
checks that enumeration yields 2,3,4,5 while its private cached count remains
zero before and after. It then checks both List and same-comparer SortedSet
public SetEquals calls return false. These are **CLR checks**, not F* proofs.
The shared proof uses the underlying-tree capacity rather than a view's cached
count as its stack bound. Forcing the
view's Count first would hide the original execution rather than establish its
correctness.

The separately fixed generic SpecOp coercion needed by `RangeMisses` is covered
by `python3 test/user_spec_type/generic_checks.py` from the repository root.
Polymorphic Int32/Int64 elements retain machine types while the explicit
SpecInt index remains mathematical. The wrong-element variant fails its lemma
precondition, not argument typing.
