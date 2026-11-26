# Frontend-installed nominal observation descriptors

```sh
make -C ../../pulse _cache/Pulse.Lib.CSharp.Enumerable.Capability.fst.checked \
  _cache/Pulse.Lib.CSharp.Enumerable.Observation.fst.checked
make cs verify bridge classifier runtime
python3 checks.py
python3 inherited_checks.py
python3 helper_checks.py
python3 miss_checks.py
make list-miss
```

`Observations.cs` now exercises **actual frontend installation**, not only the
handwritten bridge. `Observe` uses `as`/null-check, and `ObservePattern` uses a
declaration pattern. Both call the installed Count/comparer slots and prove the
results equal the selected specification observations. Ordinary and view clients
lend their actual C# sources twice, then continue using their restored ownership.
The view's Count is zero, its source's Count is one, and their comparers differ.
The CLR runtime test executes these same clients with proof assertions erased.

The compiler generates `Nominal_*` modules from nominal slot resolution and
`EnumerationObservation` metadata. Each module proves wrappers around the actual
translated getters. Ordinary ownership retains the complete source model. View
ownership retains the source invariant and an exclusive reference to an
existential **current** view record: the cache can change. It does not substitute
the source invariant for the view. Both logical observations must be preserved
by each installed slot, as checked by F*.

At installation, checked Count/CopyTo construct an owned array snapshot and the
actual interface implementation supplies checked enumeration evidence. Both
sequences must equal the installed logical projection. The descriptor and
snapshot are lent together and restored after the call. Successful casts use
the source's descriptor identity; reads invoke the installed actual getter
while retaining the snapshot. Consumers quantify over a generic model/API and
receive checked observation selectors, avoiding normalization of concrete
dependent slot records in their bodies.
Snapshot instrumentation saves and restores the view record before installation,
so a cache-writing Count used to size the snapshot does not add a view mutation;
the consumer's actual installed Count performs that mutation.

## Bounded supported forms

* A nonabstract, nonsealed, top-level target directly derived from `object`,
  with an ordinary model and one `[Spec, EnumerationModel]` sequence.
* Exactly two annotated observations: an `int` sequence length and a scalar
  `bool` or comparer. Names are not privileged: the test also renames the class,
  sequence, scalar and both getters and verifies the resulting installation.
* An exact ordinary target source (fresh named allocation without reassignment
  or ref escape, or an existing checked exactness witness), or a known sealed
  borrowing view with one ordinary retained owner and no extra owned resources.
* Actual, checked class slots and Count/CopyTo plus the actual interface yield
  implementation or an eligible checked `EnumerationProtocol`. Resource-producing
  protocols require `EnumerationState` and checked concrete iterator operations.
* Getter preconditions must follow from the retained predicate. Authored
  preconditions and exceptional domains are not replaced or assumed. A partial
  getter whose domain cannot be established makes its generated wrapper fail.

Unknown subclasses, uncertain runtime assignments, unsupported interface
reimplementations, missing enumeration evidence and concrete-helper escapes
are rejected. A missing implementation is **not** installed as a failed cast.
The nonsealed installer also handles exact, ordinary disjoint sources. A miss
still retains actual source ownership and requires checked snapshot/enumeration
correspondence; it installs no target getters. Disjoint borrowed-view sources
remain unsupported. The existing sealed hit/miss adapter is unchanged.

Private nonvirtual self helpers can take retained nominal arguments: the compiler
generates a new signature and re-verifies the original body and contracts against
the capability. It requires a successful cast, retains ordinary versus borrowed
receiver dispatch, and does not manufacture a concrete argument invariant. All
concrete parameters currently must be capabilities; pointer escapes, fields and
uninstalled observations remain rejected.

Snapshot-only forwarding temporarily exchanges the capability for the existing
snapshot plus an opaque source receipt. After the callee returns the same snapshot,
the receipt restores the same capability. Casts and slot calls cannot use the
receipt concurrently. This also applies to inherited borrowed-receiver calls.

Not yet supported: arbitrary schemas, collection-interface capabilities, forwarding
to another nominal consumer, arbitrary concrete helpers, source mutation during
lending, or arbitrary exceptional iterator resource transitions. A concrete
adapter must prove its original operation domains and all reclamation obligations.

## Checks

`Helpers.cs` calls `CompareObserved` with both ordinary and view-backed sources.
The consumer exercises a short-circuit private helper, snapshot fallback and a
repeated cast after restoration. `Empty.CompareHere` verifies the helper and
forwarding calls with an actual borrowed receiver and abstract capability input.
`helper_checks.py` rejects incorrect ordinary/view helper bodies, unestablished
original preconditions, unsupported virtual dispatch, pointer/field escapes,
missing successful-cast evidence, missing restoration and duplicate forwarding.

**Resolved prerequisite:** `ClosedViewCall.cs` is now in the positive Makefile
sources and verifies with the repaired pinned toolchain. Its unchanged concrete
view-receiver/capability-argument call formerly failed with
`Expected type Type got type r: ... perm`. Verify with:

```sh
make translate verify SOURCES='Observations.cs ClosedViewCall.cs' \
  OUT=obj/closed-view/out CACHE_DIR=obj/closed-view/_cache \
  EXTRA_INCLUDES=../../pulse/_cache
```

The initial failure alone did not establish a verifier issue. Attempts to reorder
capability type binders or eliminate the already-equal post-state existential did
not produce a robust passing caller and were reverted.
`ClosedViewCore.fst` isolates a passing call with an existing reference.
Adding a locally allocated reference, using either stack allocation or explicit
Box allocation/conversion/free, exceeded a 120-second diagnostic budget in
F* elaboration (with negligible solver CPU). The allocation experiments were
removed; they do not justify changing the compiler's allocation representation.

The subsequent [narrow call diagnostic](CALL_DIAGNOSTIC.md) corrects the
allocation hypothesis: the actual inherited consumer also fails with an existing
reference. A class-free reproducer and verified abstract-API control isolate an
internal binder-index collision in the pinned verifier's universe inference.
All-explicit type, permission, descriptor, and ghost-state arguments did not fix
the unpatched verifier. The global-ID freshness repair does. The diagnostic
scripts default to positive expectations and accept an explicit unpatched
executable for historical collision checks.

`Misses.cs` verifies nonsealed disjoint sources with both ordinary and borrowed
receivers. `SequenceProtocol.cs` uses a real borrowing iterator and the optional
sequence form of `EnumerationState` (empty or singleton current), without a
logical `default(T)`. Existing scalar-current protocols remain supported.
`miss_checks.py` rejects unknown runtime types, missing evidence, incorrect
Count/enumeration/current laws, lost restoration, and duplicate packing.

`ListMiss.cs` constructs the actual translated runtime `List<int>`, adds
`2,3,4,9`, proves a nominal miss, and proves all four elements remain after
restoration. Its gate checks the List dependency and generated client.
This required precise `Array.Copy` source-read analysis: destination writes,
overlap and local destination aliases remain mutating. Classifier checks cover
these distinctions, and the actual List CopyTo implementations verify.

## Resource-producing iterators and public SetEquals

```sh
make verify OUT=obj/iterator/out CACHE_DIR=obj/iterator/_cache \
  EXTRA_INCLUDES=../../pulse/_cache
python3 iterator_checks.py
python3 iterator_installation_check.py
python3 guard_dependency_check.py
```

The 85-module iterator gate includes successful casts, real factory/MoveNext/
Current/Dispose calls, checked source-only protocol facts, and source restoration.
`Partial` exits after one MoveNext without Dispose: its generated scope release
reclaims cursor storage, restores ownership, and does not insert Dispose.
Concrete cursor adapters retain auxiliary owners and must reclaim them; nominal
snapshot arrays are freed rather than discarded.

`NominalFacts_*` exports only protocol postconditions expressible through the
configured logical observations. Installation must prove these facts from checked
source evidence; successful dispatch exposes them through a checked reader.
Negative tests reject incorrect Next/Current laws, false facts, an unestablished
factory domain, changing Dispose state, premature Current, duplicated cursors,
and incomplete cursor reclamation.

`iterator_installation_check.py` directly translates the active SortedSet source,
without importing the generalization probe or rewriting its annotations. It
requires the promoted public SetEquals signature. It emits ordinary and TreeSubSet successful-cast
adapters and public callers in `SortedSet/obj/iterator-hit/out`. The proof targets
are `Func_SortedSetIteratorInstallation_Ordinary`,
`Func_SortedSetIteratorInstallation_View`, and the persistent List repro
`Func_SortedSetIteratorInstallation_ListFalse`. The view fixture has separate source
and receiver owners and explicitly excludes source version `-1`, as required by
the existing fresh-view coherence contract. It makes no self-aliasing or
overlapping-owner claim. The caller dependency closures verify.

`guard_dependency_check.py` first verifies the generalized public SetEquals
implementation, its view counting helper, and the actual List false-result
client. It then removes only the range guard in an isolated copy and checks the
whole affected closure, requiring the view helper implementation to fail.
Checking a caller alone against an unproved imported contract is deliberately
distinguished from verifying that closure.

The older `guard_dependency_check.py` still imports the parent-owned
`public_dispatch_checks.py` and calls `run("general-public", verify=False)`;
its `generalize(source)` must accept an already-promoted SetEquals unchanged.
The persistent iterator gate has no such dependency. These checks do not claim
generalization of the other three public comparison methods. The existing
admitted HashSet fallback is unchanged.

`Inherited.cs` covers inherited getters whose synthesized observation laws must
bind virtual Spec properties at the actual view, just like authored `At`
contracts. It also passes an exact concrete enumerable argument through an
inherited borrowed-receiver call: ordinary Count/CopyTo snapshot adaptation and
lending/return are applied there too. Generic snapshot allocation propagates its
default-value obligation. `inherited_checks.py` rejects incorrect inherited
Count/order observations and removal of the generated unlend.

`checks.py` has source-level negatives for wrong observations, wrong snapshots
and enumerations, the original getter domain, unknown ordinary/generic
subclasses, interface reimplementation, reassignment, missing copy evidence,
forwarding and iterator escape. `classifier/` separately checks assignability,
override versus hidden members, interface maps and generic uncertainty.

`ObservationBridge.fst` remains an independent mechanism test using real
generated getters. It verifies hit/repeated/miss flows and rejects wrong view
dispatch, duplicated view ownership and a wrong array snapshot. The support
interfaces expose checked contracts; their implementations add no axioms,
assumptions or admits.
