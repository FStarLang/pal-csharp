# Sealed enumerable casts: compiler integration

```
make -C test/enumerable_cast verify
make -C test/enumerable_cast fresh negative
make -C test/enumerable_cast runtime
```

`IsPacket(IEnumerable<int>)` is a real translated C# method, not a handwritten
Pulse approximation. Its contract identifies its Boolean result with the CLR
class test. The successful branch calls the concrete `Packet.Count`; the failed
branch reads the interface enumerator. `Successful` proves Boolean `true`;
`Failed` proves Boolean `false`. Both also prove the original source contents
are restored. The stock CLR harness runs with `PAL` undefined and checks both.

## Checked bridge

The compiler discovers one sealed class target per enumerable parameter. At a
concrete call site it establishes nominal equality or disjointness from Roslyn
class declarations, **not** generated names, representation equality, or a
closed-world list of implementations. A miss retains the actual source and its
invariant through an abstract ownership predicate.

The adapter invokes verified nonmutating `Count` and `CopyTo` operations, and the
translated iterator that nominally implements `IEnumerable<T>.GetEnumerator`.
It proves both the snapshot and the actual yielded sequence equal the source
model before lending any ownership. These are auxiliary nonmutating observations
of the source, not assumptions about an arbitrary method named `GetEnumerator`.

`Enumerable.Cast` builds on `Enumerable.Source` and now retains the complete
erased class model in a matching descriptor. Opening a matching descriptor
consumes the combined source resource, exposes concrete ownership and retains
the snapshot token. Closing requires the same object and model. The caller then
gets both its source invariant and the snapshot back. This test uses the identity
projection from its sequence model. The generic structured/refined-model extension
and declared `[EnumerationModel]` projection are tested in `test/enumerable_projected`.

`fresh` rechecks the complete generated dependency chain at rlimit 10, with
`--force --z3refresh`, in `obj/fresh`. `negative` uses independently translated
copies in `obj/bad-enumeration` and `obj/bad-copy`. Each deliberately wrong
implementation verifies against its honest weaker contract; the adapter clients
must fail their separate correspondence obligations. No active sources or caches
are changed by these experiments.

## Deliberate limits

The adapter accepts top-level, directly object-derived sealed classes, including
generic classes and structured/refined models with a declared projection. Call sites must supply named,
nonnullable concrete sources with full ownership. Forwarding interface loans,
named arguments, multiple class targets for one parameter, exceptional branch exits,
using the source while its concrete loan is open, and mixed collection-capability
casts are rejected. Normal early returns and scoped `as`/null-check forms are now
supported. More generally, proof obligations reject ownership aliasing
or model mutation incompatible with restoring the original source/snapshot.
Arbitrary unknown interface implementations are **not** classified as misses.

This is **not** general-enumerable SortedSet comparison verification.
SortedSet's public `[Exactly]` restrictions remain unchanged. A TreeSubSet is
assignable to SortedSet but cannot be opened as an ordinary base invariant.
The next extension must install a nominally justified abstract base capability
with the actual implementation's ownership, logical model and virtual slots
(the parent-owned `InterfaceViewFacts` study demonstrates that mechanism).
It must preserve that capability through enumeration and same/different-comparer
dispatch before the public List/view reproducer can be proved.
