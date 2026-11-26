# Source-retaining enumerable loans

`make -C pulse && make -C test/enumerable_source` verifies the support module and
its clients. The client gate forces fresh checking, including the expected
failures, at rlimit 10.

`Pulse.Lib.CSharp.Enumerable.Source` packages a source descriptor **and ownership
of that source** with a snapshot. Forming the loan requires an already-proved
equality between the snapshot and the source model's contents. Opening the source
transfers ownership; closing requires the same source model. Enumeration and
`Count`/`CopyTo` preserve the combined resource.

The tests cover:

* establishing the correspondence by verified array length/copy operations;
* retaining descriptor identity across source access and enumeration;
* allocating/freeing a source box, while returning the caller's snapshot buffer;
* rejection of incorrect snapshot contents, duplicated source ownership,
  repeated opening, and closing a changed source against its stale snapshot.

## Integration boundary

The scoped **sealed-class adapter is wired into the C# emitter**; see
`test/enumerable_cast`. Its real C# clients prove successful and failed casts,
checked copy/enumeration correspondence and restoration of source ownership.
`test/enumerable_projected` extends this to generic structured/refined models,
explicit pure enumeration projections, and scoped `as` casts with early returns.
Ordinary enumerable parameters still use `Pulse.Lib.CSharp.Enumerable`.
`EnumerableClass{As,Is,Pattern}` pin PALCS0865 for forms that cannot use the
adapter, and the `EnumerableCast*` diagnostic fixtures cover its stricter limits.

The remaining general adapter must supply a coherent CLR descriptor, source
ownership and model-to-contents map, and translate successful *assignability* casts to the
appropriate member dispatch. An exact class and its borrowing subclass cannot be
handled by recovering the same base-class representation: the borrowing case
needs its owner's resource, view state, filtered model, and view-specific calls.
The adapter also has to carry these distinctions into the public contract's
conditional comparer-compatibility requirement.

Consequently this is not a proof of general-enumerable `SortedSet.SetEquals`, nor
of its `List<int>` reproducer. The sample's public `[Exactly]` restrictions remain
unchanged. No cast outcome, contents correspondence, or ownership is assumed by
this support module.
