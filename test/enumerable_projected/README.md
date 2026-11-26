# Generic projected enumerable loans

```
make -C test/enumerable_projected verify
make -C test/enumerable_projected fresh negative facts
make -C test/enumerable_projected runtime
```

`Parcel<T,TTag>` has a structured, refined model containing its element sequence,
a separate tag sequence, and a revision. Only this declared pure projection
describes enumeration:

```csharp
[Spec, EnumerationModel] public Seq<T> Elements => Model.Values;
```

The annotation asserts nothing about runtime methods. Before lending a source,
the compiler checks its actual interface iterator and Count/CopyTo snapshot
against this projection. Count and CopyTo must preserve the source; iterator
verification also checks nonmutation. Changing the annotation to a different,
incorrect projection fails the adapter's correspondence proof.

The descriptor retains the **complete erased model**, not merely the projected
elements or an arbitrary model with the same elements. A successful cast opens
that model's concrete invariant. Closing requires exactly that model. Failed
casts capture the actual source invariant, its complete model and identity in the
abstract misses predicate. Both callers prove preservation of tags and revision,
which enumeration omits.

## C# shapes tested

* Generic target `Parcel<T,int>` in a generic method.
* `var candidate = other as Parcel<T,int>; if (candidate != null) ...`.
* Reversed operands, `null != candidate`.
* Declaration-pattern casts, with early returns.
* Nested early returns and mixed early-return/fallthrough paths.
* Success from `Parcel<int,int>` and failure from `Parcel<int,bool>`.
* A fully polymorphic `Generic<T>` client that allocates and lends `Parcel<T,int>`.
* Repeated calls on the same source with its complete model restored each time.

The emitted cleanup evaluates a returned expression while its concrete ownership
is available, closes the loan, then returns the saved result. Cleanup belongs to
the control-flow edge: closing one branch cannot remove another branch's loan.

Sealed classes with different definitions are disjoint. Distinct instantiations
of one definition are classified as misses only when their type arguments are
provably distinct. `Parcel<int,U>` cannot be classified as a miss of
`Parcel<int,int>` when `U` is unknown: this requires additional runtime evidence,
and PALCS0866 rejects it rather than assuming failure.

## Evidence

`fresh` rechecks the entire generated chain at rlimit 10 with
`--force --z3refresh`. `negative` independently translates copies under `obj/`:

* bad copy, bad iterator, and wrong declared projection: their implementations
  and abstract cast methods verify, but all three adapter clients fail at
  the exact generated correspondence obligations;
* a mutating concrete call inside the fractional loan is rejected;
* a mutating Count is rejected by the compiler, not treated as a pure observation.

`ProjectedFacts.fst` independently checks a **full-permission** write that changes
only unprojected model data. The attempted close then fails despite unchanged
enumeration. The negative runner removes `expect_failure` in an isolated copy
and checks that the actual error is at `close_match`, not an earlier operation.

`runtime` executes the genuine C# clients with PAL undefined, exercising both
values of the early-return condition and both CLR cast outcomes.

## Remaining boundary

Targets and concrete sources remain top-level sealed classes directly deriving
from object. Interface forwarding, unresolved runtime generic identity, mixed
ICollection capability casts, null-first guards without an explicit else, loops
and exceptional exits inside the concrete loan still require further support.
The simple sequence-model bridge remains supported using the identity projection.

Currently the enumeration evidence comes from a translated C# `yield` iterator
that is the actual nominal interface implementation. Ordinary borrowing-struct
enumerator factories (including SortedSet), their boxing, and MoveNext/Current/
Dispose protocols are **not silently accepted**. That extension needs nominal
interface slot bindings, iterator state/ownership and source-loan transfer,
verified cursor transitions/termination, Current's projected-element relation,
and disposal restoring the same source model. TreeSubSet additionally needs
the abstract base-view capability and its actual virtual dispatch.
