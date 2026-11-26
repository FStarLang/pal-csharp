# Default-equality evidence

`make -j12 check` verifies the constructive comparer representation, generated
nominal evidence, and rejection controls. `make cs` checks ordinary C# compilation.

The public `Equality` and `Bcl.default_equals` bindings now use the same
`has_equality` dictionary. Generic methods and specifications receive evidence;
generic owned storage retains it as an inductive type parameter. Plain reference
storage does not imply identity equality by itself.

Checked controls:

* Identity is inferred only for eligible sealed plain classes directly inheriting
  `object`, without an `Equals` override or any `IEquatable<U>` implementation.
* Same-reference, distinct-reference, null, custom-comparer, generic, and cast
  controls use the instances emitted from the C# declarations.
* Override and explicit `IEquatable` identity claims fail proof verification.
* Roslyn controls cover inheritance, unsealed classes, nested generic types,
  hidden methods, and hash-only overrides.
* The compiler's actual `EvidenceStorage<T>` raw type cannot be reinterpreted at
  another equality dictionary.
* Nested generic storage, evidence-free sequence wrappers, and nullary generic
  specifications preserve the dictionary ABI.
* Two calls to the randomized comparer factory cannot be proved to return the
  same object.

## Actual HashSet acceptance test

`samples/dotnet-runtime/pal/HashSet/ReferenceKeys.cs` uses the actual annotated
CoreLib `HashSet<T>`, not an opaque collection primitive. Its checked `Duplicate`
client proves that adding the same reference twice returns false the second time.
`Distinct` proves successful insertion for two distinct references.

After translating the sample and verifying `HashCommon`, the focused targets are:

```
make -C samples/dotnet-runtime/pal/HashSet -j12 PHASE=verify REFERENCES_BUILT=1 \
  _cache/Func_ReferenceKeys_Duplicate.fst.checked \
  _cache/Func_ReferenceKeys_Distinct.fst.checked
```

This acceptance test does not claim that SortedSet's nullable-owned-local fallback
has been verified.

## Representation and trust

`EqualityModel` separates opaque comparer objects from certified reference-default
objects. These are canonical object categories, not tags added or removed by
casts: every comparer cast preserves the complete handle. Custom comparers keep
their opaque equality/hash behavior. The reference interpretation is constructed
from the existing `RefEq.ref_eq` primitive; its hash law follows by substitution.
No nominal equality axiom or algorithmic assumption is added.

The old trusted equality/string interfaces live in the `*Opaque` modules.
Checked wrappers preserve their string transformations and identity tokens.
General `box:` / `box?:` bindings convert comparer values through their underlying
object tokens instead of boxing the model's sum representation.

The runtime randomized factory has an effectful relational interface. Its checked
implementation uses the old mathematical witness, but the interface hides that
witness's deterministic identity. Equality preservation is proved after the
factory returns, without identifying repeated calls or their hash functions.
