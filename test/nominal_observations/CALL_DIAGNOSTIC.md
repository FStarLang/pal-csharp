# Inherited-consumer call: repaired core freshness regression

The repository toolchain now includes the checked global-ID freshness repair
in `tools/fstar-core-freshness.patch`. All controls below pass with the default
toolchain, including the unchanged generated caller. The failure analysis below
records the **unpatched** compiler's behavior; it is not a current limitation.
`ClosedViewCall.cs` is also part of the normal positive translation/proof gate.

Pinned F*: `2026.10.25~dev`,
`b6b10e72d9cd42a56e5b09c25208de61119bf484`.
No allocation or production-contract workaround was used. All proof limits
remain at most 10.

## Exact emitted call

After translating `Observations.cs ClosedViewCall.cs` into
`obj/closed-view/out`, `Func_ClosedViewCall_Run.fst:73` contains:

```fstar
let t4 = func_Empty_at_Packet_CompareObserved
  ty_T var_receiver var_view
  #(O.model ty_T (Order.comparer ty_T))
  #(O.slots ty_T (Order.comparer ty_T))
  O.contents O.scalar O.select_length O.select_scalar
  (Source.view t12 var___pal_nominal_snapshot0 false);
```

Here `O`, `Order`, and `Source` abbreviate the fully qualified names in the
generated file. The diagnostic is attached to the enclosing continuation
at `(72,65-86,5)`, not to a C# conversion. The local allocation is at line 48.

Both model/API type arguments are **already explicit**. Pulse's
`--debug refl_tc_callbacks --print_implicits --print_full_names
--print_bound_var_types` trace elaborates the remaining arguments, in declaration
order, to:

| Formal | Actual |
| --- | --- |
| `#pre_this` | receiver's retained erased model (`_post_this13`) |
| `#perm_this` | `1.0R` |
| `#pre_self` | `hide t1`, the original view record |
| `#pre_input` | `vnominal_model_3 : erased (O.model ty_T (Order.comparer ty_T))` |
| `#p_input` | `1.0R` |
| `#descriptor_input` | `hide t11 : erased (C.descriptor (O.model ...) (O.slots ...))` |

`closed_view_diagnostic.py explicit` supplies every one of these binders and
also supplies both type arguments to each observation projection/selector.
It fails with the same `Expected type Type got type ... perm` diagnostic.
There is no observed argument-position or implicit-model inference mistake.
The script writes separate diagnostic modules under `obj/call-diagnostic`;
it does not modify the generated caller.

## Correction to the allocation hypothesis

`ClosedViewCore.fst` verifies, but its consumer has a **reduced** postcondition.
It was not an identical-contract control for the real inherited consumer.

`ClosedViewCall.Parameterized.fst` now calls the **actual generated consumer**
with an existing `R.ref`, all implicit arguments explicit, and its original
contract unchanged. It fails too. `ClosedViewCall.Local.fst` makes the same
call after `let mut`; it fails with the same type mismatch. Thus allocation
is neither necessary nor an established cause of this typing error.

## Class-free reproducer and passing control

These files do not import generated C# modules, collection classes, comparers,
or nominal adapters. They use the existing generic capability/observation
support, ordinary `R.ref`, and a five-field record:

* `DependentCall.Capability.fst`: verified generic consumer **and successful
  parameterized-reference control** with abstract model/API and reader slots.
  The consumer preserves the complete owner and view resources, full record
  equality, all individual field equalities, the capability, and the Boolean
  `supports` result.
* `DependentCall.CapabilityConcrete.fst`: same consumer, existing reference,
  concrete `O.model t r` / `O.slots t r`; all arguments explicit. Fails.
* `DependentCall.CapabilityLocal.fst`: same concrete instantiation with a local
  reference. Fails.

Both failures are:

```
Ill-typed term
Expected type Type
got type Pulse.Lib.CSharp.Enumerable.Observation.model t r
```

The retained files now serve as positive repair regressions and explicit
unpatched-compiler diagnostics. No contract was removed to make a caller pass.

## Internal binder collision

The class-free failing case, with `--debug High --print_implicits
--print_full_names --print_bound_var_types`, prints this universe-inference
input immediately before the error (indices are from that run):

```text
Calling universe_of_aux with
    uu___4477: i4479 ->
    uu___4478: PulseCore.FractionalPermission.perm ->
    uu___4479: O.model t3346 r3347
  -> Prims.Tot Pulse.Lib.Core.slprop
```

The API implementation-type variable `i4479 : Type0` and the newly opened
**model-value** binder `uu___4479 : O.model ...` have the same binder index.
Looking up the former in the extended environment finds the latter's type.
The error's “actual type” is this model-value type, **not** a misinferred
source-level `#enum_model` argument.

The original generated case shows the analogous permission collision:

```text
    uu___6572: i6573 ->
    uu___6573: PulseCore.FractionalPermission.perm ->
    uu___6574: O.model ...
  -> Prims.Tot Pulse.Lib.Core.slprop
```

Its reported actual type is the unfolded permission refinement
`r6579 : FStar.Real.real { r6579 >. 0.0R }`.

Relevant pinned source:

* `src/typechecker/FStarC.TypeChecker.Core.fst:140–145`:
  `fresh_binder` uses the core environment's `max_binder_index + 1`.
* The same file, `1931–1937`: `universe_of_well_typed_term` calls the ordinary
  `TcTerm.universe_of` helper, with a fallback to core checking.
* `src/typechecker/FStarC.TypeChecker.TcTerm.fst:5390–5396`:
  arrow universe inference opens binders through `arrow_formals_comp_strict`,
  pushes **all** those binders, then computes their domain universes.
* `src/syntax/FStarC.Syntax.Syntax.fst:607–620`: ordinary freshening uses
  the separate global `GS.next_id()` generator.

This locates the failure at the interaction between core-local and global
binder freshening during universe inference. It is reproducible without the
C# compiler and is not an ownership/precondition failure. The repair reserves
global IDs above the core environment's maximum before allocating through
`GenSym.next_id()`. The isolated full compiler/Pulse build and fresh project
verification passed; the parent integrated that repair into the pinned installer.

## Reproduction

From the repository root, with the generic support already checked:

```sh
python3 test/nominal_observations/call_diagnostic_checks.py
```

This now requires all three controls to verify. To reproduce the two precise
historical errors, explicitly select an unpatched executable:

```sh
python3 test/nominal_observations/call_diagnostic_checks.py \
  --fstar /path/to/unpatched/fstar.exe --expect-collision
```

Timeouts and unrelated failures are rejected, not counted as evidence.
To inspect universe inference (use the unpatched executable for the collision):

```sh
tools/run-fstar.sh --include pulse/_cache \
  --include test/nominal_observations \
  --include test/nominal_observations/obj/call-diagnostic/_cache \
  --debug High --print_implicits --print_full_names --print_bound_var_types \
  test/nominal_observations/DependentCall.CapabilityConcrete.fst
```

For the original generated chain:

```sh
make -C test/nominal_observations translate \
  SOURCES='Observations.cs ClosedViewCall.cs' \
  OUT=obj/closed-view/out CACHE_DIR=obj/closed-view/_cache
# Verify the generated dependencies as in README.md; the final caller now passes.
python3 test/nominal_observations/call_diagnostic_checks.py --generated
python3 test/nominal_observations/closed_view_diagnostic.py baseline
python3 test/nominal_observations/closed_view_diagnostic.py explicit
```

The last two commands now pass. Both accept `--fstar` to select the archived
unpatched executable. `--trace` prints elaboration callbacks. `--padding 1`
tests an inert local binder; it was not a fix and is not an emission workaround.
