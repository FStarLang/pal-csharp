# Ordinary borrowing-enumerator adapters

This fixture verifies actual C# source-backed casts, not a handwritten Pulse
substitute. `Store<T>` has a structured model whose revision is omitted by its
enumeration projection. Its ordinary borrowing struct implements `IEnumerator<T>`;
the explicit `IEnumerable<T>` factory boxes that struct.

## Checked protocol

`[EnumerationState(ready, remaining, value, valid)]` names four `[Spec]` properties
on a borrowing struct. The compiler resolves the **nominal interface slots** and
adds obligations to their actual translated implementations:

* MoveNext preserves `ready`, succeeds exactly when the old remaining sequence
  is nonempty, removes exactly its first element on success, and establishes a
  valid current value equal to that element. Empty remaining state stays empty.
* Current requires `ready && valid`, returns `value`, and preserves logical
  protocol state, including state stored in owned iterator objects.
* Dispose requires only `ready` and preserves that logical state. Thus its law
  covers partial enumeration, repeated disposal, and subsequent observations.

These laws extend the domain to `originalPre || protocolPre`, retaining authored
attribute/body postconditions under `Old(originalPre)` and protocol laws under
`Old(protocolPre)`. Exceptions remain checked outside the ready protocol domain.
An end-only precondition cannot hide partial disposal, and readiness cannot hide
the original stale-version exception behavior. Authored postconditions
are still checked. The laws are not new axioms or trusted method annotations.
The adapter requires one `IEnumerator<T>` instantiation, and checked ordinary
method bodies rather than `[Admit]`, `[Implements]`, or `[PulseBody]` replacements.

`[EnumerationProtocol]` marks a complete proof traversal. Its checked shape is:
the nominal factory on `this`; a loop on that iterator's nominal MoveNext;
exactly one yield of its nominal Current per iteration; then nominal Dispose.
The loop may contain invariants, a decreases clause, assertions, and lemma calls.
Its proved yielded sequence and the separately checked Count/CopyTo snapshot
must both equal `[EnumerationModel]`. A conveniently named, different factory or
Current does not suffice.

Boxing is specialized only for a fresh, nonescaping local obtained from
`((IEnumerable<T>)source).GetEnumerator()`. Interface calls resolve to the actual
struct implementations, with one mutable state cell and the original source
resource. Aliasing, identity observations, reassignment, and escaping the box are
not supported. No unboxing-injectivity axiom is used.

Named nonnullable owned collection locals now work in static clients as well as
instance methods. `StaticBox` and `StaticStruct` construct their own collection,
enumerate it, and prove its original complete model remains available.

## Real factory shapes

The resolver accepts the direct boxing delegation used by SortedSet. It also
accepts a conditional forwarding branch guarded by a checked read-only integer
property compared with a constant. The adapter proves that branch is selected;
it **does not assume the other branch is empty**. `checks.py positive` generates
and freshly verifies this second shape, corresponding to List's
`Count == 0 ? Empty : GetEnumerator()` nonempty branch.

The empty branch needs its own adapter before arbitrary possibly-empty List
sources can be supported. Nonsealed source dispatch and compiler integration of
TreeSubSet's abstract base capability remain separate work. The actual List
protocol is separately annotated and checked; this fixture does not establish
SortedSet's iterator correspondence. Public SortedSet `[Exactly]` restrictions
are unchanged.

## Loan forwarding

`ForwardClient` passes an existing source-owning loan through differently named
parameters with the same cast target. `SnapshotOnly` temporarily receives the
existing snapshot, without taking a second snapshot or duplicating source
ownership. `GuardFalse` checks the normal cleanup edge after a successful cast
whose additional condition is false. The source's complete model is available
again on return. Changing the target, inventing source metadata from a plain
snapshot, and forwarding while the concrete cast loan is open are rejected.
Internal loops, including deferred early returns, restore the loan after the
loop. A cast nested in an enclosing loop and exceptional exits remain excluded.

## Tests

* `make verify`: all translated modules.
* `make fresh`: isolated, complete direct and guarded chains (36 modules each),
  `--force --z3refresh`, rlimit 10.
* `make negative`: weakened wrong Current/MoveNext contracts, restart after end,
  source-mutating Dispose, partial-state-changing Dispose, restrictive attribute
  and body preconditions, bad ranking, Current after exhaustion, wrong factory
  branch, missing Dispose, wrong yielded slot, boxed aliasing, and generated
  specification-key collisions, swallowed stale-version exceptions, and
  invalid loan forwarding.
* `make runtime`: real CLR clients covering both cast results, zero/one-step
  disposal, polymorphism, static locally-owned sources, forwarding, and the
  stale-version exception outside the ready protocol domain.

The source/snapshot cursor now becomes `-1` when exhausted. Previously it stayed
at the sequence length, inadvertently permitting Current after a false MoveNext.
The new terminal client verifies repeated false returns, and its isolated
Current-after-end variant fails verification.

The support interface and implementation are checked separately. For a fresh
implementation check, remove/move its target `.checked` file while retaining the
separately verified interface, then run with `--z3refresh --query_stats`.
The cache-absent run discharges the actual implementation queries. The new
interface-free generated modules use `--force`.
