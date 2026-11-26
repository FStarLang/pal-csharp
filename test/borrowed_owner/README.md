# Known borrowed-view iterator owners

`Owner<T>.Window` is a borrowing view, not an ordinary base object. Its iterator
retains the view's state-cell reference alongside the underlying collection
ownership. Members are rechecked at this representation. A virtual getter writes
the view cache and returns 7, while the underlying source remains 33.

The client checks constructor, factory, looped MoveNext, Current and Dispose:

```
make verify
make cs
python3 checks.py
```

The owner also has two inherited erased ghost fields. Chained iterator
constructors and looped calls preserve `audit`; the view's virtual getter
updates `touches` as well as its runtime cache. Constructor and factory frames
must therefore forward the former without promising the latter unchanged.
`wrong-ghost-frame` rejects that false promise. The erased loop snapshot reuses
the existing value rather than introducing a double `hide`.

`Identity => this` is inlined to the actual ordinary object reference, not its
model. The view overrides it with `Identity => source`; both ordinary and
specialized iterator methods pass that reference to a checked `Ghost<Owner<T>>`
lemma. `SameModelDistinct` has equal-model and distinct-reference preconditions;
the false identity-equality variant is rejected. This narrow support requires
a direct non-null reference in a proof expression. Composite receiver-dependent
observations still need a receiver-aware ABI and are rejected. A view's own
`this` cannot be reinterpreted as the ordinary underlying class pointer.

`Branch` checks conditional Current followed by Dispose, and `MutatingBranch`
allows MoveNext to change iterator/view state inside one arm. The checked
`Pulse.Lib.CSharp.RefJoin` wrapper retains common reference links across the
join: links must be required and unconditionally returned by all participating
ref-taking calls. Both arms must prove them; no mutable payload is pinned.
The compiler leaves executable branches and the single continuation intact.
Wrong branch results and removal of the ownership packing are negative tests.

`Compare` is inherited by the view and retains two iterators: one of the view
itself and one of an ordinary peer. It calls both MoveNext methods before and
inside a loop, then disposes both iterators. `DirectCompare` also tests an
explicit `this.GetEnumerator()` inside a member declared on the view.
The selected-value and distinct-peer clients prove both Boolean outcomes;
the source's value (33) must not replace the view's value (7).

Iterator locals in view members are registered with their individual owner
contexts. Calls on the view-owned iterator pass the underlying source plus
the actual view cell; peer iterator calls pass the peer instead. Transitive
iterator effects suppress invalid view-cache and ghost-state frames, while
untouched inherited ghost state is preserved by checked loop invariants.
Negative cases reject a wrong peer, source/view dispatch confusion, copying
a held iterator inside a view, a false mutation frame, and removal of the
inherited ghost loop frame. This does not remove existing ownership or
aliasing restrictions.
`ConditionOnly` checks that an iterator call in an `if` condition does not
trigger ownership packing when neither arm touches the iterator. Such packing
would forget its already-established value facts; only arm effects select
records for a join.

`ShortCircuit`, `AndCircuit`, and `GetterJoins` check readonly virtual getters
inside short-circuit expressions. A view member with no detected writes gets
a whole-state preservation postcondition, which its implementation must prove.
For ref-record calls with that unconditional guarantee, the caller captures
the current points-to witness and checks that the returned resource can be
reindexed to it. This preserves the view/source link across expression joins
without changing the reference ABI or executable branches. Negative cases
remove the reindexing, claim a wrong Boolean result, or mutate the getter;
mutation must not acquire an unchecked readonly guarantee.

`ReadonlyRetainedOwner` and `Iterator.ReadCurrent` check preservation of a
mutable flag in the extra owner-view cell across Current. Per-method transitive
effects now select that cell's untouched runtime fields as well as its ghost
fields; checked loop snapshots carry those frames through iterator methods.
A wholly untouched cell receives a checked whole-state postcondition.
MoveNext reaches a getter that toggles the flag, so it must not freeze that
field. Negatives make Current mutate the owner or falsely require MoveNext to
preserve the flag. The extra cell is never treated as the underlying class.

Negative cases reject view reassignment after its identity has been retained,
copying the held iterator, and a false result contract claiming base dispatch.
`ReadWindow` and `ReadWindowLoop` additionally exercise a checked return trade:
an argument reads the raw alias before the readonly call needs the original
invariant. The compiler supplies the known immutable snapshot after argument
evaluation, including inside non-region-owner loops. `Handoff.fst` proves the
alias conversion and ownership return; its mixed SpecOp/lemma C# container
must retain the checked lemma module. Wrong read results, stale mutation
results, and removal of the emitted handoff are rejected. `ChangeAndRead` and
`ChangeArgument` remain accepted without pinning their mutable state.

`ClosedOwnerReads` and `ClosedOwnerLoop` combine direct owner-field reads,
inferred ghost owner/model arguments, explicit identity arguments, and a
closed-invariant-to-read-window transition. For an eligible readonly owner,
the compiler keeps the invariant closed between reads and emits checked
assert/unfold/read/fold brackets. Subsequent ghost captures and loop frames
therefore use the closed invariant, not a stale expectation of raw ownership.
No `Restore` call or new annotation is needed. Removing a read's closing fold,
lying about its result, or inserting mutation before the inferred-owner call
is rejected.

This representation choice uses existing ghost class-parameter and spatial
precondition metadata; it does not identify arbitrary predicates as class
invariants. It excludes mutating, indexed, heap/region, inherited-base-model,
and owned-array/object-field receivers. Explicit raw ghost snippets, raw
receiver-field specifications, and `[Open]` calls retain the previous protocol.
Ghost parameters explicitly marked `[Plain]` do not select the closed protocol.
Proofs using this path name receiver state through model observations.

The current bridge requires a known view, stable owner binding, and a
nonwrapping iterator record without additional record refinements. It is not
an arbitrary-subclass or general IEnumerable cast implementation.
