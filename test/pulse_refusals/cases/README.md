# The obligations, and a program that fails each of them

Every case here is C# that `palcs` translates without complaint and F* then refuses. The
suite is indexed by *obligation kind* — by what the translation asks the prover to
establish — rather than by C# feature, because a suite grouped by feature tends to exercise
the same two obligations from a dozen angles and still leave whole rules untested. Grouped
this way the table below is an inventory: it says which obligations the scheme generates,
and every row is a program that makes exactly that one fail.

Two kinds of case live here and they are worth telling apart.

Most are **the obligation working**: the frontend deliberately declines to rule on these,
because a rule about what a separation logic can prove belongs in the separation logic. §0
rule 3 says the emitter never invents a proof step; these are the same rule pointed the
other way, and they are the evidence that the checker does its half.

Four are **counter-tests**: the exact program that verified before a soundness bug was
fixed. They are marked below, and they are the reason a fix cannot silently regress —
each one is a false theorem that `palcs` once proved.

## Safety obligations, from expressions

| Case | The obligation |
|---|---|
| `IndexInBounds` | An array index is below the length. |
| `SumOverflows` | A machine-integer sum is representable at its width. |
| `DivisorNonZero` | A divisor is non-zero, and the quotient representable. |
| `FloorDivContract` † | A specification's `/` is C#'s truncating division, not F*'s floor. |
| `BitAndContract` † | A specification's `&` is bitwise-and, not addition. |
| `BitNotContract` † | A specification's `~` is complement, not the operand unchanged. |

## Contract obligations

| Case | The obligation |
|---|---|
| `PostconditionFalse` | The body computes what the postcondition claims. |
| `PreservesViolated` | An argument a method claims to leave alone is left alone. |
| `CalleePrecondition` | A call site establishes the callee's precondition. |
| `StepCountedTwice` † | An l-value with a side effect is evaluated once, not twice. |
| `BranchMissesPostcondition` | The postcondition holds on *every* path, not on one. |
| `MissingLemma` | A recursive specification is not unfolded at a symbolic index; the step has to be supplied, and this is what happens when it is not. |
| `LemmaNotProved` | A `[Lemma]` is proved, not declared. The most load-bearing case here: were lemma bodies admitted rather than checked, nothing else in this directory would mean anything. |

## Loop obligations

All three parts of the loop rule, separately — a suite that tests only preservation tests
a third of it.

| Case | The obligation |
|---|---|
| `InvariantNotEstablished` | The invariant holds on entry. |
| `InvariantNotPreserved` | The body restores the invariant. |
| `InvariantTooWeak` | Invariant and negated guard together give the postcondition. |
| `MeasureNotDecreasing` | The `[Decreases]` measure falls on every iteration. |

## Ownership and permissions

| Case | The obligation |
|---|---|
| `AliasedArrays` | Two array parameters are separate; a caller cannot pass one twice. |
| `AliasedObjects` | The same, for objects. |
| `FracMutates` | A write needs full ownership, which `[Frac]` does not grant. |
| `BorrowNotReturned` | A span's borrow is given back before the parent is spoken about again. |

## Objects and inheritance

| Case | The obligation |
|---|---|
| `ConstructorInvariant` | The constructor establishes the class invariant. |
| `ClassInvariantBroken` | Every method restores it by the time it returns. |
| `FracSlotOverride` | An override honours the contract in the vtable slot. |
| `UpcastParameter` | An upcast carries the sub-object's invariant to the base. |
| `ListModelWrong` | The §10 inductive model refuses a false claim too. |
| `GenericModelWrong` | So does §15's, at the class's type binders. |

† Counter-test: this program verified before the bug named in `SOUNDNESS_FINDINGS.md` was
fixed.

## Writing a case

Two lines are load-bearing.

`// EXPECT-PULSE: <text>` on the first line names what must appear in the *mapped* message
— the one a user is shown, after `palcs report` has put F*'s complaint back against the C#.
Naming the failed property rather than merely asserting that something failed is what stops
a case from passing for the wrong reason, which is the failure mode a negative suite is
prone to: the program is *meant* to be broken, so any error at all looks like success.

`// MARKER` sits on the line *above* the offending construct, so the C# below it stays
exactly what a reader would write, and so the assertion moves when the file is edited. Note
where the marker goes for a postcondition: an obligation discharged at a method's implicit
exit is reported at the *method*, because the statement that happens to be last is very
often innocent — `BorrowNotReturned` writes through a span and it is the method, not the
write, that then cannot speak about the array. An explicit `return` keeps its own location.

Iterate on one case with `run.sh <CaseName>`; the whole suite is `run.sh`, which runs cases
in parallel (`PAL_JOBS`, default 16).

The quickest way to get the expectation right is to write the case with a placeholder, run
it, and read what the harness prints when the expectation does not match: it dumps the
mapped message, which is the text to choose from. Prefer a fragment naming the property or
the resource; avoid the generated `__v<name>_<n>` counters, whose numbering is not a stable
interface.
