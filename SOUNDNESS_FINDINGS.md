# Soundness audit of `pal-csharp`

An adversarial review of the C#→Pulse verification pipeline, looking for the one thing
that matters: a C# program that **should** fail verification and does not. Four holes were
found, all four confirmed by running the program, all four fixed, all four pinned by new
regression tests.

The two that matter are the first two. Both let a false postcondition be *proved*, and in
both cases the proof was a correct proof — of a different program than the one the C#
describes. That is the shape every unsoundness in a translational verifier has, and it is
the shape this audit went looking for.

---

## Method

Nothing here is an argument from reading the source. Every claim below — including every
claim that something is *sound* — is backed by an actual run of the pipeline, and for the
two real unsoundnesses, by compiling and executing the C# to exhibit a number different
from the one the prover certified.

1. **Built and ran the existing gate first.** `make tools` (pinned F* nightly-2026-08-05),
   `make build`, `make lib`, then the full `make test`. Everything passed. That baseline is
   what makes a later failure meaningful.
2. **Built a one-file harness**, `try.sh`, mirroring `test/verify.mk`: translate with
   `palcs`, compute F* dependency order via `--dep full`, check each module, map the
   result back through `palcs report`, print `VERIFIED` or `REFUSED`. Roughly forty
   candidate exploits were run through it.
3. **Read the gatekeepers directly** — `Passes/Check.cs`, `Passes/Normalize.cs`,
   `Emit/SpecEmitter.cs`, `Emit/CodeEmitter.cs`, `Frontend/*Lowerer.cs` — looking for
   places where the C# and the emitted Pulse could mean different things.
4. **Enumerated the trusted base**: every `assume`, `admit`, `val` in an `.fsti` with no
   `.fst`, and every F* flag. Each was judged against what the CLR actually guarantees.
5. **Three parallel deep dives** over disjoint surfaces — frontend totality (what gets
   silently dropped), ownership and framing (aliasing, borrows, `Old`), and contracts
   (Liskov, invariants, structs, ghost erasure) — each required to *run* its candidates
   rather than reason about them.
6. **For the confirmed bugs, executed the C#.** A proof of `cursor == Old(cursor) + 2` is
   not interesting until you run the program and watch it print `1`.

The negative-test surface was thin going in: **4** `pulse_refusals` cases and 64
`diagnostics` cases against ~50 acceptance directories. A verifier's regression suite is
mostly a record of what it accepts; what pins soundness is the record of what it refuses.
That ratio is the reason two of these findings survived to be found.

---

## Finding 1 — L-value duplication in `++`, `--`, and `op=` — **HIGH, unsound, fixed**

### The claim

R5.3 normalises `x op= e` to `x = x op e` and `x++` to `x = x + 1`. That is a C#→C#
rewrite, and it is sound as a rewrite — on the *syntax*. The implementation performed it on
the *lowered IR*, splicing one lowered L-value into two positions (three for the expression
form, which also snapshots). C# evaluates the L-value of a compound assignment or an
increment **exactly once** (ECMA-334 §12.18.3, §12.21). The emitter evaluated it twice.

For an L-value with no effects this is invisible, which is why it survived. For one with
effects it is not a subtlety — it is a different program.

### The exploit

```csharp
[Requires("0 <= cursor && cursor < 1000")]
[Ensures("cursor == Old(cursor) + 1")]     // Bump advances the cursor by ONE
[Ensures("Result == Old(cursor)")]
public static int Bump(ref int cursor)
{
    int r = cursor;
    cursor = cursor + 1;
    return r;
}

[Requires("0 <= cursor && cursor + 1 < a.Length && a.Length < 1000")]
[Requires("a[cursor] == 0 && a[cursor + 1] == 0")]
[Ensures("cursor == Old(cursor) + 2")]     // FALSE. C# calls Bump once.
public static void PokeOnce(int[] a, ref int cursor)
{
    a[Bump(ref cursor)]++;
}
```

Before the fix:

```
Verified module: Func_LvalDup3_PokeOnce
All verification conditions discharged successfully
RESULT: VERIFIED
```

And then, running the same source as ordinary C#:

```
cursor = 4          (the proof certified 5)
```

The theorem was proved and the program refutes it. The mechanism is visible in the F*
context of a nearby failing variant, which shows **two** postcondition binders for `Bump`
— `_post_cursor7` and `_post_cursor10` — where the C# has one call.

The second-order damage is worse than the counter. The emitted code writes to `a[t₀]` and
reads from `a[t₁]` with `t₀ ≠ t₁`: it increments an element the C# never touches, and
leaves the element the C# does touch alone. Any client proof about the array contents is
equally available to be false.

Confirmed in all three positions:

| Form | Written | Proved | Actual |
|---|---|---|---|
| increment | `a[Bump(ref cursor)]++` | `+2` | `+1` |
| compound | `a[Bump(ref cursor)] += 5` | `+2` | `+1` |
| expression | `return a[Bump(ref cursor)]++` | `+3` | `+1` |

### The fix

`LinearizeLValue` in `Frontend/ExprLowerer.cs`, wired into `StmtLowerer.Step`,
`StmtLowerer.LowerAssignment`, and `ExprLowerer.Step`. The effectful part of an L-value is
evaluated once into a fresh immutable local, and every copy of the L-value names that
local — the same discipline `Normalize` already applies to a `switch` scrutinee.

That works for an **index**, which is a value. It does not work for the array or the
receiver, which are resources: hoisting a resource is a *move*, not a binding, and the
second occurrence would find it gone. So `Make()[0] += 1` is **refused** (**PALCS0578**)
rather than approximated. §0 rule 3 — the emitter never invents a proof step — cuts both
ways, and a linearisation the ownership discipline cannot express is a guess.

`HasEffect` is deliberately conservative: a method call, a `new`, a `new[]`, or a nested
statement-expression. `[Lemma]` calls are `[Conditional("PAL")]` and erased, so duplicating
one is not observable and is not treated as an effect.

### What now pins it

- `test/step_once/StepOnce.cs` — five methods whose contracts *count the calls*, so a
  translation that duplicated the L-value would fail them. Includes `a[i++] += 1`, where
  the index is itself an increment.
- `test/pulse_refusals/cases/StepCountedTwice.cs` — the false theorem above. It must now
  fail in Pulse, and must fail against the `cursor` postcondition on the marked line.
- `test/diagnostics/cases/EffectfulLValueReceiver.cs` — PALCS0578 on the un-hoistable case.
- `doc/translation.md` **R5.3a** now states the single-evaluation rule.

---

## Finding 2 — a specification's `/` and `%` were F*'s, not C#'s — **HIGH, unsound, fixed**

### The claim

C# rounds `/` and `%` toward **zero**. F*'s `Prims.op_Division` and `op_Modulus` round
toward **minus infinity**. They differ on exactly one input class, and it is a class nobody
tests:

| | C# | F* |
|---|---|---|
| `-7 / 2` | `-3` | `-4` |
| `-7 % 2` | `-1` | `1` |

The *program* side was always faithful: `CodeEmitter` emits `I32.div`, which is
`FStar.Int.op_Slash_Subtraction`, the truncating division ("Multiplicative operator
semantics, see C11 6.5.5"). The *specification* side emitted F*'s `/` and `%`. So a
contract written in C# syntax meant something the C# does not, and the divergence is
invisible: both readings are spelled `x / 2`, and they part company only at a sign the
reader was not thinking about.

This is not a soundness hole in the logic. It is worse in a way: the logic is fine and the
*contract* is a lie. A caller reading `[Ensures("Result == x / 2")]` and reasoning in C#
draws a false conclusion, with a proof behind it.

### The exploit

```csharp
[Requires("x > -1000 && x < 1000")]
[Ensures("Result == x / 2")]
public static int Half(int x)
{
    if (x >= 0) { return x / 2; }
    return (x - 1) / 2;        // floor division
}
```

`Half` computes floor division. Before the fix this **VERIFIED**, because the contract's
`/` was also floor division. Running it:

```
Half(-7) == -4          C#'s (-7) / 2 == -3
```

The method does not satisfy its contract as any C# programmer would read it, and the
pipeline certified that it does.

The dual case is as bad. `[Ensures("Result == -7 / 2")]` on a method that honestly computes
`a / b` at `a = -7, b = 2` was **REFUSED** before the fix — a correct program rejected
because the specification language disagreed with the language it was quoting.

`doc/translation.md` R6.4 documented the *obligation* (`y != 0`) and said nothing about
rounding, so this was an undocumented discrepancy rather than a considered choice.

### The fix

`Pulse.Lib.CSharp.Seq` gains `cdiv` (`FStar.Int.op_Slash_Subtraction`) and `crem`
(`a - cdiv a b * b`), plus `SMTPat` lemmas `cdiv_nonneg` / `crem_nonneg` identifying them
with F*'s operators on non-negative operands, and `cdiv_crem` for the division identity.

`SpecEmitter.Binary` emits `CS.cdiv` / `CS.crem` **when both operands are machine integers
and at least one is signed** — the only configuration where the divergence is reachable.
The two exclusions are not conveniences, they are the rule:

- **Spec-only numerics** (`SpecInt`, `SpecNat`) are mathematics. There is no C# operator
  for them to disagree with, so `/` is the floor division it looks like.
- **Unsigned machine integers** are non-negative, where the two roundings coincide
  *exactly*. F*'s operators already are C#'s, and rewriting them would only cost proofs.

That distinction is load-bearing, and finding it was the interesting part of this fix. The
first attempt applied C# semantics to every `/` and `%` in spec position, and broke
`examples/adler32`: its `CongAdd` lemma is stated over `SpecInt` with a `[PulseBody]`
appealing to `FStar.Math.Lemmas.lemma_mod_add_distr`, which is a theorem about `%`. That
was the right failure to get. A congruence lemma over mathematical integers *is*
mathematics, and forcing C# rounding onto it was the emitter answering a question nobody
asked. After narrowing, `examples/adler32` verifies unchanged.

### What now pins it

- `test/spec_division/SpecDivision.cs` — both sides of the rule. `DivNegative` and
  `RemNegative` state the answer twice, once as a literal and once as the C# expression, so
  the two `Ensures` are consistent only under truncation. `TwoWorlds` asserts
  `Floor2(-7) == -4` (mathematics) and `-7 / 2 == -3` (C#) in the same method — both hold,
  and neither would if one rule were used for both. `RemUnsigned` pins the unsigned path.
- `test/pulse_refusals/cases/FloorDivContract.cs` — `Half` above. It must now fail, and the
  refusal must name `CS.cdiv`.
- `doc/translation.md` **R6.4a** states the rule and why it turns on the operand types.

---

## Finding 3 — mutual recursion crashed F* instead of being diagnosed — **MEDIUM, fixed**

`Check.cs` required `[Decreases]` on a recursive method (PALCS0568), but `MentionsSelf`
only detected a **direct** self-call (`c.Callee == m.Name`). A cycle through two methods —
or through two `[Spec]` functions — was not recursion as far as the frontend was concerned,
so it was emitted, as two separate `fn` / `let` definitions that reference each other.

`fn rec` and `let rec` are single-binding forms. There is no emission for a cycle. What
happened instead was that F* accepted the modules individually and then failed with an
**internal error**:

```
Impossible: cycle detected after cycle detection has passed
```

No line, no C# name, no measure, nothing a user could act on. That is not an unsoundness —
nothing false was proved — but it violates the sentinel property §0 states: the pipeline
never fails in a way it cannot explain. A user hitting this learns that the tool is broken,
not that their program is out of scope.

**Fixed** by `CheckCallCycles` in `Passes/Check.cs`: a whole-program call-graph cycle
search over methods and `[Spec]` functions together, reporting each cycle once (against its
lexicographically least member, so a 3-cycle is one diagnostic, not three) and naming the
whole path. **PALCS0579**.

Pinned by `test/diagnostics/cases/MutualMethods.cs` and `MutualSpecs.cs`; documented under
R10.6.

---

## Finding 4 — `??=` and `>>>=` crashed the translator — **LOW, fixed**

`StmtLowerer.LowerAssignment` handled the compound operators it knew and ended in
`throw new NotSupportedException`. `x ??= y` and `u >>>= 1` are ordinary C#; both produced
a .NET stack trace instead of a diagnostic.

Same sentinel-property violation as Finding 3, smaller blast radius. Replaced with
`diagnostics.Unsupported(...)` (**PALCS0001**), pinned by
`test/diagnostics/cases/UnsupportedAssignmentOperator.cs`.

---

## The trusted computing base

Every axiom in the pipeline, in descending order of blast radius. All of them were read;
all of them are true of the CLR. No `--lax`, no `--admit_smt_queries`, no `friend`
anywhere.

| Axiom | Where | What it asserts | Judgement |
|---|---|---|---|
| `recover` | `Pulse.Lib.CSharp.Assumptions.fsti` | a reference's dynamic type is one of its hierarchy's leaves | **True** of the CLR — a sealed hierarchy has no other case. Deliberately in `stt`, not `stt_div`, so it cannot be used to fabricate a non-terminating proof. Largest single axiom; correct. |
| `clr_array_length_header` | `Pulse.Lib.CSharp.*` | an array's length is non-negative and fits `int` | **True.** The CLR stores the length in the object header and caps it at `Int32.MaxValue`. |
| `clr_span_length_header` | ditto | the same for a span | **True**, same reasoning. |
| `SizeTFitsU32` | ditto | `size_t` admits every `uint32` | **True** on every platform the CLR targets. |
| `alloc`'s `admit()` | array allocation | allocation yields a fresh, fully-owned array | **True**; this is what `newarr` does. |
| `length_i32`'s `admit()` | length accessor | the `int` view of the length agrees with the model | **True**, given the header axiom. |

`Pulse.Lib.CSharp.Assumptions` is `.fsti`-only, so `val recover` is an axiom *by
construction* rather than by an `assume` keyword someone might delete by accident. That is
the right way to hold an axiom.

### The escape hatches are warnings, not errors

`[Admit]` (PALCS0900), a `[Lemma]` with no `[Ensures]` (PALCS0901), and `Pal.Assume`
(PALCS0902) are **warnings**. They do not fail the gate. That is defensible — they are
development tools, and the diagnostics do fire — but it means a repository can accumulate
admitted proofs and still be green.

The suite is clean today: no accepted test or example uses `[Admit]` or `Pal.Assume` in a
load-bearing way (the sole occurrence is `test/annotations/Annotated.cs:107`, testing the
annotation itself). **Recommendation:** a CI mode that promotes PALCS0900/0901/0902 to
errors, so the property "this repository contains no admitted proof" is checked rather than
maintained by habit.

Separately, `test/pulse_facts/*.fst` contain hand-written `assume`s
(`DeepHierarchy.fst:173,274`, `InheritanceFacts.fst:144,147`, `ShapeHierarchy.fst:135,236`).
These are probes *modelling* the encoding, not part of the emitted pipeline, so they cannot
affect a user's proof — but they are worth a comment saying so, since a reader grepping for
`assume` will find them first.

---

## Attack surfaces probed and found sound

These are as much of the result as the bugs are. Each was attacked with a concrete program
and each refused it, for the right reason.

**Aliasing.** `SetBoth(ref a, ref a)` and `SetBoth(x, x)` are both refused: `MethodPlan`
joins per-parameter resources with `**`, so a repeated argument demands `2.0` of a
fractional permission the caller has `1.0` of. This is the separation logic doing exactly
its job, and it means the pipeline never needs an aliasing analysis — the discipline is not
approximated, it is enforced. `ref arr[i]` and `ref obj.f` are refused up front
(PALCS0402).

**Span borrow and restore.** Attempted: double-restore, restore a span never borrowed,
restore the wrong span, hold two writable overlapping windows. All impossible, and for a
structural reason rather than a check: the receipts (`is_from_array`, `is_range_of`,
`is_sub_of`) are *resources*, so using one twice is using a resource twice. Restoring a
span parameter is PALCS0590.

**Liskov / contract inheritance.** An `override` may not carry a contract at all
(PALCS0544). The contract lives once, on the `abstract` declaration. Contract weakening is
not checked because it is not expressible — the strongest possible design.

**Structs.** True value semantics; assignment emits a fresh copy. No aliasing through a
struct field.

**`Old`.** `Old(a[i])` captures the pre-state array *and* the pre-state index, which is the
subtle case and the one usually gotten wrong.

**Ghost erasure.** `Ghost<T>.Value` throws at runtime and `SpecInt`→`int` is a C# compile
error (CS0030), so a ghost value cannot become a program value. `[Spec]` functions cannot be
called from executable code (PALCS0001), which closes the corresponding route: `SpecInt`
mathematics can never be substituted for C#'s 32-bit semantics at runtime.

**Static mutable state.** Refused (PALCS0001), not silently treated as pure.

**Loop measures.** The counted-`for` measure is an `IrTypeBoundMeasure` that Pulse still
checks each iteration, so a body that moves the counter backwards is refused rather than
trusted to the syntactic form.

**Evaluation order.** Short-circuit `&&` / `||` and left-to-right operand order are
preserved by `CodeEmitter.Binary` / `Assign`. R13.3's decision to emit an expression-position
`++` *at the operator's own position* rather than hoisting it is what makes
`p && a[i++] > 0` faithful — hoisting would have been wrong, and the design notes say so.

**Diagnostic-to-source mapping.** The `pulse_refusals` harness checks not just that Pulse
refuses but that the mapped message lands on the marked C# line. A refusal reported against
the wrong statement is its own kind of unsoundness — the user fixes the wrong thing — and
this is checked.

---

## Tests added

| File | Kind | Pins |
|---|---|---|
| `test/step_once/StepOnce.cs` | acceptance | An L-value is evaluated once, in all three of `++`, `op=`, and expression position, with contracts that count the calls. |
| `test/spec_division/SpecDivision.cs` | acceptance | Spec `/` and `%` are C#'s over signed machine ints, and mathematics over `SpecInt`, in the same file. |
| `test/pulse_refusals/cases/StepCountedTwice.cs` | refusal | The `+2` theorem Finding 1 proved must now fail, on the right line. |
| `test/pulse_refusals/cases/FloorDivContract.cs` | refusal | Finding 2's floor-division contract must now fail, naming `CS.cdiv`. |
| `test/diagnostics/cases/EffectfulLValueReceiver.cs` | diagnostic | PALCS0578 — un-hoistable effectful receiver. |
| `test/diagnostics/cases/UnsupportedAssignmentOperator.cs` | diagnostic | PALCS0001 — `>>>=` diagnosed, not thrown. |
| `test/diagnostics/cases/MutualMethods.cs` | diagnostic | PALCS0579 — mutual recursion between methods. |
| `test/diagnostics/cases/MutualSpecs.cs` | diagnostic | PALCS0579 — mutual recursion between `[Spec]` functions. |

Two of these are *counter-tests*: `StepCountedTwice` and `FloorDivContract` are the exact
programs that were verified before this audit. They are the tests that would have caught
these bugs, and they are the reason the bugs cannot come back.

`pulse_refusals` goes from 4 cases to 6; `diagnostics` from 64 to 68.

---

## Recommendations not acted on

1. **A CI mode promoting PALCS0900/0901/0902 to errors.** See the TCB section. The property
   is currently maintained by convention.
2. **Grow the refusal suite deliberately.** Four `pulse_refusals` cases against ~50
   acceptance directories is the ratio that let Findings 1 and 2 survive. The useful
   discipline is that a new *rule* arrives with the program that rule refuses, not only the
   program it accepts — `pulse_refusals/run.sh` already checks the refusal lands on the right
   line, so these tests are strong.
3. **Comment the `assume`s in `test/pulse_facts/`** to say they model the encoding and are
   not in the emitted path.
4. **Consider a general C#-semantics audit of the spec language.** Finding 2 was one
   operator where spec syntax and C# syntax coincided while their meanings did not.
   Shift operators (C# masks the count to 5 or 6 bits), integral conversion and promotion,
   and `char` arithmetic are the places the same question could have a different answer,
   and none was probed as thoroughly as division was.

---

## Verification status

The tool builds (`make build`, `make lib`), the Pulse support library verifies, and the
full gate (`make test` — every acceptance directory, `examples/adler32`, the diagnostics
suite, the refusal suite, and the seven lint checks) passes with all of the above in place.
