# The pal-csharp translation scheme

This document defines `⟦·⟧`, the translation from annotated C# to Pulse. It is the
**specification of the emitter**: `Pal.Compiler` is an implementation of the rules below,
and anything the emitter does that is not justified by a rule here is a bug.

Every rule is **compositional**: it is defined by the shape of a C# construct alone,
independently of any example and of its surrounding context.

---

## 0. The anti-contortion discipline

It is easy to write each test program directly in clean, idiomatic Pulse and then contort
the translator into producing that. The result is a pile of per-example hacks wearing a
compiler's clothes. The goal is a **translation of C#, reflecting C# semantics and
structure** — not a re-implementation of each example in Pulse.

Four rules, in force from the first commit.

**Rule 1 — Scheme before code.** This document precedes the emitter. Derived Pulse is
obtained by *hand-executing* the rules, never authored freely. Output that cannot be
justified rule-by-rule is a bug in the scheme, not a licence to tweak the output.

**Rule 2 — Structure preservation.** Emitted Pulse mirrors its source (§3–§6). Explicit
anti-goals: no inlining, no constant folding, no reordering or reassociating control flow,
no rewriting an imperative loop into a recursion or a fold, no whole-method
"recognise this algorithm" pattern matching.

**Rule 3 — The emitter never invents proof steps.** When a proof needs help, the help
comes from exactly two places:
* the user's C# annotations — `Pal.Invariant`, `Pal.Assert`, `[Lemma]` calls,
  `Pal.GhostStmt`, `Ghost<T>` arguments (this is *the point* of a proof annotation
  language); or
* general-purpose lemmas in `Pulse.Lib.CSharp.*`, usable by any program.

A special case in the emitter is never a legitimate fix.

**Rule 4 — No example is nameable from inside the compiler.** `Pal.Compiler` contains no
identifier drawn from the test suite. Enforced by `test/no-example-names.sh`.

Two mechanical detectors back these up: **variant tests** (every acceptance test ships an
equivalent but differently-written C# variant that must verify with no emitter change) and
the **provenance lint** (every emitted top-level construct must trace to a C# source span
via `source_range_info.json`).

---

## 1. Validated Pulse facts

The rules below depend on the following, each **verified against the pinned toolchain**
(`tools/fstar`, nightly-2026-07-30) rather than assumed:

| # | Fact | Evidence |
|---|---|---|
| F1 | A `while` condition may be a **stateful statement block**, so short-circuiting guards that read memory need no flag-rotation encoding. | `pulse/lib/Pulse.Lib.Array.fst:41-42` uses `while (let vi = !i; if (vi < l) { a1.(vi) = a2.(vi) } else { false })`; reproduced locally in `W3.fst`, verified. |
| F2 | Every `while` in a terminating `fn` **requires `decreases`**; without it the loop is `stt_div` and fails to compose with the `stt` continuation ("Cannot compose computations in this divergent block"). | Reproduced locally: `W2.fst` fails, `W3.fst` succeeds with `decreases` added. |
| F3 | A `decreases` measure **may dereference mutable locals** (`!i`), but **may not** mention invariant-bound existentials. | `Pulse.Lib.Array.fst:49`, `Pulse.Lib.ArrayPtr.fst:385`; local `W3.fst` failed with `reveal v`, succeeded with `!i`. |
| F4 | Pulse source requires the `#lang-pulse` pragma after the module header and `open`s. | `pal/pulse/Pulse.Lib.C.Array.fst:9`; local `Smoke.fst`, verified. |
| F5 | The F* binary release bundles Pulse; no separate install is needed. | `tools/fstar/lib/fstar/pulse/` present after `make tools`. |
| F6 | Every support-library operation whose result is consumed inside a `while` guard **must** specify its result with `rewrites_to`, not `pure (x == …)`. A `pure` postcondition leaves the let-bound intermediate existentially quantified, and Pulse then cannot infer the guard's postcondition — it reports `Cannot find witness for exists* (t: …)`. | Discovered by the insertion-sort probe (`test/probe_insertion_sort`): both `Array.length_i32` and `Array.read` failed this way and were respecified with `rewrites_to`. Pulse's own `op_Array_Access` and PAL's `array_read_all` do the same. |
| F8 | A **stateful block may appear in term position**, as the scrutinee of a `let`: `let t = if (c) { <stateful block> } else { e };` is well-formed Pulse. This is what makes the short-circuit rule R6.3 compositional — the same lowering serves a loop guard, an `if` condition and an assignment right-hand side, with no context-dependent special case. | `test/pulse_facts/PulseFacts.fst:short_circuit_in_term_position`, verified; relied on by every generated short-circuit. |
| F9 | A `decreases` measure may dereference a mutable local, but **not underneath an `if`**. `decreases (if !b then 0 else I32.v !r)` is rejected with "Expected type `FStar.Int32.t` but `!r` has type `fn …`", because the `!` sugar is elaborated only outside the branches. A conditional measure must keep its dereferences out of the branches. | `test/pulse_facts/PulseFacts.fst:decreases_conditional_without_deref`, verified; the failing form was reproduced while writing `test/binary_search`. |
| F7 | `Pulse.Lib.Array` provides no SMT-patterned link between `Array.Core.length a` and `Seq.length s`; `pts_to_len` must be invoked explicitly. Modelling `a.Length` as a *pure* function of the array (sound, because a CLR array's length is immutable) avoids needing it at every guard. | `Pulse.Lib.Array.fst:38,65,117` all call `pts_to_len` by hand; `Pulse.Lib.CSharp.Array.arr_length` takes the pure route. |
| F10 | F\* resolves **module-qualified record syntax** in all three positions — projection `e.M.f`, update `{ e with M.f = v }`, and literal `{ M.f = a; g = b }` — without the defining module being `open`ed. So a generated struct module needs no `open` anywhere, and two structs may share a field name with no ambiguity. | `test/pulse_facts/PulseFacts.fst` + `test/pulse_facts/StructFacts.fst`, verified. |
| F11 | A record **update's source must be a pure term**: `{ !r with M.f = v }` is rejected ("Ill-typed term … got expression of type `fn … returns …`"), because `!r` is a stateful operation and the update is a term former, not a statement. The deref must be let-bound first. This does not contradict F8: F8 is about a stateful block as the *scrutinee of a `let`*, which is precisely the form that fixes this. | `test/pulse_facts/StructFacts.fst:struct_field_write`, verified; the failing form was reproduced while writing R3.4. |
| F12 | A Pulse `fn` **must have at least one binder**. A parameterless one fails in the elaborator, not the solver: "Tactic failed — main: FnDefn does not have binders". So a C# method with no parameters takes `()`. | `test/pulse_facts/StructFacts.fst:no_parameters`, verified; the failing form was reproduced by `test/point_struct`'s `Origin()`. |

F1 and F8 together **retire** the plan's original top risk: no `cont`-flag rotation and no
auto-generated short-circuit invariants are needed. F2 introduces a new obligation
(§5.3). F6 and F7 are constraints on the *library*, not on the emitter, and are the reason
`Pulse.Lib.CSharp.Array` is not a thin `include` of `Pulse.Lib.Array`.

Two further points of Pulse syntax, learned the hard way and pinned by the same test:
a `decreases` clause on a `while` takes **no trailing semicolon**, and a recursive F\*
definition needs `: Tot t (decreases m)` rather than `: t` followed by `(decreases m)`.

One semantic fact matters more than any of these for anybody *writing* annotations:
**a Pulse loop body sees the invariant and nothing else.** Pure facts from the enclosing
`requires` are not in scope inside the loop. Any precondition the body still needs must be
restated as an invariant. This is by far the most common annotation fix, and it is not
something the translator may paper over (§0, rule 3).

---

## 2. Modules, names, and output layout

Following PAL's conventions.

| C# declaration | Emitted module |
|---|---|
| method `C.M` | `Func_C_M.fsti` (signature + contract) and `Func_C_M.fst` (body) |
| `struct S` | `Struct_S.fst` |
| `[Spec]` method `C.P` | `Let_C_P.fst` |
| `[Lemma]` method `C.L` | `Let_C_L.fst` |
| `[PulseType]` type `T` | `Type_T.fst` |
| `IncludePulse("M", …)` | `M.fst` |
| static field | `Global_F.fst` |
| — | `TranslationErrors.fst` — contains `let _ = assert False` iff translation reported errors, so running F* on the output directory always surfaces translation problems |

**R2.1 (naming).** A C# method `Ns.C.M` emits `fn func_C_M` in module `Func_C_M`. A
parameter `p` becomes the Pulse binder `var_p`. A local `x` becomes `var_x`. A `[Spec]`
function becomes `spec_C_P`, a `[Lemma]` becomes `lemma_C_L`. Name mangling is a pure
function of the source name; the emitter never chooses names by inspecting a program's
meaning.

PAL can name a module after the function alone, because C has a single global function
namespace. C# does not — two classes in one program may each declare `Abs` — so the
declaring type is always part of the name. Always, not only on collision: a program's
generated module names must not change when an unrelated class is added.

**R2.2 (provenance).** Every emitted construct records the Roslyn `Location` it came from,
written to `source_range_info.json` as
`{module, file, construct, source: {file, range}}`. A module whose whole text is the
user's own Pulse (`[assembly: IncludePulse]`) records the single construct `"*"`.

`test/provenance-lint.sh` reads the generated `.fst` files — not the compiler's account of
what it did — extracts every top-level `fn`, `let` and `let rec`, and requires each to
appear in `source_range_info.json` with a span in a C# file that exists. A construct with
no provenance was invented by the translator, and anything the translator invents must be
justified as a numbered rule in this document rather than as a response to one example.
An emitter that *forgets* to record a construct therefore fails exactly as loudly as one
that invents it. The lint runs in `make -C test` and in CI, alongside
`test/no-example-names.sh`; together they are §7.2's two mechanical detectors.

---

## 3. Types

**R3.1 (scalars).** `bool→bool`, `int→Int32.t`, `uint→UInt32.t`, `long→Int64.t`,
`ulong→UInt64.t`, `byte→UInt8.t`, `sbyte→Int8.t`, `short→Int16.t`, `ushort→UInt16.t`,
`char→UInt16.t`, `nint→PtrdiffT.t`, `nuint→SizeT.t`. `SpecInt→int`, `SpecNat→nat`,
`Seq<T>→Seq.seq ⟦T⟧`, `SlProp→slprop`. `float`/`double` are rejected in M1.

**R3.2 (ownership from the C# type system).** C# already encodes what PAL needs explicit
macros for. No attribute is required for any of these:

| C# parameter | Pulse binder | `requires` | `ensures` |
|---|---|---|---|
| `T x` (value) | `var_x: ⟦T⟧` | — | — |
| `ref T x` | `var_x: ref ⟦T⟧` | `pts_to var_x v` | `pts_to var_x v'` |
| `out T x` | `var_x: ref ⟦T⟧` | `pts_to_uninit var_x` | `pts_to var_x v'` |
| `in T x` | `var_x: ref ⟦T⟧` | `pts_to var_x #p v` | `pts_to var_x #p v` |
| `T[] a`, `Span<T> a` | `var_a: array ⟦T⟧` | `array_pts_to_full var_a 1.0R s` | `array_pts_to_full var_a 1.0R s'` |
| `ReadOnlySpan<T> a` | `var_a: array ⟦T⟧` | `array_pts_to var_a #p s` | `array_pts_to var_a #p s` |

Attributes are needed only for the residue: `[Consumes]`, `[Plain]`, `[Frac]`, `[NonNull]`,
`[CoreRef]`.

**R3.3 (the index bridge).** C# array lengths and indices are signed `int`; Pulse arrays are
indexed by `SizeT`. This crossing is pervasive, so it is fixed here once and never decided
per-example:

* `a.Length` ⟶ `Pulse.Lib.CSharp.Array.length_i32 var_a : Int32.t`, whose result
  `rewrites_to` the **pure** model `arr_length var_a` (F6, F7). Purity is not an
  optimisation: a CLR array's length is fixed at allocation, so `a.Length` genuinely is a
  function of `a`, and modelling it that way is what makes a counted `for` over an array
  — where `a.Length` appears in the *guard* — translatable at all. `arr_length` returning
  `Int32.t` is also where the bound `length a < 2^31` enters, since
  `System.Array.Length` has type `int`.
* an index expression `e` in a subscript ⟶ `Pal.Idx ⟦e⟧`, where
  `Idx : (i:Int32.t{Int32.v i >= 0}) -> SZ.t` with `SZ.v (Idx i) == Int32.v i`.
  The side condition `Int32.v i >= 0` is discharged by the bounds obligation of R6.4.
* in *spec* position an index is `Int32.v ⟦e⟧ : nat`, used directly with `Seq.index`.

**R3.4 (structs).** A C# `struct` is a **value**: it has no identity, assignment copies it,
and — unlike a C `struct` — nothing may hold a pointer into the middle of one. That single
fact collapses almost all of PAL's struct machinery. Where PAL emits a record, a ghost
spec type, fold/unfold predicates, per-field pointer projectors and their axioms, a C#
`struct` needs only an F\* record.

A declaration

```csharp
[Refine("P₁")] … [Refine("Pₙ")]
struct S { T₁ f₁; … T_k f_k; }
```

becomes `Struct_S.fst`:

```fstar
noeq type struct_S__raw = { fld_f₁: ⟦T₁⟧; … ; fld_f_k: ⟦T_k⟧ }
let struct_S__pred (this: struct_S__raw) : prop = ⟦P₁⟧ /\ … /\ ⟦Pₙ⟧
type struct_S = this: struct_S__raw { struct_S__pred this }
```

and `⟦S⟧ = Struct_S.struct_S`. Notes, each of which is a decision rather than an accident:

* **Fields are prefixed `fld_`** and always referred to module-qualified (`e.Struct_S.fld_f`),
  so a C# field name can never collide with a Pulse keyword, with another struct's field,
  or with anything in the preamble. By F10 this needs no `open`, which is why a generated
  function module's dependency list never mentions a struct module.
* **The refinement is a refinement type, not a separate obligation to remember.** Anything
  that *produces* an `S` must prove `struct_S__pred`, and anything that *consumes* one may
  assume it — which is exactly what `[Refine]` means, and it falls out of F\* subtyping
  with no work from the emitter.
* **A refinement is bound with the struct's fields in scope as simple names.** `[Refine("Lo <= Hi")]`,
  not `[Refine("this.Lo <= this.Hi")]`: inside a C# `struct` declaration an unqualified
  `Lo` already means "this instance's `Lo`", so this is the reading a C# programmer expects,
  and it lets the shim of §4 be an ordinary static method whose parameters are the fields.
  `this` is a C# keyword and cannot be a shim parameter, so PAL's spelling is unavailable
  even if it were wanted.
* `struct_S__pred` is emitted even when there are no `[Refine]`s, as `True`. Uniform output
  beats output with fewer moving parts in one case and more in another (§0 rule 2).
* **A field's type must itself be translatable and must be a value.** Scalars and other
  translated structs qualify. A reference-typed field — an array, or a class — does not,
  because it would make the struct own a resource, and a value carrying a resource needs
  the separation-logic predicate and fold/unfold discipline this rule exists to avoid.
  Rejected as PALCS0511; see §8.

**R3.5 (struct expressions).** Three forms, all structure-preserving:

| C# | Pulse |
|---|---|
| `e.f` | `⟦e⟧.Struct_S.fld_f` |
| `new S { f₁ = e₁, … }` | `{ Struct_S.fld_f₁ = ⟦e₁⟧; … }`, every field present |
| `new S()`, `default(S)` | the same literal with every field at its type's zero |

C# guarantees a `struct` is fully initialized at construction, so the emitted literal is
always total: a field the user did not mention is filled with its zero, which is what the
CLR does. `default(S)` on a refined `S` therefore carries a real proof obligation — the
zero value must satisfy the refinement — and that is correct, since a `default(S)` that
violates `[Refine]` is a bug the annotation was written to catch.

**R3.6 (struct assignment).** `x.f = e` where `x` is a local or `ref` parameter becomes a
whole-value update of `x`'s cell, because that is what a C# field assignment on a value
type *is*:

```
let t = !var_x;
var_x := { t with Struct_S.fld_f = ⟦e⟧ };
```

The deref is let-bound rather than written inline because a record update's source must be
a pure term (F11). Nested paths compose the same way: `x.f.g = e` updates `f` with an
update of `g`.

---

## 4. Methods and contracts

**R4.1 (method).** A static method

```csharp
[Requires(P₁)] … [Ensures(Q₁)] …
static R M(p₁, …, pₙ)   { B }
```

emits

```
fn func_M (var_p₁: ⟦T₁⟧) … (var_pₙ: ⟦Tₙ⟧) (#g₁: erased ⟦G₁⟧) …
requires ⟦own(p₁)⟧ ** … ** pure (⟦P₁⟧ /\ …)
returns  var_result: ⟦R⟧
ensures  ⟦own'(p₁)⟧ ** … ** pure (⟦Q₁⟧ /\ …)
{ ⟦B⟧ }
```

The ownership conjuncts come from R3.2 and the pure conjuncts from the user's annotations,
in source order. The emitter contributes **no** additional pure conjuncts beyond the
obligations of §6. A method with no parameters at all takes the single binder `()`, since
a Pulse `fn` must have one (F12).

**R4.2 (parameter rebinding).** Every by-value parameter that the body assigns to is
rebound as `let mut var_p = var_p;`, as PAL does. Parameters that are never assigned are
used directly.

**R4.3 (`Old`).** `Old(e)` in an `ensures` denotes `⟦e⟧` evaluated against the `requires`
state: the emitter binds the pre-state existentials once and refers to them. `Old` is
illegal outside a postcondition.

**R4.4 (`Result`).** In an `ensures`, `Result` denotes the `returns` binder `var_result`.

**R4.6 (`[Spec]` methods).** A `[Spec]` method is pure, ghost, and — in M1 —
usable *only* in specification position. Consequently its C# parameter types are
translated with the **spec** reading rather than the code reading:

| C# parameter of a `[Spec]` method | Pulse binder |
|---|---|
| `int`, `long`, … | mathematical `int` (no overflow obligations arise in specs) |
| `T[]`, `Span<T>` | `Seq.seq ⟦T⟧` — the contents, not the array |
| `bool` return | `prop` |

Its `[Requires]` clauses become a **refinement on the last binder**, so that the body
type-checks: `Sorted`'s `hi <= a.Length` is what makes `Seq.index var_a var_j` well-typed
under the quantifier in its body. Correspondingly, at a call site in spec position an
argument of C# type `int` is translated as `Int32.v ⟦e⟧`, and an array argument as its
contents existential.

**R4.5 (ghost parameters).** A parameter of type `Ghost<G>` (necessarily optional, so C#
callers may omit it) emits an erased implicit `(#g: erased ⟦G⟧)` and is erased from the
runtime signature. Equivalently `[GhostArg("G g")]`.

*Known limitation, shared with PAL.* An implicit binder is resolved by unification at the
call site, so a ghost argument that appears only in the **pure** part of a contract is not
determined and such a method cannot yet be called from translated C#. Ghost arguments that
appear in a separation-logic conjunct are resolved from the resource and call normally.

**R4.7 (`[Lemma]` methods).** A lemma is a proof step about the values the program
actually holds, so — unlike a `[Spec]` function (R4.6) — its parameters keep their
**program** reading: `int` is `I32.t`, `SpecInt` is `int`, `T[]` and `Seq<T>` are
`Seq.seq`. It is emitted as an ordinary F\* lemma in `Let_C_L.fst`,

```
let lemma_C_L (var_p₁: ⟦T₁⟧) … : Lemma (requires ⟦P⟧) (ensures ⟦Q⟧) = ⟦body⟧
```

where `⟦body⟧` is the C# body, the `[PulseBody]` text with `$(…)` antiquotation expanded,
or `admit()` under `[Admit]`. A call is a plain ghost statement `Let_C_L.lemma_C_L a₁ … aₙ;`
with the arguments passed **raw** — no `Int32.v` coercion, because the lemma's binders are
already program-typed. A lemma that wants a mathematical index therefore declares `int n`
and lets the specification translation insert `I32.v` where the *specification* needs it.

**R4.8 (postconditions are stated under the precondition).** A Pulse `ensures` is
type-checked in a context that does **not** include the `requires`, so a postcondition
whose well-typedness depends on the precondition — `Result == s[i]` guarded by
`i < s.Length` is the everyday case — would be rejected before any proof is attempted.
The emitted postcondition is therefore

```
ensures … ** pure ((⟦P₁⟧ /\ … /\ ⟦Pₙ⟧) ==> (⟦Q₁⟧ /\ … /\ ⟦Qₘ⟧))
```

This weakens nothing. The precondition is expressed entirely over pre-state binders, which
remain in scope in the postcondition, and the caller has just discharged it, so
`P ==> Q` gives the caller exactly `Q`.

It does **not** rescue a postcondition whose well-typedness depends on an *earlier
postcondition*; F\* type-checks each conjunct of `p₁ /\ p₂` with `p₁` in scope, so the
conjunct that bounds an array must be written before the conjunct that indexes it. That is
an ordering obligation on the annotations, and it is documented rather than inferred.

**R4.9 (fractional permissions).** `[Frac("p")]` on an array or `ref`/`in` parameter
introduces a ghost permission binder `(#p: perm)` and weakens the parameter's resource
from full ownership to `A.pts_to a #p s` (resp. `R.pts_to x #p v`). Two consequences follow
mechanically, and neither is a choice:

* **The contents cannot change**, so the *same* binder stands for the pre- and the
  post-state. The `ensures` needs no existential for that parameter and the caller needs no
  frame reasoning about it. Compare the full-ownership case (R4.1), where every array
  parameter contributes an existential to every postcondition.
* **Writing through the parameter is an error** (`PALCS0305`), reported against the
  assignment. A fractional permission is exactly the right to read.

What this buys, and what nothing else does: the same array may be passed to two parameters
at once, because the caller splits its permission rather than surrendering it.

---

## 5. Statements

**R5.1 (sequence).** `s₁ s₂ … sₙ` ⟶ `⟦s₁⟧; ⟦s₂⟧; …; ⟦sₙ⟧`. **Order is preserved.** The
emitter never reorders, merges, or elides a statement.

**R5.2 (local declaration).** `T x = e;` ⟶ `let mut var_x : ⟦T⟧ = ⟦e⟧;`. Every C# local is
a Pulse `ref` cell; a read of `x` is `!var_x` (R6.1). Locals are *not* promoted to
immutable `let` bindings even when never reassigned — that would be an optimisation, and
optimisations are how translators start fitting examples.

**R5.3 (assignment).** `x = e;` ⟶ `var_x := ⟦e⟧;`. `a[i] = e;` ⟶ `array_write var_a (Idx ⟦i⟧) ⟦e⟧`
after A-normalisation (R6.2). Compound assignment `x op= e` is normalised to `x = x op e`
and `x++` to `x = x + 1` in the Normalize pass, which is a C#→C# rewrite.

**R5.4 (`if`).** `if (c) s₁ else s₂` ⟶ `if (⟦c⟧) { ⟦s₁⟧ } else { ⟦s₂⟧ }`. **Both branches
are always emitted**, even when one is empty.

**R5.5 (`return`).** `return e;` ⟶ `⟦e⟧` in tail position.

**R5.5b (early return).** Pulse has no non-tail `return`, so the Normalize pass rewrites
one away as a **C#→C# transformation**: a statement sequence `s₁ … sₖ rest` in which `sₖ`
is an `if` whose taken branch ends in a `return` becomes

```csharp
s₁ … if (c) { thenBranch } else { elseBranch; rest }
```

so that every `return` is in tail position. The rewrite is driven by the syntactic
predicate "does this branch end in a `return`", is applied uniformly, and preserves the
order and the identity of every statement — it neither duplicates code nor introduces a
flag. `return` inside a loop is *not* restructured; it is rejected with a diagnostic, since
turning it into a flag-driven loop would be the translator inventing control flow.

**R5.6 (`while`).**

```csharp
while (c) { Pal.Invariant(I₁); … Pal.Decreases(m); B }
```

⟶

```
while (⟦c⟧)
invariant ⟦live-set⟧ ** ⟦frame⟧ ** pure (⟦I₁⟧ /\ …)
decreases ⟦m⟧
{ ⟦B⟧ }
```

By F1 and F8 the guard `⟦c⟧` may be a stateful block, so no flag encoding is used. The
`decreases` clause takes **no trailing semicolon** (§1).

A Pulse loop body sees the invariant and nothing else. The emitter therefore does **not**
propagate the enclosing `requires` into the loop; a fact the body needs is the annotation
author's responsibility to restate as an invariant. Inventing invariants is exactly the
"emitter invents proof steps" failure §0 rule 3 forbids.

**R5.7 (`for` → `while`).** `for (init; cond; step) { body }` ⟶
`{ init; while (cond) { body; step } }` as a **C#→C# rewrite** in the Normalize pass. The
emitter only ever sees `while`.

One qualification, for R5.10's sake: C# runs `step` after a `continue` but not after a
`break`, and appending `step` to `body` loses that distinction. So when the body contains
an escape the step is *not* appended; it is carried in a separate slot on the `while` and
emitted by R5.10 under the break flag alone. When the body contains no escape the two are
indistinguishable and the step is appended, as above.

**R5.8 (`live` inference).** The `invariant` includes `pts_to` for every local the loop body
reads or writes, computed from the body's free variables. This is an improvement over PAL,
which requires an explicit `_invariant(_live(x))` per local. It is a syntactic function of
the body, not a search: it does not depend on what the loop is *for*. `Pal.Live(x)` adds a
resource the inference cannot see.

**R5.8b (frame for unassigned locals).** A local that the loop body **never assigns** keeps
its value across the loop, so the emitter binds that value *outside* the loop
(`with v. assert (pts_to var_x v);`) and writes `pts_to var_x v` in the invariant, rather
than existentially quantifying it. Whether a local is assigned is a syntactic property of
the body — it does not depend on what the loop is for — so this is a rule, not an
inference.

Without it, nothing connects the local's value before and after the loop. The
insertion-sort probe found this the hard way: the outer loop's step `i = i + 1` could not
be shown to decrease the measure, because the *inner* loop had existentially rebound `i`
even though it never touches it.

**R5.9 (`decreases` obligation).** By F2 every emitted `while` **must** carry `decreases`.
The measure is obtained, in order:
1. an explicit `Pal.Decreases(m)` in the loop body ⟶ `⟦m⟧`;
2. otherwise, for a loop whose Normalize-pass origin is a counted `for` with a monotone
   integer step — guard `i < h` with step `i = i + k`, `k > 0` — the measure
   **`pow2 31 - Int32.v !var_i`** (and `Int32.v !var_i + pow2 31` for a decreasing
   counter). Note it does **not** mention the loop's upper bound `h`. That is deliberate
   and was forced by the probe: `h` is very often `a.Length`, which is not available as a
   pure expression at the point `decreases` is checked. Since the counter has type `int`
   it is bounded by its own type, and the type's bound is a measure — one that is always
   available, always non-negative, and never requires looking at what the loop is
   counting over. This is a *syntactic* pattern on the loop's own shape, and it satisfies
   F3's requirement that the measure dereference locals rather than invariant
   existentials;
3. otherwise the translation **fails with a diagnostic** demanding `Pal.Decreases`.

Case 3 is deliberate: guessing a measure would be the emitter inventing a proof step
(Rule 3).

**R5.10 (`break` and `continue`).** Pulse has neither. Both are translated with *escape
flags*, allocated only for the forms the body actually uses, so a loop with no escape is
emitted exactly as R5.6 describes.

| C# | Pulse |
|---|---|
| a loop whose body contains `break` | `let mut var_brk_n = false;` **before** the loop |
| a loop whose body contains `continue` | `let mut var_cont_n = false;` as the **first statement of the body**, so it is cleared on every iteration |
| `break;` | `var_brk_n := true;` (and `var_cont_n := true;` if that flag exists) |
| `continue;` | `var_cont_n := true;` |
| guard `c` | `⟦c⟧ && not !var_brk_n` |
| invariant | additionally `exists* v. pts_to var_brk_n v` |
| measure `m` | `⟦m⟧ + (if !var_brk_n then 0 else 1)` |
| `S₁; S₂` in a loop body, where `S₁` may escape | `⟦S₁⟧; if (not !var_brk_n && not !var_cont_n) { ⟦S₂⟧ } else { () };` |
| the `for` step of R5.7 | emitted after the body, under `not !var_brk_n` only |

Four points are worth stating because each is forced, not chosen:

* **The user's guard comes first.** In a short-circuit guard `e₁ && e₂` only `e₁`'s
  dereferences stay visible to the loop body, so appending the flag rather than prepending
  it is what keeps R5.6 loops unchanged.
* **The measure needs the flag.** The iteration that breaks need not decrease the user's
  measure — it exits instead. Adding one while the flag is still clear restores the
  decrease on every path, uniformly. It stays *linear*, which matters: multiplication in a
  measure puts Z3 into nonlinear mode and destabilises unrelated obligations in the same
  definition. It also stays inside F9, which forbids a dereference in a *branch* of an
  `if` in a measure but not in its condition.
* **`var_cont_n` needs no invariant** because it is allocated inside the body and so does
  not cross the loop's boundary.
* **The guard is a syntactic test.** "May escape" is a walk over the statement that stops
  at a nested loop, whose own `break` and `continue` bind to that loop. It never looks at
  what the loop computes.

**R5.11 (ghost statements).** `Pal.Assert(p)` ⟶ `assert (⟦p⟧)`. A call to a `[Lemma]`
method ⟶ the corresponding ghost call. `Pal.GhostStmt("…")` ⟶ the string verbatim, after
antiquotation expansion.

---

## 6. Expressions

**R6.1 (variables).** A read of local or rebound parameter `x` ⟶ `!var_x`. A read of a
non-rebound by-value parameter `p` ⟶ `var_p`.

**R6.2 (A-normalisation).** C# expressions may nest effectful subexpressions; Pulse
statements are atomic. Every effectful subexpression (array read, method call) is therefore
lifted into a `let` binding, **in C#'s guaranteed left-to-right evaluation order**:

```csharp
a[j + 1] = a[j];
```
⟶
```
let t0 = array_read var_a (Idx (!var_j));
array_write var_a (Idx (!var_j + 1l)) t0;
```

This is a single uniform rule, not a peephole. Pure subexpressions are not lifted.

**R6.3 (short-circuit operators).** By F1:

* `e₁ && e₂` ⟶ `let t = ⟦e₁⟧; if (t) { ⟦e₂⟧ } else { false }`
* `e₁ || e₂` ⟶ `let t = ⟦e₁⟧; if (t) { true } else { ⟦e₂⟧ }`
* `c ? e₁ : e₂` ⟶ `if (⟦c⟧) { ⟦e₁⟧ } else { ⟦e₂⟧ }`

When `e₂` is pure, this degenerates to the plain Pulse operator. The rule is stated once
and applies identically in a loop guard, an `if` condition, and an assignment RHS —
which is exactly what makes insertion sort's `j >= 0 && a[j] > key` unremarkable.

**R6.4 (arithmetic and proof obligations).** `e₁ op e₂` ⟶ the corresponding
`Pulse.Lib.CSharp.Int32` operation, which carries the obligation. C# semantics differ from
C's, so M1 fixes:

| Construct | C# runtime behaviour | M1 obligation |
|---|---|---|
| `x + y`, `x * y`, … | wraps (`unchecked`, default) | **no overflow** |
| `a[i]` | throws `IndexOutOfRangeException` | `0 <= i < a.Length` |
| `x / y`, `x % y` | throws `DivideByZeroException` | `y != 0` |
| `o.f` | throws `NullReferenceException` | `o != null` |

M1 therefore proves **exception freedom**; `try`/`catch`/`throw` are rejected. The
no-overflow choice matches PAL and is revisited if it proves onerous; `[Unchecked]` would
opt into a wrapping model.

**R6.5 (array access).** `a[i]` ⟶ `array_read var_a (Idx ⟦i⟧)` in code, and
`Seq.index s (Int32.v ⟦i⟧)` in spec position, where `s` is the array's contents
existential. `a.Length` ⟶ R3.3.

**R6.6 (calls).** `C.M(a₁, …)` ⟶ `func_M ⟦a₁⟧ …` after A-normalisation. `[Spec]` methods are
callable in spec position and emit `Let_M.fst`; `[Lemma]` methods emit ghost calls.

**R6.7 (quantifiers).** `Pal.Forall((T i) => p)` ⟶ `forall (i: ⟦T⟧). ⟦p⟧`; likewise
`Pal.Exists`. `Pal.Implies(a, b)` ⟶ `⟦a⟧ ==> ⟦b⟧`. `Pal.Contents(a)` ⟶ the array's contents
existential, giving specs a `Seq` view.

---

## 7. Worked derivation

The inner loop of insertion sort, derived rule by rule. Note that nothing below is a
choice: each line cites the rule that produced it.

```csharp
while (j >= 0 && a[j] > key) {      // R5.6
    Pal.Invariant(-1 <= j && j < i);
    a[j + 1] = a[j];
    j--;
}
```

| Step | Rule |
|---|---|
| guard becomes a stateful block `let t = !var_j >= 0l; if (t) { let u = array_read var_a (Idx !var_j); u > !var_key } else { false }` | R6.3 + R6.1 + R6.5 |
| `invariant` gains `pts_to var_j _ ** pts_to var_key _ ** array_pts_to_full var_a _ _` | R5.8 |
| `invariant` gains `pure (-1 <= Int32.v !var_j /\ …)` | R5.6 |
| `decreases (Int32.v !var_j + 1)` — not a counted `for`, so **the user must supply `Pal.Decreases`**; absent it, translation fails with a diagnostic | R5.9 case 3 |
| body: `let t0 = array_read var_a (Idx !var_j); array_write var_a (Idx (!var_j + 1l)) t0;` | R6.2 |
| `j--` normalised to `j = j - 1`, then `var_j := !var_j - 1l;` | R5.3 |

The result is verbose and machine-shaped. That is the point: it is what the rules produce,
not what a Pulse programmer would write. If it fails to verify, Rule 3 says the fix is a
stronger annotation in the `.cs` file or a stronger general lemma in `Pulse.Lib.CSharp.*` —
never a change here that special-cases this loop.

---

## 8. Status

Rules are recorded here as they are validated.

* §1 facts **F1–F9** are verified against the pinned toolchain and regression-pinned in
  `test/pulse_facts`.
* **`test/probe_insertion_sort` was the first end-to-end validation of §2–§6.** Its
  `Func_InsertionSort.fst` and `Let_Sorted.fst` were produced by hand-executing the rules
  above on `InsertionSort.cs` — before any emitter code existed — and verify against
  `Pulse.Lib.CSharp.*`, proving length preservation and permutation. Every deviation the
  probe forced was recorded here (F6, F7, R3.3, R4.6, R5.8b, R5.9 case 2) or fixed in the
  library (`Pulse.Lib.CSharp.Seq.upd_shift_is_permutation`, `upd_same`); **none was fixed
  by special-casing the example**, and the probe's one *annotation* failure — the invariant
  `1 <= i && i <= a.Length`, false for an empty array — was fixed in the `.cs` file, which
  is exactly where §0 rule 3 says it belongs.
* **The emitter now implements R2–R6 and reproduces the probe from source.** Fourteen
  acceptance-test directories translate and verify from annotated C#: `swap`, `abs_max`,
  `out_param`, `spec_let`, `sum_array`, `reverse`, `insertion_sort`, `insertion_sort_sorted`,
  `binary_search`, `lemma_call`, `ghost_arg`, `pulse_interop`, `break_continue` and
  `compare_elements`.
* **Ill-formed C# stops at the C# level.** `Passes/Check.cs` is the standalone
  well-formedness validator PAL runs twice: it walks the whole IR after Normalize, reports
  and never rewrites, and covers the cross-node conditions no single lowering site can see
  (`PALCS05xx`, plus `PALCS09xx` warnings for `[Admit]` and `Pal.Assume`).
  `test/diagnostics` is its counterpart to the verification tests — twelve cases, each
  headed by the diagnostic it must produce, each required to exit non-zero, poison
  `TranslationErrors.fst`, and carry a span in the user's own file.
* **Insertion sort is fully verified** (plan tiers 7.1a *and* 7.1b, in a single method).
  `test/insertion_sort_sorted` proves, of the ordinary two-nested-loop C# insertion sort:

  ```
  Contents(a).Length == Old(Contents(a)).Length
  Sorted(Contents(a), 0, Contents(a).Length)
  IsPermutation(Contents(a), Old(Contents(a)))
  ```

  which is the full functional-correctness statement for a sort — the output is ordered
  *and* it is the input rearranged. Two techniques were needed, and both are recorded here
  because they generalise:

  1. **Spec predicates used in loop invariants must be total.** A `[Spec]` predicate
     carrying a `[Requires]` becomes a refinement on its last binder (R4.6), and that
     refinement must then be discharged wherever the predicate appears — including at
     invariant *establishment*, where the loop counter is often out of range (`i = 1` on an
     empty array). `Sorted`, `AllAbove` and `Dominated` therefore take no `[Requires]`; the
     index bounds are folded into the quantifier's antecedent, from which well-typedness of
     `s[i]` follows.
  2. **The proof is carried entirely by annotations in the `.cs` file** — four invariants
     naming the two intact runs either side of the hole, and four `Pal.Assert` steps
     restating them at the narrowed hole after the shift — plus one general library lemma
     (`Pulse.Lib.CSharp.Seq.upd_shift_is_permutation`) reached through a `[Lemma]` method.
     That is precisely the split §0 rule 3 mandates: **no emitter change was made for this
     proof.**
* **The contortion detector is running.** `abs_max`, `sum_array`, `reverse` and
  `insertion_sort` each ship a *variant*: the same contract and algorithm written
  differently — `for` against `while`, inverted branches, renamed and reordered locals,
  an exchanged guard, an index computed rather than carried, an inferred measure against a
  given one. All four verify with **no change to the translator**. `test/no-example-names.sh`
  additionally forbids any acceptance-test directory or method name from appearing anywhere
  in `Pal.Compiler`, and `test/provenance-lint.sh` (R2.2) requires every top-level
  construct in every generated module to trace to a C# span. `break_continue` and
  `compare_elements` ship variants too: six variant directories in all, none of which
  required a translator change.
* Every fix demanded by these tests landed where §0 rule 3 requires. `binary_search` needed
  three `Pal.Assert` steps and a measure that decreases on the iteration that finds the key
  — all in the `.cs` file. `sum_array` needed the `SumsFit` precondition and the
  `SumUpToStep` unfolding lemma — again in the `.cs` file. The only emitter changes were
  new *rules*: R4.7, R4.8 and R2.1's type qualification.

### Not yet done

* `struct` and `Span<T>`. A method mentioning either is rejected with a diagnostic rather
  than mistranslated, so `test/point_struct` and `test/circular_buffer` of the M1 suite are
  outstanding. `Struct_<n>.fst` generation and `[Refine]` are designed (§3) but unbuilt.
* Numeric conversions between machine-integer widths, and a non-tail `return` inside a
  loop: likewise rejected rather than mistranslated.
* A ghost argument determined only by the pure part of a contract cannot be passed at a
  call site (R4.5), because ghost arguments are resolved by unification and there is no
  zero-cost C# surface for explicit implicit application.
* **A postcondition cannot say why a loop stopped.** R5.10's break flag is internal to the
  translation, so an invariant cannot mention it, and a contract that needs "the loop ran
  to completion" is unstatable — see the note in `test/compare_elements`, whose `Equal`
  carries its exit condition in the guard for this reason. PAL's answer is a per-`break`
  `_ensures`, which is the intended fix; the C# surface for it would be a `Pal.Ensures(Q)`
  leading a `break`.
* `out` parameters are modelled exactly like `ref` — `pts_to` in both pre- and
  post-condition — rather than `pts_to_uninit` in the precondition. This is sound but
  demands more of the caller than C# does.
