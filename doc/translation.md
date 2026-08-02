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
| F13 | `preserves p` is a genuine `fn` spec clause, meaning exactly `requires p ensures p`, and it composes with `requires` and `ensures` on the same `fn`. | `test/pulse_facts/ObjectFacts.fst:count`, verified. Relied on by R4.11. |
| F14 | `Pulse.Lib.Box` is the **sound** heap cell and the right model of a CLR object. `Pulse.Lib.Reference.alloc` is marked `[@@deprecated "…is unsound; only use for model implementations"]` and may not appear in generated code; `Box.alloc` carries no such marker. `Box` additionally supplies `null`, a *pure* `is_null`, and `pts_to_not_null`, so a nullable object reference needs no new machinery. | `tools/fstar/lib/fstar/pulse/pulse/lib/Pulse.Lib.Reference.fsti:87` and `Pulse.Lib.Box.fsti:31-53,90-110`; `test/pulse_facts/ObjectFacts.fst:ownership_implies_non_null`, verified. Relied on by R3.8 and R3.11. |
| F15 | Pulse slprops are **affine**: `Box.free` exists but nothing compels a caller to reach it, and a leftover resource is discharged by `drop_`. So modelling a garbage-collected heap needs **no axiom at all** — allocate, never free. | `test/pulse_facts/ObjectFacts.fst:alloc_without_free`, verified: it allocates an array and a box, returns, and frees neither. Relied on by R3.12. |
| F16 | An object resource is linear, so passing the same object to two owned parameters is **unprovable**, reported as a bare `Error 228: Cannot prove: class_C__inv a _`. Aliasing is thus safe but incomprehensible, which is why R3.13 requires the emitter to diagnose it first. | `test/pulse_facts/ObjectFacts.fst:aliasing_is_unprovable` documents the rejected call; the failure was reproduced against the pinned toolchain. |
| F18 | F15's affinity is a **permission to discard, not an automatic discard**. A method that allocates an object and does not return it still holds the invariant when it ends: `Error 228: Leftover resources: class_C__inv x _`. Writing the discard needs a name for the model the context holds — an existential witness the emitter never chose — which `with m. assert p;` binds. | `test/pulse_facts/ObjectFacts.fst:allocate_and_discard`, verified; the failure was reproduced by `test/counter_client`'s `FreshIsZero` before R4.14 existed. Relied on by R4.14. |
| F17 | A fact about the **model alone** is visible to a caller only if it lives in the model type as a *refinement*. Placed instead inside the object invariant it is unreachable: a caller holding `class_C__inv this m` cannot derive it without unfolding, and F* reports `Error 19` at the postcondition. | `test/pulse_facts/ObjectFacts.fst:client_sees_model_invariant`, verified; weakening `model_StackModel__pred` to `True` reproduces the `Error 19`. Relied on by R3.9d. |

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

### 3.4 Classes

**Status: implemented.** Every rule below was written before the emitter, per §0, and every
shape is pinned by `test/pulse_facts/ObjectFacts.fst`, which verifies against the pinned
toolchain. `test/counter_class`, `test/counter_client` and `test/stack_class` are the
acceptance tests.

A class is the construct M1 could not express at all. R3.4 forbids a struct field of
reference type (PALCS0511) because copying the struct would duplicate ownership, which is
why `test/circular_buffer` has to pass its storage array *alongside* the struct that
describes it. A class is a heap cell rather than a value, so it can own its array outright.

**R3.7 (class representation).** A `sealed class C` emits a record of its fields, using the
same `fld_` prefix and the same access and update rules as a struct (R3.5, R3.6):

```fstar
noeq type class_C__raw = { fld_f₁: T₁; … }
```

Unlike R3.4, a field of reference type is **allowed** here, and is the point of the whole
construct.

**R3.8 (class reference type).** `C` is translated to `Pulse.Lib.Box.box class_C__raw`.

`Box` and not `Pulse.Lib.Reference.ref`: `Reference.alloc` carries
`[@@deprecated "Reference.alloc is unsound; only use for model implementations"]` and may
not appear in generated code, whereas `Box.alloc` is an ordinary specified operation
(F14).

**R3.9 (object model).** Each class has a **pure ghost model type**, and the invariant's
job is to relate the implementation type to it.

The model type is **declared by the user**, not derived by the emitter. It is whatever type
the class's `[Model]` member returns — a `Seq<T>`, or a spec-only struct — so it may be a
type the user already has a theory about, and pure lemmas about the model can be stated and
proved without mentioning the implementation at all. The emitter names it `model_M` after
that type; it never invents one.

The one constraint is that the model must expose everything a **caller** needs, both to
establish a precondition and to exploit a postcondition. This is a real constraint, not
bookkeeping: modelling a bounded stack by its element sequence alone leaves capacity trapped
inside the invariant's existential, so a client could not state "the stack is not full" and
`Push` would be uncallable. That stack's model is `{ elems: Seq.seq T; capacity: nat }`.

**R3.9a (spec-only structs).** `[Spec]` on a `struct` declaration makes it a *spec-only
type*: it is erased, it never appears in executable code, and — unlike an ordinary struct
(R3.4) — its fields may be spec-only types such as `Seq<T>` and `SpecInt`. It may still not
own a resource: an array or class-typed field is PALCS0511 here as it is there, because a
ghost value cannot be an owner either.

This is a new requirement that R3.9 forces, not a convenience. The built-in spec-only types
of §8 are all atomic, so without a way to *declare* one there is no way to write a model
that is a product — and a bounded container's model is exactly a product of its contents
and its capacity. `[Spec]` is reused rather than a new attribute introduced because it
already means "exists only in specifications" on a method, and this is the same meaning on
a type.

**R3.9b (the abstraction relation is inlined, bounds first).** The relation between
representation and model is a **conjunct inside the invariant**, not a separate
`abs : raw → model` function.

This is forced rather than stylistic. The abstraction is *partial*: for the stack,
`Seq.slice contents 0 (I32.v top)` is well-typed only once `0 <= I32.v top <= Seq.length contents`
is known. Factoring it out as a total function would mean refining its arguments, and that
refinement would then have to be discharged at **every** use of the model — the identical
trap R4.6 and `test/insertion_sort_sorted` already recorded for `[Spec]` predicates
carrying a `[Requires]`. Inlining costs nothing, because `p₁ /\ p₂` type-checks `p₂` with
`p₁` in scope, so the bounds conjuncts make the partial operation well-typed exactly where
it appears. **Conjunct order is load-bearing**, as it already is for `[Ensures]`.

**R3.9c (`[Spec]` members are functions of the model).** A `[Spec]` member of a class
translates to a pure function of `model_M`, never of `class_C__raw`.

This is what makes `[Requires("Count < Capacity")]` mean anything to a caller: the caller
holds `class_C__inv this m` and nothing else, so every observation a contract mentions must
be computable from `m` alone. A `[Spec]` member whose body reads a field directly is
**PALCS0523**, and its message is "widen the model" — which delivers the diagnosis for the
too-weak-model problem at the *declaration*, rather than as an unprovable call site much
later. The `[Model]` member is the sole exception: reading the fields is precisely its job.

**R3.9d (where a fact goes: `[Invariant]` or `[Refine]`).** The invariant's abstraction
conjunct (R3.9b) is what connects the memory-resident fields to the model, and it is
**mandatory** — it is derived from `[Model]`, and the user does not choose whether to have
it. There is no decision there. What *is* a decision is where each **additional** fact goes,
and it is settled by what the fact mentions:

| The fact mentions | It goes in | Because |
|---|---|---|
| fields (`0 <= top`, `top <= items.Length`) | `[Invariant]` on the class | it is temporarily false between two field writes, so it needs the `unfold`/`fold` window of R4.10 |
| only the model (`Count <= Capacity`) | `[Refine]`, on the `[Model]` member or on the model type | it is a property of a pure ghost value, so it is never breakable — and a caller can only ever see it there |

The second row is not a preference; it is forced by **F17**. A caller holds
`class_C__inv this m` and nothing else. A model-level fact sitting inside that predicate
cannot be reached without unfolding — and once R3.9's deferred `.fsti` step makes the
predicate opaque, cannot be reached at all. Stated as a refinement it travels in the *type*
of `m`, so it arrives with the model, everywhere, for free. This is pinned in both probes:
weakening the model predicate turns `client_sees_model_invariant` (`test/pulse_facts`) and
`func_CounterClient_ValueIsNonNegative` (`test/objects_probe`) from verified into `Error 19`,
while every other module in the probe keeps verifying — which is the precise statement that
the fact is *unreachable to callers*, not merely absent.

So each class emits a **refined model type**, in R3.5's shape verbatim:

```fstar
let class_C__model__pred (m: <the [Model] member's return type>) : prop = <the [Refine] clauses>
type class_C__model = m: <the [Model] member's return type> { class_C__model__pred m }
```

and `class_C__inv` is indexed by `class_C__model`. Three details are deliberate.

* It is emitted **unconditionally**, with the predicate `True` when there are no clauses —
  the same reason `struct_S__pred` is emitted when trivial (§0 rule 2).
* It is named after the **class**, not after the model type. This is what lets an *atomic*
  model such as `SpecInt` or `Seq<int>` carry a refinement at all: there is no user-declared
  struct to put one on. Naming it after the model type would also collide whenever two
  classes share one. Verified for the atomic case by `test/objects_probe`.
* It **composes with**, rather than replaces, R3.5. When the model is a `[Spec]` struct, a
  fact intrinsic to the type is better placed on the struct itself, where it is simply an
  ordinary struct refinement and is shared by everything using that model; `[Refine]` on
  `[Model]` is for a fact this *class* guarantees. Both shapes are verified — the struct form
  by `test/pulse_facts/ObjectFacts.fst`, the member form by `test/objects_probe`.

In a `[Refine]` on the `[Model]` member the model value is named `Result`, as it is in an
`[Ensures]`; in a `[Refine]` on a struct, fields are named directly, as R3.5 already
specifies.

The obligation this creates is discharged where it belongs: at the `fold` of R4.11a, the
emitter must show the model it constructs from the post-state satisfies the refinement. That
is a real proof obligation, and it is what ties the two kinds of fact together — the
representation-level `[Invariant]` is exactly what makes the model-level `[Refine]` provable.

Consequently an `[Invariant]` clause that mentions no field — only `[Spec]` observations — is
**PALCS0527**, advising that it move to the model. This is the same shape of diagnosis as
PALCS0523: a specification-strength mistake reported at the declaration, rather than as an
unprovable call site much later.

**R3.10 (object invariant).** Each class emits
```fstar
let class_C__inv (this: class_C) (m: model_M) : slprop =
  exists* (r: class_C__raw) … .
    B.pts_to this r ** <the resource of each reference-typed field> **
    pure (<bounds> /\ <the model agrees with the representation> /\ <the [Invariant] clauses>)
```

Two properties of this shape are load-bearing.

* **The invariant is indexed by the model, and must be.** With an un-indexed
  `inv (x: C) : slprop`, the object's entire state sits under an existential, so a
  postcondition can mention arguments and nothing else — `Count(this) == Old(Count(this)) + 1`
  would be inexpressible, and every method spec would degrade to "the object is still well
  formed". That is memory safety, not functional correctness, and it is exactly the
  weak-specification failure this project exists to avoid. The index is what makes
  functional correctness statable. Note that this is not a new idea here: `A.pts_to var_a s`
  is already a model-indexed resource, and R4.10 threads a class's model exactly as R4.4
  already threads an array's.
* **A class invariant is a `pure` conjunct inside the predicate, not a `[Refine]`.** A
  refinement type must hold of *every* value of the type, but R3.6 writes a whole record
  per field assignment, so a method that transiently breaks its invariant between two field
  writes would be rejected outright. Struct refinements are always true; class invariants
  are temporarily breakable, and the fold/unfold discipline of R4.10 is what marks the
  window in which they may be broken. Using one mechanism for both would be wrong. This
  concerns the **representation** only; a fact about the model alone must go the other way,
  as a refinement on the model type, for the reason R3.9d and F17 give.

**R3.10a (a class owns its arrays).** For each field of array type, the invariant gains an
existential for its contents, an `A.pts_to` conjunct, and a length bound:

```fstar
let class_C__inv (this: class_C) (m: class_C__model) : slprop =
  exists* (r: class_C__raw) (contents_f: Seq.seq ⟦T⟧).
    B.pts_to this r **
    A.pts_to r.fld_f contents_f **
    pure (Seq.length contents_f <= 2147483647 /\ … )
```

This is the rule R3.4 could not have. A struct is a value, so a field owning a resource
would make every copy a second owner (PALCS0511) — which is why `test/circular_buffer` has
to pass its storage *alongside* the struct describing it, leaving the two connected only
by a convention the type system does not enforce. A class is a heap cell with identity, so
there is exactly one owner and the array can go inside. The consequence is that the
storage becomes genuinely private: a client never names it and, by F16's linearity, cannot
alias it.

Three details are forced.

* **The field name denotes the *contents* in every specification, and the reference only in
  the `A.pts_to`.** `items.Length` is `Seq.length contents_items` and `Pal.Contents(items)`
  is `contents_items`, so a class-level clause reads exactly as a method contract about an
  array parameter already does (R4.4). Nothing new has to be learned to write one.
* **The length bound is emitted for every array field.** It is a fact about the C# type —
  an array's length is an `int` — and not an assumption: it enters at `new T[n]`, whose
  argument is already an `int`, and is re-proved at every fold from there. It is stated
  first because it is what makes arithmetic on an index into the array provably
  non-overflowing: `top < items.Length` bounds `top + 1` only once `items.Length` is known
  to be bounded.
* **A field of *class* type remains PALCS0531.** The difference from an array is not effort.
  An array's resource is a `pts_to`, which has no window of its own; another object's is an
  abstraction with its own `unfold`/`fold` discipline, so nesting it raises a question the
  scheme does not answer — when may the outer object open the inner one? Refusing it is
  the honest outcome until that is written down.

The obligation this creates lands at the `fold` of R4.11a, and needs one extra device
there. After a method has written into the array, the contents the `unfold` produced are
stale, and the emitter never named the new ones. `with c. assert (A.pts_to …f c);` binds
them — the same device R4.14 needs, for the same reason.

**R3.11 (null).** `Box` already models a nullable CLR reference, so `null` needs no new
machinery: `Box.null` is `null`, `Box.is_null` is a *pure* boolean (so it may appear in a
contract), and `Box.pts_to_not_null` proves that a live object is non-null.

That last one settles the design. Ownership *implies* non-nullness, so a method holding
`class_C__inv this m` never has to test for null and R6.4's "no null dereference"
obligation is discharged by the invariant rather than by a check. `C?` maps to `box` with
no additional obligation; `C` maps to `box` together with a `pure (not (is_null x))`
conjunct that `pts_to_not_null` supplies for free.

**R3.12 (allocation and the garbage collector).** `new C(…)` emits `Box.alloc`, and the
emitter **never** emits `Box.free`.

This needs no MODELING AXIOM, unlike the array case. Pulse slprops are affine: `Box.free`
exists but nothing compels a caller to reach it, and a leftover resource is discharged by
`drop_` (F15). An object whose invariant is simply dropped *is* a garbage-collected object.
Contrast `Pulse.Lib.CSharp.Array.alloc`, which did need an axiom, because the underlying
`Pulse.Lib.Array.alloc` is a stack allocation that must not outlive its frame. The CLR
being garbage collected is thus a genuine simplification over PAL's C, not merely a
different set of obligations.

**R3.13 (aliasing).** An object resource is linear, so two owned parameters are necessarily
distinct objects. Aliasing is therefore not unsound — it is *unprovable*.

That is the correct outcome, but F* reports it as a bare `Cannot prove: class_C__inv a _`,
which means nothing to a C# programmer who has just written `Merge(s, s)`. The emitter must
therefore detect a call passing syntactically equal object arguments to two owned
parameters and reject it as **PALCS0520** with an explanatory message. This is a
diagnostic, not a proof step, so it does not violate §0 rule 3.

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

### 4.5 Instance methods

**Status: specified, not yet implemented**, alongside §3.4.

**R4.10 (instance method).** An instance method of `sealed class C` translates exactly as
R4.1 does, with three additions. The receiver becomes a leading explicit binder `this`, the
model becomes a leading *erased* implicit binder, and the object resource brackets the
contract:

```csharp
[Requires(P)] [Ensures(Q)]
public void M(T x) { … }
```
⟶
```
fn method_C_M (this: class_C) (var_x: ⟦T⟧) (#m: erased model_M)
  requires class_C__inv this m ** pure ⟦P⟧
  ensures  exists* m'. class_C__inv this m' ** pure ⟦Q⟧
{ unfold class_C__inv this m;  ⟦body⟧;  fold class_C__inv this <the new model>; }
```

The postcondition **existentially quantifies the new model** `m'` and constrains it with
the user's `[Ensures]` clauses, read over `m'` and `m`. It does *not* name the new model as
an emitter-computed function of the old one: there is no way to compute a model transformer
in general, and inventing one would be exactly the proof step §0 rule 3 forbids. This is
also the shape arrays already use — `ensures exists* post_a. A.pts_to var_a post_a ** pure (…)`
— so a class's model is threaded precisely as an array's is (R4.4), and `Old` needs no new
machinery: inside ⟦Q⟧ an observation reads as `spec_C_Obs m'`, and `Old(observation)` as
`spec_C_Obs m`.

**R4.10a (the receiver is spelled `@this`).** A contract on an instance member names the
receiver `@this`, as in `[Requires("@this.Count < @this.Capacity")]`.

This is forced by the shim mechanism (§4 of `internals.md`), and both halves were checked
against Roslyn rather than assumed:

* A spec string is compiled as the body of a **static** method, so a bare `this` is
  `CS0026: Keyword 'this' is not valid in a static property, static method, or static
  field initializer`. The receiver must be an ordinary parameter.
* `ShimParameters` already renders every parameter with an `@` prefix, so a parameter
  *named* `this` renders as the verbatim identifier `@this`, which is legal C# and binds.
  Nothing in the shim machinery changes.

`CS0026` inside a spec string is therefore remapped to **PALCS0526**, whose message is
"write `@this`" — the one error every user will hit once.

**R4.10b (a contract may only name accessible members).** The shim lives in
`namespace __PalSpecShims`, so a contract can reference only `public` or `internal` members
of the class: `@this.Priv` on a private member is `CS0122`, remapped to **PALCS0525**.

A `[Spec]` member intended for use in contracts must accordingly be at least `internal`.
`[Model]` is exempt and may be `private`, because it is consumed only by R3.10's invariant,
which the emitter builds from the member's *body* — inside the class, where private fields
are visible. That asymmetry is the point: the abstraction function sees the representation,
and nothing else does.

The `unfold`/`fold` bracket is the window in which R3.10's invariant may be broken. It is
emitted unconditionally, for the same reason `struct_S__pred` is emitted even when trivial
(§0 rule 2).

**R4.11 (read-only method).** When a method assigns no field and passes `this` to no
mutating method, R4.10's two clauses collapse to one:

```
preserves class_C__inv this m
```

`preserves p` is a real Pulse spec clause meaning exactly `requires p ensures p`, and it
composes with `requires`/`ensures` (F13). This is a *specification-strength* rule, not an
optimisation, and it is the read-only case that needs it. Under R4.10's existential form a
read-only method says only "*some* model holds afterwards"; the caller loses the fact that
the object is unchanged unless the user writes `[Ensures("@this.X == Old(@this.X)")]` for
every observation. `preserves` states it once, for all of them. The distinction is decided
by the existing write-set analysis (Normalize), not by a heuristic.

**R4.11a (fold witness).** R4.10's closing `fold` must name the model it re-establishes,
and the term to name follows from the same write-set split:

| Method shape | `ensures` clause | `fold class_C__inv this …` at |
|---|---|---|
| assigns no field (R4.11) | `preserves class_C__inv this m` | `m` — the pre-state model binder |
| assigns a field (R4.10) | `exists* m'. class_C__inv this m' ** …` | ⟦*body of* `[Model]`⟧, evaluated at the post-state |

Each is forced, and neither is a search. In the read-only case the representation is
untouched, so `m` is still a correct index and is the *only* term that discharges
`preserves` — refolding at a recomputed model fails with `Error 228: Cannot prove:
class_C__inv this m`, because reconciling two indices is a matching problem the prover does
not hand to the SMT solver. In the mutating case `m` is stale and the new model is not yet
named by anything, so the emitter re-reads the representation and applies the abstraction:
this is not an invented proof step but the *definition* of the model, the one the user
supplied in `[Model]` (R3.9), transcribed at a second program point.

Both branches, with the constructor and the class module, are hand-executed and verified in
`test/objects_probe/`.

**R4.12 (constructor).** `new C(args)` emits a function that allocates, establishes the
invariant, and returns the object:

```
fn ctor_C (…args…)
  requires pure ⟦P⟧
  returns  x : class_C
  ensures  exists* m. class_C__inv x m ** pure ⟦Q⟧
```

The postcondition **constrains the initial model** through the constructor's `[Ensures]`,
in the same existential form as R4.10. `ensures class_C__inv x m` alone — for some
unconstrained `m` — would say the object is well formed without saying what it holds, which
is R3.10's weak-specification failure relocated to the constructor. A constructor with no
`[Ensures]` is therefore a warning (`PALCS0903`): it is legal, and almost never what was
meant.

Freshness is free and needs no emitter work: the frame rule gives every caller
`frame ** class_C__inv x m₀`, so a newly constructed object is automatically separate from
everything that already existed.

**R4.14 (the garbage collector).** An object whose reference does not leave the method is
**dropped at every exit**:

```
with m. assert (Class_C.class_C__inv var_x m);
drop_ (Class_C.class_C__inv var_x m);
```

This is where the CLR's collector enters the translation. F15 says the resource *may* be
discarded; F18 says the discard must nonetheless be *written*, and that writing it needs a
name for a model the emitter never chose — hence the `with`. A returned object is exempt:
its invariant is in the postcondition.

A returned object also keeps the binder its callee produced it under. Pulse matches
resources syntactically, so `let var_c = t0` leaves the context holding `inv t0 _` while
the postcondition asks for `inv var_c _`, and the frame rule cannot bridge the two even
though the equality is trivially true (`Error 228`). The emitter therefore emits a call
that initialises an object local *into that local's binder* rather than into a temporary
the local then aliases.

**R4.13 (rejections).** M2 supports `sealed` classes only. `virtual`, `abstract`,
`override`, and interface implementations are **PALCS0521**: a per-class `class_C__inv`
cannot express behavioural subtyping without existential packages, and admitting them
without one would silently produce unsound or unprovable specs. A **static mutable field**
is **PALCS0522** — it is unowned global mutable state, which no per-object invariant
covers. A `[Spec]` member that reads a field directly is **PALCS0523** (R3.9c), and a class
with no `[Model]` member is **PALCS0524**: without one there is no model, and without a
model every method spec collapses to memory safety.

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

A quantifier binder is bound *outside* both program states, so it is in scope on both
sides of `Old`: under `forall (int k)`, `Old(a[k])` reads the pre-state array at the
same `k` the postcondition speaks of. Emit therefore extends the pre-state scope with
the binder as well as the current one.

**R6.8 (projection receivers).** `⟦e.f⟧ = ⟦e⟧′.Struct_S.fld_f`, where `⟦e⟧′` is `⟦e⟧`
parenthesised unless it is already atomic. This is not cosmetic: `!var_s.M.fld` parses in
Pulse as `!(var_s.M.fld)`, a dereference of a projection *out of* a reference, which is
not what C#'s `s.f` on a `ref` parameter means.

**R6.9 (mathematical `[Spec]` results).** R4.6 makes a `[Spec]` method's integer
*parameters* mathematical; its integer *result* is mathematical for the same reason. A
`[Spec] int` emits `: int` with a mathematical body, and an application of it denotes a
mathematical value — so it composes with arithmetic and may be used as an array index. A
`[Spec] bool` emits `: prop`. Nothing else about the two cases differs.

**R6.10 (by-reference arguments).** A `ref`/`out`/`in` argument passes the *cell*, not its
contents:

```csharp
Enqueue(a, ref s, value);
```
⟶
```
let t0 = !var_value;
let t1 = func_Enqueue var_a var_s t0;
```

`var_s` is passed unchanged, so the callee's `requires R.pts_to var_s _` is satisfied by
the caller's ownership of the same cell and the write the callee performs is visible after
the call. Passing anything other than a cell — a temporary, a field, an array element — is
**PALCS0402**; C# does not permit it either.

Two consequences the write-set analysis (R5.4) must respect: a call may write through
*every* by-reference argument and through *every* array argument, so all of those names
must be existentially quantified in an enclosing loop's invariant. Missing one does not
produce an unsound proof — it produces an invariant asserting the call changed nothing,
which simply fails to re-establish.

**R6.11 (array allocation).** `new T[n]` ⟶ `alloc ⟦n⟧ ⟦default(T)⟧`, using
`Pulse.Lib.CSharp.Array.alloc`.

Two things are being read off the CLR rather than off Pulse. The allocation always
succeeds and imposes no deallocation obligation, which is why `Pulse.Lib.Array.alloc` —
a *stack* allocation that must not outlive its frame — is not what is called; and the
result is zero-filled, which is why the initial contents are `Seq.create (v n) 0` and no
initialisation loop is emitted. Both live in the one MODELING AXIOM inside
`Pulse.Lib.CSharp.Array.alloc`, where they can be read, rather than being spread across the
emitter.

An explicit initialiser list, `new[] { 1, 2, 3 }`, is refused. It is an initialisation
loop written as an expression, and unrolling it would put writes into the translation that
no C# statement corresponds to, with nowhere to attach a specification between them.

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

* §1 facts **F1–F18** are verified against the pinned toolchain and
  regression-pinned in `test/pulse_facts`. F13–F16 were established by probing
  Pulse *before* §3.4 and §4.5 were written, which is the order §0 requires.
* **`test/objects_probe` is the scheme-adequacy probe for §3.4 and §4.5**, and stands to
  the class emitter as `test/probe_insertion_sort` stood to the M1 emitter. Its
  `Class_Counter.fst`, `Func_Counter__ctor.fst`, `Func_Counter_Increment.fst` and
  `Func_Counter_Get.fst` were produced by hand-executing R3.7–R3.13 and R4.10–R4.12 on
  `Counter.cs`, before any class-emitting code existed, and all four verify. The probe
  forced exactly one addition — **R4.11a**, the fold witness: refolding a read-only method's
  invariant at a *recomputed* model fails with `Error 228: Cannot prove: class_C__inv this
  m`, so the read-only branch must refold at the pre-state binder `m`. It also settled two
  spellings the emitter must use: box access is written `B.op_Bang` / `B.op_Colon_Equals`
  rather than `!` / `:=`, so that a method holding both a box receiver and `let mut` locals
  has no operator ambiguity; and a field of another module's record is projected and updated
  qualified (`t.Class_C.fld_x`, `{ t with Class_C.fld_x = … }`), as F10 already required for
  structs.
* **`test/probe_insertion_sort` was the first end-to-end validation of §2–§6.** Its
  `Func_InsertionSort.fst` and `Let_Sorted.fst` were produced by hand-executing the rules
  above on `InsertionSort.cs` — before any emitter code existed — and verify against
  `Pulse.Lib.CSharp.*`, proving length preservation and permutation. Every deviation the
  probe forced was recorded here (F6, F7, R3.3, R4.6, R5.8b, R5.9 case 2) or fixed in the
  library (`Pulse.Lib.CSharp.Seq.upd_shift_is_permutation`, `upd_same`); **none was fixed
  by special-casing the example**, and the probe's one *annotation* failure — the invariant
  `1 <= i && i <= a.Length`, false for an empty array — was fixed in the `.cs` file, which
  is exactly where §0 rule 3 says it belongs.
* **A class owns its array** (R3.10a, R3.9a, R6.11). `test/stack_class` is the test M1
  could not have written: a `Stack` whose `int[]` lives *inside* its invariant, so the
  storage is unreachable to a client and cannot be aliased. It needed three rules and no
  special cases. R3.9a makes `[Spec]` on a `struct` declare a spec-only type, which R3.9
  forces — a bounded container's model is a product of contents and capacity, and every
  built-in ghost type is atomic. R3.10a puts the array's `A.pts_to` in the invariant and
  binds the field name to its *contents* in every specification, so a class-level clause
  reads exactly as an array parameter's contract does. R6.11 translates `new T[n]`.

  The specifications are functional, not structural: `Push` and `Pop` each fix the new
  contents element by element and relate them to the old, and the model refinement
  `Elems.Length <= Capacity` is what makes "there is room" statable by a caller who cannot
  see inside. Sixteen modules verify, including a client that allocates a stack, uses it
  and drops it, and `PileVariant.cs` — the same class with its members in the opposite
  order, different field names, `this.` written out and `++`/`--` in place of assignment —
  whose output is identical modulo those names and the declaration order they induce.
* **The class emitter implements R3.7–R3.13 and R4.10–R4.14, and reproduces
  `test/objects_probe` from source.** `test/counter_class` translates `Counter.cs` — the
  probe's own source — and all five generated modules verify: the class module, the
  constructor, the mutator, the read-only method and the client that observes F17. The
  emitted output agrees with the hand-derived probe construct for construct.
  `test/counter_client` covers the other half — using an object from outside it, where
  the invariant is never unfolded and everything the caller knows comes from a `[Spec]`
  member applied to the model. It forced two rules. **R4.11's caller side**: a call to a
  mutator makes the receiver's post-state model an existential, so read-only-ness is
  computed for *callees* too, from the same syntactic test that decides it for the method
  in hand. **R4.14**, the garbage collector: an object that is allocated and not returned
  must be explicitly dropped, which F18 pins.

  Two emitter constraints fell out of the same test, both consequences of Pulse matching
  resources syntactically. An object local is initialised *into its own binder* rather
  than aliasing a temporary, and only the *receiver* of a class's own methods is unfolded
  — an object that merely passes through must stay folded, because every function taking
  it expects its invariant and not its representation.

  `TallyVariant.cs` is the §7.2 variant detector for objects: the same class with the
  field renamed, `this.` written out, `++` in place of `x = x + 1`, an expression-bodied
  reader and the members declared in reverse order. It produces output **byte-identical**
  to `Counter.cs`'s modulo the names, with no emitter change — the strongest evidence
  available that the class rules are compositional rather than fitted to one example.
* **The transiently broken invariant is exercised.** `test/interval_class`'s `Shift`
  writes `lo` and then `hi`; between the two the object is a well-formed
  `class_Interval__raw` whose `lo <= hi` is false. R3.10's choice of a `pure` conjunct over
  a refinement is what admits it — a refinement would have to hold of that intermediate
  record, and R3.6 writes a whole record per assignment, so there is no way to write both
  fields at once and dodge the question. The intermediate state is visible in the output as
  two `B.op_Colon_Equals` with no `fold` between them.
* **R3.13 is enforced** (`PALCS0520`). A call passing one object — or one non-`[Frac]`
  array — to two owned parameters is refused before it is emitted, with the reason. It is
  a diagnostic and not a proof step: the translation of the call is unchanged. `Bank.Transfer`
  in `test/account_class` is the shape it protects, and `test/diagnostics` the misuse.
* **Conservation across two objects verifies.** `test/account_class` proves
  `from.Balance + to.Balance` is unchanged by a transfer. Nothing asserts that the two
  accounts are distinct or that the second call left the first alone; separation supplies
  both, and the property is statable at all only because each object carries its own model
  binder (R3.10).
* **R3.9d is mechanically enforced.** `PALCS0527` refuses an `[Invariant]` clause that
  mentions no field. Such a clause is a fact about the model alone, and F17 shows it is
  unreachable from inside the invariant: it verifies where it is written and fails much
  later, in an unrelated client file. `test/diagnostics/cases/ModelFactInInvariant.cs`
  pins it. `PALCS0524` likewise refuses a class that carries contracts but declares no
  `[Model]`, rather than letting its members fall through to the generic `PALCS0530`.
* **The emitter implements R2–R6 and reproduces the probe from source.** The whole M1
  acceptance suite translates and verifies from annotated C#: `swap`, `abs_max`,
  `out_param`, `spec_let`, `sum_array`, `reverse`, `insertion_sort`, `insertion_sort_sorted`,
  `binary_search`, `lemma_call`, `ghost_arg`, `pulse_interop`, `break_continue`,
  `compare_elements`, `point_struct` and `circular_buffer`.
* **Ill-formed C# stops at the C# level.** `Passes/Check.cs` is the standalone
  well-formedness validator PAL runs twice: it walks the whole IR after Normalize, reports
  and never rewrites, and covers the cross-node conditions no single lowering site can see
  (`PALCS05xx`, plus `PALCS09xx` warnings for `[Admit]` and `Pal.Assume`).
  `test/diagnostics` is its counterpart to the verification tests — nineteen cases, each
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

* **Structs closed the suite, and cost four rules rather than four special cases.**
  `test/circular_buffer` was the last acceptance test, and every failure it produced was
  either a missing *rule* or a missing *annotation* — never an example-shaped patch:
  R6.7's `Old`-under-a-binder scope, R6.8's receiver parenthesisation, R6.9's mathematical
  `[Spec]` results and R6.10's by-reference arguments are all stated context-free above and
  apply to every program. Everything else went into the `.cs` file: the pure `At` model the
  executable `Wrap` is tied to (a specification may only call `[Spec]`/`[Lemma]` methods,
  never executable ones), the `capacity <= 2^30 - 1` bound that makes `Head + Count`
  provably non-overflowing, and the explicit `a.Length == Old(a.Length)` a quantified
  frame condition needs.

### Not yet done

* `Span<T>` and `ReadOnlySpan<T>`. A method mentioning either is rejected with a diagnostic
  rather than mistranslated; fractional permissions are reached through `[Frac]` instead
  (R4.9).
* A struct field must be a value — a scalar or another translated struct. An array or
  class field is **PALCS0511**, and that is the model rather than a shortcut: a struct
  copy would duplicate ownership of the same memory. Storage therefore travels alongside
  the state it describes, as in `test/circular_buffer`. A *class* has no such restriction
  (R3.10a), so `test/stack_class` is what `test/circular_buffer` wanted to be.
* Generics, interfaces, `string`, and `float`/`double` remain unspecified as well as
  unimplemented. Classes are implemented; what is still missing inside §3.4 is a class
  field of *class* type (R3.10a, PALCS0531) — the array case is done.
* **Object abstraction is deliberately deferred.** `class_C__inv` is specified as a
  *concrete* definition in the class's own module. Hiding it behind an `.fsti`
  (`val class_C : Type0`, `val class_C__inv : class_C -> model_M -> slprop`) works
  and needs no F\* `friend`, but it requires a module shape the emitter does not have
  today, and C# `private` already hides the representation at the source level. The step is
  available when proof performance or genuine information hiding demands it.
* **A loop inside an instance method is refused** (`PALCS0001`). R4.10's bracket is open
  across the whole body, so the loop sits where the invariant does not hold, and R5.8's
  loop rule would have to carry the *representation* — `B.pts_to this r`, one `A.pts_to`
  per array field, `r` and the contents existentially quantified — with the user's
  `Pal.Invariant` clauses read against the fields rather than the model. That is a
  sub-scheme and it is not written; emitting the folded invariant instead produces Pulse
  that cannot verify and whose failure points at generated code. The workaround is the one
  M1 already supports: put the loop in a static method taking the array. This is the
  largest single gap in §3.4.
* **Object lifecycle and re-entrancy are unspecified.** A class with two-phase
  initialisation or `Dispose` wants a *state*-indexed invariant, and calling a method on
  `this` while its invariant is unfolded (R4.10) requires either re-establishing the
  invariant first or a marked helper that operates on the unfolded state. Neither is
  designed; R4.13's `sealed`-only restriction keeps them out of scope for now.
* **Reference identity** — `ReferenceEquals`, and `==` on a class — has no story. `Box`
  supports equality, but nothing relates it to the ownership discipline.* Numeric conversions between machine-integer widths, and a non-tail `return` inside a
  loop: likewise rejected rather than mistranslated.
* `out` is modelled exactly as `ref`, not as `pts_to_uninit` strengthening to `pts_to`, so
  a caller must initialise an `out` argument before the call.
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
