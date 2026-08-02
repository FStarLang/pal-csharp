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

The rule reads in both directions, and the second one is easier to forget: **the frontend
never invents a refusal.** pal-csharp refuses what it cannot *translate* — a construct with
no image in Pulse, a measure it would have to guess, a field with no ownership story. What
cannot be *proved* is the prover's to say. A check that inspects a program and predicts the
proof will fail is doing separation logic in a pass that does not have it, and will
therefore be a silhouette of the rule rather than the rule: it fires on the shapes it was
written for and misses the rest. It also costs more than it looks, because a refusal hides
everything behind it — a program refused in the frontend is never emitted, so nothing else
wrong with it is ever discovered. R3.13 is the worked example; `test/pulse_refusals` is
where programs that translate faithfully and fail honestly are kept.

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
| F20 | An object's invariant may **contain** another's, and nesting needs no new device: the outer invariant existentially quantifies the sub-object's *model* exactly as R3.10a quantifies an array's *contents*. Inside the outer `unfold` window the sub-object stays **folded**, so calling its methods is an ordinary call. The closing `fold` must re-name the sub-models where it happens, because a call may have moved one. A bound on a sub-model reaches a call site only as a **refinement on the model type** — F17 again, and not optional: as a `pure` conjunct inside the sub-invariant it is behind a folded slprop and does not reach. | `test/pulse_facts/ObjectFacts.fst:ranked_mk`, `ranked_bump_left`, verified. Relied on by R3.10b. |
| F21 | An slprop `let` may take a **meta-argument-defaulted** permission binder, as `Box.pts_to` does: `let inv (this: C) (#[T.exact (`1.0R)] p: perm) (m: M) : slprop`. `inv x m` then *means* `inv x #1.0R m`. So indexing every class invariant by a permission changes no existing emission — full ownership stays what you get by not asking. | `test/pulse_facts/ObjectFacts.fst:frac__inv`, `frac_default_is_full`, verified. Relied on by R3.10c. |
| F22 | A per-class `share` is provable from `Box.share`, `Array.share` and each sub-object's own `share`. Each closing `fold` **must** be preceded by an `assert` naming the resources it consumes: the invariant's existentials are solved by matching against the context, and after a share the context holds two candidates for every one of them. | `test/pulse_facts/ObjectFacts.fst:frac__inv_share`, `frac_outer__inv_share`, verified. Relied on by R3.10d. |
| F23 | A per-class `gather` proves the two models **equal**. Not an extra hypothesis and not a choice: R3.9's invariant pins `m` to the abstraction function of the representation, `Box.gather` proves the two representations equal, and a function of equal arguments is equal. Two read-only aliases of one object therefore necessarily agree about it. It composes only if the two permissions are **explicit** parameters and the second view is renamed onto the first with `pts_to_injective_eq` *before* either is gathered — both matching problems, invisible at one level of nesting. | `test/pulse_facts/ObjectFacts.fst:frac__inv_gather_gen` and `frac_outer__inv_gather_gen` (a class owning a class, the smallest configuration that catches it), verified. Relied on by R3.10d. |
| F24 | Pulse normalises `p /. 2.0R +. p /. 2.0R` to `p` for `pts_to`, which has prover support, but **not** for a user-defined slprop, which is matched syntactically. | `test/pulse_facts/ObjectFacts.fst:frac__inv_gather` needs the arithmetic discharged by an explicit `rewrite`; `PermProbe`-style `Box.share; Box.gather` round-trips without one. Relied on by R3.10d, which states `gather` as `share`'s exact inverse so the arithmetic is discharged once. |
| F25 | Pulse does **not** split a permission at a call site. `f s s`, where `f` takes two independently-fractional parameters, fails with `Cannot prove: …__inv s _` against a context holding exactly that resource — for an object *and* for an array. Splitting is a proof step, and Pulse does not guess it. | `test/pulse_facts/ObjectFacts.fst:frac_alias`, `frac_alias_array`, verified with the `share` and failing without it. Relied on by R5.13. |
| F27 | **Two** views of one object may be in scope at once; **three** may not. Matching an slprop against the context is a search for a *unique* candidate, so after a second `share` there are three resources with the same head and the same name and the next call is refused. Two is what read-only aliasing needs, and more is reached by nesting share/use/gather. The permission itself splits without bound — it is simultaneity that is limited. | `test/pulse_facts/ObjectFacts.fst:frac_two_views` (verified), `frac_three_views` (`expect_failure`), `frac_split_thrice` (verified). Relied on by R3.10e. |
| F26 | Generalising a **read-only** method over the permission is a *pure* generalisation: a caller holding full ownership calls it unchanged, because Pulse instantiates the binder at `1.0R`. It is also **necessary for composition** — R3.10c propagates the outer fraction into a sub-object's invariant, so an owner's reader can only call its parts' readers if those are generalised too. | `test/pulse_facts/ObjectFacts.fst:frac_peek`, `frac_full_owner_reads`, `frac_outer_peek`, verified. Relied on by R4.11b. |
| F19 | F18's idiom works only where the postcondition is **known**. Inside a block in statement position Pulse is still solving for that block's post, and unifying the object's model existential against a uvar fails: `Error 339: Cannot find witness for …; Cannot check relation with uvars`. Binding the witness at the allocation, discarding `exists* m. inv x m` directly, and annotating the branch `ensures emp` all fail (the last one succeeds only for a branch that touches nothing else). | `test/pulse_facts/ObjectFacts.fst:allocate_in_a_returning_branch`, verified; the failing shape is `test/diagnostics/cases/ObjectInNestedBlock.cs`. Relied on by R4.14a. |
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

**R2.3 (reading the verifier's answer back).** R2.2 answers "what does this construct come
from". The other direction — "what is this *line* about" — is what turns an F* error into
something a C# programmer can act on, and it is the reason the frontend does not need to
pre-empt the prover.

The emitter records, for each line of each generated module, the `IrLoc` it was emitting
for, written to `line_map.json` as `{file, fallback, lines: [{line, source}]}`. A statement,
a clause of a contract and a declaration each claim a line; the temporaries, folds and
discards between them claim none, and are read as belonging to the last construct that
started at or before them. `palcs report` consumes F*'s `--message_format json` on stdin,
maps each message through that, and writes `verification.txt` — a flat tab-separated file,
not JSON, because it is read inside a Roslyn analyzer where a dependency that fails to load
is a silently missing feature rather than an exception.

Three properties are deliberate:

* **The message is F*'s, verbatim.** Only the location changes. A tool that rewrote a
  prover's explanation into something friendlier would be paraphrasing a proof it did not
  perform, and the first time the paraphrase was wrong there would be no way to tell.
* **The reporter passes judgement on nothing.** It exits zero whatever it read; `pipefail`
  in `test/verify.mk` is what keeps a failed proof a failed build. A filter that could also
  fail the build would make a passing build depend on it having understood the output. For
  the same reason it never consumes what it did not recognise: F*'s prose ("Verified
  module: M") goes through untouched, and a message it could not place is printed at the
  location F* gave it. A filter standing in a build's only output stream may relocate, but
  it may not silence.
* **A warning that maps only to the module's fallback is dropped.** F* warns about its own
  caches and options against ranges in files nobody wrote; claiming those are about a
  particular class would be an invention. An *error* is reported wherever it lands, because
  an error the user cannot see is worse than one in roughly the right place.

The line map is a separate file from `source_range_info.json` rather than a field in it:
they answer different questions, one is read by the provenance lint and the other by the
reporter, and a single file answering both is one neither reader can skim.

For how this reaches an editor, see §8: the analyzer reads `verification.txt` through
Roslyn's `AdditionalFiles`, which is change-tracked, so re-running `make` updates the
squiggles and nothing has to invalidate a cache by hand.

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
* **A field of *class* type is R3.10b's business**, and the same shape.

The obligation this creates lands at the `fold` of R4.11a, and needs one extra device
there. After a method has written into the array, the contents the `unfold` produced are
stale, and the emitter never named the new ones. `with c. assert (A.pts_to …f c);` binds
them — the same device R4.14 needs, for the same reason.

**R3.10b (a class owns its objects).** For each field of class type the invariant gains an
existential for the sub-object's **model** and a conjunct holding the sub-object's own
invariant:

```fstar
let class_C__inv (this: class_C) (m: class_C__model) : slprop =
  exists* (r: class_C__raw) (model_g: Class_D.class_D__model).
    B.pts_to this r **
    Class_D.class_D__inv r.fld_g model_g **
    pure (… /\ m == ⟦abstraction⟧)
```

This is R3.10a with one word changed. An array field contributes its *contents*; an object
field contributes its *model*; in both cases the field's **reference** appears only in the
resource, and the field name denotes the summary everywhere in the `pure`. So
`low.N` in an `[Invariant]` is `spec_D_N model_low`, which is what `low.N` means in a
client's contract about an object parameter. One reading of a member access, everywhere.

Four things follow.

* **The outer invariant contains the inner one; it does not restate it.** An inner class's
  `[Invariant]` clauses are proved once, where they were written. What the outer class adds
  is what only it can say — a clause relating two sub-objects, such as `low.N <= high.N`.
  That is what composition is *for*, and it is the reason the sub-model rather than the
  sub-object is what the invariant quantifies: a fact about two objects has to be a fact
  about two values.
* **Inside R4.10's window the sub-object is still folded** (F20). The window opens the
  outer box; it does not open what the box holds. So `low.Bump()` in a method of `Range` is
  an ordinary call, needing `Counter`'s precondition and nothing else — and it is *not* a
  self-call, because the receiver is a different object. The question the old refusal said
  the scheme could not answer — when may the outer object open the inner one? — turns out
  not to arise: it never opens it.
* **How an owner names a whole sub-model** is the existing `[Spec]` mechanism doing an
  extra job. A `[Spec]` member of `D` returning `D`'s model type makes `low.State` mean
  `spec_D_State model_low`, so a composite model can hold sub-models rather than
  re-projecting each scalar. No new annotation was required.
* **A bound on a sub-model must be a `[Refine]` on the sub-class's `[Model]`.** F17 is not
  optional here: at a call site the sub-invariant is a folded slprop, so a `pure` conjunct
  inside it is not in the context, and `low.N <= 2147483647` will not be available to
  discharge `Bump`'s precondition. The refinement travels with the model type and is
  therefore always in scope.

The `fold` needs the same extra device R3.10a's arrays need, and for the same reason: a
method may have called something that moved a sub-model, so the binder the `unfold`
produced is stale. `with model_g. assert (Class_D.class_D__inv …fld_g model_g);` names
what the context is actually holding.

Three consequences of the rule being *the same* rule are worth stating, because each was
a question the refusal left open, and `test/deep_class` settles all three.

* **A class may own an array and an object at once**, and nothing mediates between them.
  `Ledger` writes `slots[at]` and then calls `cursor.Step()`; the write settles nothing
  about the cursor and the call settles nothing about the array, which is separation and
  not a rule anyone had to add. The invariant may relate them — `cursor.Bound ==
  slots.Length` ties the object to the array's length — because by then both are values.
* **Depth is not a special case.** `Ledger` owns a `Cursor` that owns two `Cell`s, and the
  middle level is a composite and a component at once. A client of `Ledger` reasons about
  a sequence and a count and never learns that the count lives in a `Cell`.
* **Refinements do not inherit, so each level republishes what its owners need.** A
  `[Refine]` belongs to the *class* model type `class_D__model`; an owner's composite model
  is built from the `[Spec]` **struct** `struct_DModel`, which is that type without the
  refinement. So `Cell`'s `0 <= V` is available inside `Cursor`'s window and *not* in
  `Ledger`'s contracts, and `Cursor` has to state it again. This is F17 one more time, and
  it is the one cost R3.10b charges for depth. It is not busywork: the facts a level
  publishes are exactly the facts its clients may use, so restating them is the interface
  being written down. The alternative — refining the composite's field types by the owning
  class — is not available, because a `[Spec]` struct names no class and several classes
  may share one.

**Ownership transfer is not expressible, and Pulse says so.** A class-typed *parameter* is
preserved (R4.9), so a constructor that stores one in a field asks the `fold` for a
resource its own postcondition also returns, and Pulse reports `Cannot prove:
class_Cell__inv var_x pre_x`. That is the same disposition as a self-call: the translation
is faithful, the program is wrong, and the prover is the one to say it. Sub-objects are
therefore built by the constructor that owns them, which is also why no owner can alias
two of its fields. Aliasing at a *call* is the same disposition again — see R3.13.

What is *still* PALCS0531 is a field whose type is spec-only — a `Seq`, a `Ghost`. Those
are mathematical values with no runtime representation and no resource, so there is nothing
for the invariant to hold and nothing for a constructor to allocate. A field of a class
that declares no `[Model]` is **PALCS0500**, with a message saying so: it fails the type
map rather than the ownership rule.

**R3.10c (the invariant is indexed by a permission).** Every class invariant takes a
**meta-argument-defaulted** permission binder, and the permission propagates to every
resource conjunct — the box, each array field, and each sub-object's own invariant:

```fstar
let class_C__inv (this: class_C) (#[T.exact (`1.0R)] p: perm) (m: class_C__model) : slprop =
  exists* (r: class_C__raw) (contents_f: Seq.seq ⟦T⟧) (model_g: Class_D.class_D__model).
    B.pts_to this #p r **
    A.pts_to r.fld_f #p contents_f **
    Class_D.class_D__inv r.fld_g #p model_g **
    pure (…)
```

`class_C__inv this m` still *means* `class_C__inv this #1.0R m` (F21), so this rule changes
no other rule's output: full ownership is what you get by not asking for anything, which is
what every existing contract says. The whole feature is reached by asking.

Three things about the shape are forced.

* **The propagation is uniform, and it has to be.** A fraction that stopped at the box
  would let two observers of one object disagree about its array, which is exactly the
  unsoundness the box's fraction was preventing. An object at permission `p` is an object
  every part of which is held at `p`; there is no other coherent reading, and it is why
  `[Frac]` on a *field* is not a thing the language offers. A field's permission is the
  enclosing invariant's, always.
* **The model index is unaffected.** A fraction weakens what you may *do* with the object,
  not what you may *know* about it: an observer still names `this.Count` and still gets a
  postcondition about it. That is the point of separating the model from the
  representation — the model was never ownership in the first place.
* **The permission is not part of the model.** Nothing in a `[Model]`, an `[Invariant]` or
  a contract can mention `p`; it is a binder the translation introduces and the user names
  only through `[Frac]`. A specification that could talk about its own permission would be
  talking about the proof rather than the program.

**R3.10d (share and gather).** Each class additionally emits three ghost lemmas:

```fstar
ghost fn class_C__inv_share (this: class_C) (#p: perm) (#m: class_C__model)
  requires class_C__inv this #p m
  ensures  class_C__inv this #(p /. 2.0R) m ** class_C__inv this #(p /. 2.0R) m

[@@allow_ambiguous]
ghost fn class_C__inv_gather_gen (this: class_C) (p q: perm) (#m #m': class_C__model)
  requires class_C__inv this #p m ** class_C__inv this #q m'
  ensures  class_C__inv this #(p +. q) m ** pure (m == m')

[@@allow_ambiguous]
ghost fn class_C__inv_gather (this: class_C) (#p: perm) (#m #m': class_C__model)
  requires class_C__inv this #(p /. 2.0R) m ** class_C__inv this #(p /. 2.0R) m'
  ensures  class_C__inv this #p m ** pure (m == m')
```

They are emitted per class rather than written once in the support library because their
proofs recurse into the class's own structure: `share` shares the box, then each array,
then calls **each sub-object's `share`** (F22). A generic lemma would have to quantify over
that structure, and there is nothing to quantify over — the invariant is a `let`, not an
instance of an interface.

Six details are forced, and each was found by a probe rather than assumed.

* **Every `fold` in the proofs is preceded by an `assert` naming what it consumes** (F22).
  The invariant's existentials are solved by matching against the context, and after a
  share the context holds two candidates for each of them. This is the emitter emitting
  the *scheme*, not rescuing a proof: the lemma's body is fixed by the rule and does not
  vary with the program, exactly as R4.10's fold/unfold bracket does.
* **`gather` proves the two models equal** (F23), and that is not an extra hypothesis. R3.9
  pins `m` to the abstraction function of the representation, `Box.gather` proves the two
  representations equal, and a function of equal arguments is equal. Two read-only aliases
  of one object *necessarily* agree about it — which is the entire reason to allow them.
  A scheme in which they could disagree would be one in which the model was not an
  abstraction function, and F17 already rules that out.
* **`gather` is stated as `share`'s exact inverse**, with the general form kept alongside
  it. Pulse normalises `p /. 2.0R +. p /. 2.0R` to `p` for `pts_to` but not for a
  user-defined slprop (F24), so without this the arithmetic would surface as a `rewrite`
  the user had to write at every call site — a proof step about the *encoding*, which is
  precisely what a proof annotation language must not make anyone write. Discharging it
  once, inside the emitted lemma, is the alternative.
* **`gather_gen` takes its two permissions as *explicit* parameters**, and `gather` calls
  it as `class_C__inv_gather_gen this (p /. 2.0R) (p /. 2.0R)`. Left implicit they are
  solved by matching, and a *nested* gather could then return at `q +. p` where its
  caller's `fold` wanted `p +. q` — the same permission, but a user-defined slprop gets no
  normalisation (F24) and matching is syntactic. Naming them at the call site fixes the
  order once and the nesting composes. Nothing one level deep can detect this, which is
  why F23's pin is a class owning a class.
* **The second view is renamed onto the first *before* anything is gathered**, using
  `Box.pts_to_injective_eq` rather than `Box.gather`. `gather` is `allow_ambiguous` and its
  `ensures` keeps whichever of the two values it matched first, so a subsequent `fold`
  naming the other one fails against a resource provably equal to what it asked for.
  Learning `r == alt_r` without consuming either view, and rewriting first, leaves exactly
  one candidate for every existential — after which the closing `fold` needs no `assert`
  at all, because there is nothing left to disambiguate.
* **A class with no `[Model]` gets none of them**, because it has no invariant to share.

**R3.10e (`share` needs no permission left over).** Nothing bounds how far a permission may
be split: `share` halves whatever it is given, and halving is always possible. The only
thing a program can never do is *write* through a fraction — a write needs `1.0R`, which no
proper fraction can reach and which `gather` recovers only by collecting every piece back.
That asymmetry is fractional permissions working, not a limitation of the translation, and
it is what makes read-only aliasing safe to allow where R3.13's aliasing was not.

What *is* bounded is how many views may be live at once, and the bound is **two** (F27).
Matching an slprop against the context is a search for a unique candidate, so a second
`Share` on a name that already has two views leaves three resources with the same head and
the same name, and the next call is refused — with an error that lists the very thing it
wanted, three times over. More than two observers is reached by nesting: `Share`, use both
halves, `Gather`, and only then `Share` again.

This is worth being precise about, because it is a fact about Pulse's matcher and not about
permissions, and the two are easy to confuse. The permission really does split arbitrarily
far; `test/pulse_facts`'s `frac_split_thrice` halves twice and recombines twice with nothing
in between. It is *simultaneity* that is limited, and pal-csharp says nothing about it —
the refusal arrives from Pulse, on the C# call site, through R2.3.

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
distinct objects. Aliasing is therefore not unsound — it is *unprovable*, and Pulse is what
says so: `Merge(s, s)` gets `Cannot prove: class_C__inv var_s _`.

This rule used to say the opposite. The emitter detected a call passing syntactically equal
object arguments to two owned parameters and refused it as `PALCS0520`, on the reasoning
that F*'s message means nothing to someone who has just written `Merge(s, s)` and that a
diagnostic is not a proof step, so §0 rule 3 was untouched. The reasoning was wrong in two
ways, and both are worth keeping written down.

*It put a rule about separation logic in a pass that does not do separation logic.* The
check could see `f(a, a)` and nothing else. It could not see `f(a, a.Inner)`, or an alias
established three statements earlier, or two paths to one object through a field — all of
which are the same mistake and none of which it caught. So it was never the rule; it was a
syntactic silhouette of the rule, and the difference between those is exactly where a
frontend starts lying. §0 rule 3 says the emitter never invents a proof step. The same
rule points the other way too: **the checker never invents a refusal.** What pal-csharp
refuses is what it cannot *translate*. What Pulse refuses is what cannot be *proved*, and
that boundary is the only reason the frontend is small enough to trust.

*And a refusal hides everything behind it.* `test/diagnostics/cases/AliasedObjects.cs`
carried a second bug for as long as it existed — its `Transfer` required a bound on `from`
while depositing into `to`, so the method did not verify on its own account. Nobody found
out, because the file was refused before it was ever emitted. A frontend that answers
questions the verifier should answer does not merely answer them worse; it stops the
verifier from being asked.

What remains true is the original complaint: `Cannot prove: class_C__inv var_s _` is a poor
thing to show a C# programmer. That is a problem about *where the message appears*, not
about who should produce it, and R2.3 is how it is solved — the message is F*'s, reported
on the C# line that caused it. The case now lives in `test/pulse_refusals`, which checks
all three things at once: that the translation is clean, that Pulse refuses it for the
stated reason, and that the refusal lands on the line the reader is looking at.

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
at once — provided the caller splits its permission first, which is `Pal.Share` (R5.13).

**R4.9a (an observed object).** `[Frac("p")]` on a **class-typed** parameter weakens its
resource the same way, from `class_C__inv a m` to `class_C__inv a #p m`:

```csharp
public static bool SameSize([Frac("pa")] Stack a, [Frac("pb")] Stack b) => …
```
⟶
```
fn func_Cmp_SameSize (var_a: Class_Stack.class_Stack) (var_b: Class_Stack.class_Stack)
                     (#pa: perm) (#pb: perm)
                     (#pre_a: erased Class_Stack.class_Stack__model)
                     (#pre_b: erased Class_Stack.class_Stack__model)
  preserves Class_Stack.class_Stack__inv var_a #pa pre_a
  preserves Class_Stack.class_Stack__inv var_b #pb pre_b
  …
```

The consequences are R4.9's, one word changed, and one of them is new.

* **The model cannot change**, so — as for an array — the one binder stands for the pre-
  and the post-state. An observed object contributes no existential to the postcondition,
  which is why `SameSize`'s `ensures` can say `Result == (a.Count == b.Count)` with no
  `Old` and no frame reasoning.
* **The two permissions are independent binders**, which is exactly what makes `a` and `b`
  allowed to be the same object. Giving both parameters one binder would forbid it again
  by construction.
* **A mutating method may not be called on it**, and pal-csharp does not say so — Pulse
  does, because `Push` requires `class_Stack__inv this m` and the context holds
  `class_Stack__inv this #p m`. This is §0 rule 3's other direction working as intended:
  the frontend would have to know which methods mutate, which is a question about
  contracts, and the contracts are already in front of the prover.

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

*A self-call is a call like any other.* An instance method called on `this` lowers, by
R6.6, to a call whose first argument is `this` — because that is what it is. Its precondition asks for
`class_C__inv this m`, and the window this method is running in is precisely where that
does not hold, so **Pulse reports it**. The emitter neither refuses it nor arranges around
it, and both restraints are deliberate.

Refusing would be a claim the scheme is not entitled to make. The rule is a consequence of
R4.10, not an extra restriction on top of it: an unfolded object does not satisfy a
contract that asks for a folded one, and Pulse says so in exactly those terms. A
compiler-side check would be a *second*, hand-maintained statement of the same fact,
free to drift from the first.

Arranging around it would be worse. Re-folding before the call and re-unfolding after is
the obvious repair, and it silently inserts a proof obligation the user never wrote — the
invariant would have to be re-established at a point they did not choose, and when it could
not be, the failure would land there rather than where the design went wrong. That is §0
rule 3's case exactly.

So the remedy is the user's, and it is the ordinary one: move the shared work into a static
method taking what it needs, and have both instance methods call *that*. What is left over
after doing so is usually a sign that the object wanted a state-indexed invariant, which is
a different scheme (see §8).

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
by a write-set analysis, not by a heuristic.

*What counts as a write*, precisely, because two of the three were learned the hard way:

1. A **field assignment**. The original rule, and the only obvious one.
2. A **write into an array the object owns**. `items[i] = v` assigns no field symbol, but
   R3.10a says the contents *are* part of the model, so a method doing only this moves its
   model and must not be given `preserves`. The test peels an assignment target down to its
   root before asking whether it is a field. Handing an owned array to any callee counts
   too: it may come back written.
3. A **call to an instance method that is not itself read-only**. This one *follows the
   call*, and R3.10b is why it must. An owner reads its state by calling its sub-objects'
   read-only methods, so a rule counting any instance call as a write would classify every
   such reader as a mutator — and its caller would be handed a result related to a model it
   knows nothing about. That is not a conservative approximation, it is a useless answer.
   Recursion terminates by treating a cycle as a write.

Every one of these errs strict when it errs: the permissive direction would tell a caller
the model did not move when it did, which is unsound, while the strict direction only costs
the caller an existential — exactly what it would have had without R4.11 at all.

**R4.11b (a read-only method is observed, not owned).** The same analysis decides one more
thing: a method that gets `preserves` also gets a permission binder, and its receiver is
held at that permission rather than at `1.0R`:

```
fn func_C_M (var_this: Class_C.class_C) (#p: perm) (#m: erased Class_C.class_C__model)
  preserves Class_C.class_C__inv var_this #p m
```

No annotation is involved, and none is offered. Three reasons this is inference where
R4.9a is annotation.

* **It is a pure generalisation** (F26). A caller holding full ownership is unaffected:
  Pulse instantiates the binder at `1.0R` and the call site is textually what it was. So
  unlike `[Frac]` on a parameter — which *weakens* what the callee may do and therefore has
  to be the author's decision — this weakens nothing and can be given for free.
* **It is forced by R3.10c** rather than merely allowed. The fraction propagates into
  sub-object invariants, so a read-only method of an owner holds its parts at *its own*
  permission. If a part's readers were fixed at `1.0R`, no fractional owner could read its
  own parts, and R3.10b's composition would stop at the first fraction. Generalising is not
  an optimisation here; it is what makes the two rules compose.
* **It is decided by the same analysis, so it cannot disagree with `preserves`.** A method
  that may move its model needs full ownership and a method that cannot does not, and those
  are the same question asked once. Two analyses could drift apart; one cannot.

What this rule does **not** do is decide anything about a *call*. Whether a caller has
enough permission for the method it is calling is a separation-logic question, and R3.13's
lesson applies: it is asked and answered by Pulse, against the contracts, and the answer
arrives on the C# call site through R2.3.

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

**R4.14b (an object local that is an alias).** `C x = y;` where `y` already names an object
allocates nothing. It binds a second C# name to one object, so the translation is to bind a
second *slot* to one Pulse binder: `x` and `y` denote the same term, and nothing at all is
emitted for the declaration.

That is forced from both sides. R4.14 would otherwise discard `x`'s invariant at the end of
the method — but `x` owns nothing, the invariant belongs to `y`, and the discard would take
the resource the method has to hand back. And emitting `let var_x = var_y;` would not help:
the context would hold `inv var_y _` while every later mention asked for `inv var_x _`,
which is the same syntactic gap R4.14's last paragraph closes for a returned object, in the
other direction.

Sharing the slot also makes R5.13 do the right thing without knowing about aliases at all.
`Pal.Share(x)` becomes the lemma applied to `var_y`, because that is the object there is —
and the case where an alias is what makes the split worth writing is exactly the case
`test/frac_alias`'s variant is built around.

**R4.14a (where an object may be allocated).** R4.14's discard lands at the end of the
block that declares the object — which is where C# says the name goes out of scope, and
not merely at the end of the method: an object allocated in one arm of an `if` must not be
discarded in the other, where its binder does not exist.

F19 then bounds where the declaration may appear. The discard has to be checked against
the enclosing block's postcondition, and only a block that ends at the method's exit has
one. So an object local may be declared in the method's own block, or in a branch that
returns; in a block that *closes* around it — a statement-position `if`, a loop body — it
is **PALCS0001**. The message says where to move it.

**R4.15 (statements inside the window).** R4.10's bracket is open across the whole body,
so every statement in an instance method runs where the object's invariant does *not* hold
and the receiver is a representation rather than an object. Two rules follow from that, and
both live in §5 because they are rules about statements: R5.11a for a ghost statement and
**R5.12** for a loop.

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

A ghost statement is a proposition about values, and the context holds resources, so the
values have to be named first. The emitter emits `with v₁ … vₙ. assert (r₁ ** … ** rₙ);`
over everything the method owns, and binds each `vᵢ` in the scope the proposition is
elaborated in — F18's idiom, used to *read* rather than to discard.

**R5.11a (a ghost statement inside R4.10's window).** In an instance method the receiver is
not among those resources: R4.15 says the invariant is unfolded, so `class_C__inv this m`
is precisely what the context does not hold and asserting it would fail. R5.12's
representation is named instead — the same `B.pts_to`, the same one `A.pts_to` per array
field, the same `this.f` scope bindings — which is also what lets the proposition mention a
field:

```csharp
Pal.Assert(n <= items.Length);
```
⟶
```
with vrep vcontents_items. assert (B.pts_to var_this vrep **
                                   A.pts_to vrep.Class_Bag.fld_items vcontents_items);
assert (pure ((I32.v vrep.Class_Bag.fld_n) <= (Seq.length vcontents_items)));
```

**R5.12 (a loop inside R4.10's window).** A loop in an instance method sits where the
invariant is unfolded, so what it carries is the **representation**, not the object:

| carried | for |
|---|---|
| `B.pts_to var_this r` | the record cell R3.6 gave the class |
| `A.pts_to r.Class_C.fld_f c_f` | each array field `f`, whose contents R3.10a makes part of the model |
| `Class_D.class_D__inv r.Class_C.fld_g model_g` | each object field `g`, still **folded**, so the body may call its methods (R3.10b, F20) |

Each field is bound in the invariant's scope under the key `this.f`, so that a user writing
`Pal.Invariant(n <= items.Length)` inside the method means the representation's `n` and the
representation's contents — the same reading R3.9b gives a class-level `[Invariant]`, and
for the same reason. A scalar field denotes its projection out of `r`; an array field
denotes its contents sequence.

*Which halves are existential* is decided by what the body writes, and the distinction is
not an optimisation:

* A **field assignment** replaces the whole record (R3.6), so it unsettles `r` and, with
  it, every array reference projected out of `r`.
* An **element write** — or handing an owned array to a callee, which may write it —
  unsettles only that array's contents. The record survives, because a record update is
  definitionally equal to the original in every field it does not mention.
* A **call on a sub-object** unsettles only that sub-object's model, and only if the callee
  is not read-only. This is the one case in which a field survives being handed to a
  callee, and it needs a distinction `MutatesReceiver` alone cannot draw — a read-only
  instance call and a static call both leave it false — so the IR records whether a call's
  first argument is a receiver at all.
* Anything the loop leaves alone is **named before the loop** with R5.8b's `with … assert`
  rather than quantified inside it. For the receiver that is essential rather than
  convenient: a read-only method re-folds its invariant at the model it was *handed*
  (R4.11a), and an existentially quantified record could not possibly abstract to it.

Two pure conjuncts are the emitter's, and only two, because both come from C#'s array type
rather than from anything the user wrote:

* `Seq.length c_f <= 2147483647` — R3.10a's bound, restated because an existential remembers
  nothing.
* `Seq.length c_f == Seq.length c⁰_f` where the contents are existential but the record is
  not — no C# operation changes the length of an array it has been handed, so a loop that
  writes only elements leaves the length where it was. `c⁰_f` is named before the loop, for
  the same reason and by the same mechanism as the fixed binders above.

What is **not** carried is the class's own `[Invariant]` clauses. They may be transiently
false — that is what the window is for — so a loop that needs `n <= items.Length` says so,
in a `Pal.Invariant` of its own. That is R5.8's rule unchanged: the resources are the
emitter's, the propositions are the user's.

*Interaction with F3.* A `decreases` measure may name a field only where the loop leaves
that field alone, because only then does the field have a binder from *before* the loop.
Where the loop writes it, the binding is simply absent from the measure's scope and naming
it is refused — which is F3's rule (a measure may not mention the invariant's
existentials) arriving as a consequence rather than as a special case.

`test/bag_class` is the acceptance test: `Fill` writes elements (contents existential,
record fixed, length carried) and `Max` writes nothing (everything fixed, so R4.11a's
`preserves` re-fold goes through). `BagVariant.cs` writes both loops as `for` loops and
gets, modulo names, the same Pulse.

**R5.13 (splitting and recombining a permission).** `Pal.Share(x)` and `Pal.Gather(x)` are
ghost statements, `[Conditional]` like every other, and they translate by what `x` is:

| `x` | `Pal.Share(x)` | `Pal.Gather(x)` |
|---|---|---|
| an object of class `C` | `Class_C.class_C__inv_share ⟦x⟧;` | `Class_C.class_C__inv_gather ⟦x⟧;` |
| an array | `A.share ⟦x⟧;` | `A.gather ⟦x⟧;` |

They exist because **Pulse does not split a permission on its own** (F25). Passing one
object to two observed parameters fails with `Cannot prove: class_C__inv s _` against a
context holding exactly that resource, and the same is true of an array — so R4.9's
standing claim that "the same array may be passed to two parameters at once" was, until
this rule, not actually reachable. `test/pulse_facts` now pins both halves.

The design question this rule answers is *who* writes the split, and there were two
candidates.

*The emitter could insert it*, at a call site passing the same argument twice. That is
§0 rule 3's forbidden move in its purest form: a proof step invented by the translator in
response to the shape of one call. It also could not work — the emitter would have to
recognise the aliasing to know when to split, which is exactly the recognition R3.13 has
just finished establishing that a frontend cannot do. Two objects reached through fields,
or aliased three statements earlier, need the same split and present no syntactic sign of
it.

*Or the user writes it*, which is the choice, and it is the ordinary one: a split is a
proof step, proof steps come from the user's annotations, and `Pal.Share` sits beside
`Pal.Assert` and a `[Lemma]` call as one more of them. It costs a line, and the line says
something true about the program that was not otherwise written down — that from here on
this object is being read, not owned.

Four consequences.

* **`Gather` is `Share`'s exact inverse, so the pair round-trips with nothing in between.**
  This is what R3.10d's third lemma buys (F24): without it every `Gather` would be followed
  by a `rewrite` about `p /. 2.0R +. p /. 2.0R`, which is a fact about the encoding and not
  about the program.
* **`Gather` proves the two views agreed** (F23), so nothing needs to be re-established
  after one. A caller that shared, observed through both halves, and gathered knows the
  model is the one it started with.
* **Sharing more than twice is sharing twice, twice.** `Share` halves; three observers take
  two shares and two gathers. Nothing bounds the depth.
* **`Pal.Share(this)` inside an instance method is Pulse's to refuse.** R4.15 says the
  receiver's invariant is unfolded there, so the lemma's precondition is precisely what the
  context does not hold. The frontend says nothing about it — §0 rule 3, other direction.

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

**R6.7a (sequence vocabulary).** `Pal.Slice(s, i, j)` ⟶ `Seq.slice ⟦s⟧ ⟦i⟧ ⟦j⟧`,
`Pal.SetAt(s, i, v)` ⟶ `Seq.upd`, `Pal.IsPermutation` ⟶ `CS.is_permutation`, and
`Pal.Rotate(s, n)` ⟶ `CS.rotate ⟦s⟧ ⟦n⟧`, the sequence read from `n` and wrapping. Each is
a direct name for an `FStar.Seq` or `Pulse.Lib.CSharp.Seq` function; the emitter adds
nothing. `rotate` is there because it is the abstraction function of any container that
stores its elements at a moving origin, and because its characteristic equation
`⟦Rotate(s, n)[k]⟧ == ⟦s[(n + k) % s.Length]⟧` is a fact about sequences that §0 rule 3
places in the library rather than in the emitter or in one program's annotations.

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
* **`test/circular_buffer` has been done again, properly** (`test/ring_class`). M1's
  version is a struct beside an array the caller carries, with every specification written
  against `head`, `count` and raw indices, because a struct can hide nothing. The class
  version owns the array (R3.10a), and its model is a queue of `Elems` with room for
  `Capacity` — the wrap-around appears once, in the abstraction function
  `Slice(Rotate(Contents(buf), head), 0, count)`, and nowhere else. A client proves FIFO
  order, and proves that filling, draining and refilling a capacity-two buffer is
  unobservable, without naming a field. The proof needed three general sequence facts —
  `rotate`'s characteristic equation and two modular ones — and they went into
  `Pulse.Lib.CSharp.Seq` over arbitrary sequences, which is §0 rule 3 working as designed:
  every module verified on the first attempt once the library had them. §7.2's variant
  detector was run on it — `QueueVariant.cs`, the same class with members in the opposite
  order, renamed fields, `this.` written out, compound assignment and expression bodies —
  and the output is identical modulo names and declaration order. Wrap-around is
  translated as arithmetic, not recognised as a shape.
* **An object may own other objects** (R3.10b, `test/nested_class`). The outer invariant
  quantifies each sub-object's *model* and holds each sub-object's own invariant, which is
  R3.10a's rule for arrays with one word changed — and, like it, needed no new annotation.
  `Range` owns two `Counter`s and states `low.N <= high.N`, a fact neither `Counter` could
  express; that is what composition is for. Inside R4.10's window a sub-object stays
  **folded**, so `low.Bump()` is an ordinary call and the question the old refusal could
  not answer — when may the outer object open the inner one? — turns out not to arise, as
  it never opens it. A client of `Range` names no field at any depth, and separation gives
  it that advancing one `Range` leaves another alone *through two levels of ownership*.
  `test/deep_class` takes it further: three levels, and one class owning an array *and* an
  object, with an invariant tying them together. It also found the one cost of depth — a
  `[Refine]` belongs to the class model type, so an owner's composite model, built from
  spec structs, does not inherit it and each level must republish what its owners need.

  `AdvanceBy` puts a loop over a sub-object, which is R5.12 and R3.10b at once: `low` is
  written so its model is quantified, `high` is not so its model is named before the loop.

  Two pre-existing defects surfaced. R4.2's prologue was never emitted for a **constructor**
  — unreachable until a constructor first handed a parameter to a call, which is what
  `new Counter(from)` does. And R4.11's read-only test counted *any* instance call as a
  write, which would have made every composite reader a mutator and its result unusable to
  a caller; it now follows the call, treating a cycle as a write.
* **A loop inside an instance method works** (R5.12, `test/bag_class`). This was refused
  until the sub-scheme was written, and writing it turned out to need one idea: inside
  R4.10's window a loop carries the *representation*, and which half of it is
  existentially quantified is read off what the body writes — a field assignment unsettles
  the record, an element write unsettles only that array's contents, and anything the loop
  leaves alone is named *before* the loop instead. That last part is not an optimisation:
  `Bag.Max` is read-only, so R4.11a re-folds at the model it was handed, which an
  existentially quantified record could never satisfy. `Bag.Fill` is the other side — it
  writes elements, and needs the contents to move while the record does not.
  Implementing it also found a real unsoundness in R4.11's read-only test: it asked
  whether the body assigned a *field*, and `items[i] = v` assigns none, so a method that
  demonstrably moves its model was being given `preserves`. R3.10a says the contents are
  part of the model, so writing one is a mutation, and the test now peels an assignment
  target down to its root. `BagVariant.cs` writes both loops as `for` loops and gets,
  modulo names, the same Pulse.
* **The transiently broken invariant is exercised.** `test/interval_class`'s `Shift`
  writes `lo` and then `hi`; between the two the object is a well-formed
  `class_Interval__raw` whose `lo <= hi` is false. R3.10's choice of a `pure` conjunct over
  a refinement is what admits it — a refinement would have to hold of that intermediate
  record, and R3.6 writes a whole record per assignment, so there is no way to write both
  fields at once and dodge the question. The intermediate state is visible in the output as
  two `B.op_Colon_Equals` with no `fold` between them.
* **R4.10a and R4.10b are enforced** (`PALCS0526`, `PALCS0525`). Roslyn reports both as
  errors about a static method in a namespace the user has never heard of, because that is
  what the shim is; the remapping states them in terms of the annotation surface instead —
  "write `@this`", and "a contract may name only what a client could name". Every other
  binding error is still passed through verbatim, because Roslyn words it better than we
  would.
* **R3.13 is Pulse's** (no diagnostic). A call passing one object — or one non-`[Frac]`
  array — to two owned parameters is translated faithfully and refused by the prover, which
  is the only thing that can tell an alias from a coincidence. `Bank.Transfer` in
  `test/account_class` is the shape it protects; `test/pulse_refusals` is the misuse, and
  checks that the refusal arrives on the calling line.
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
  `test/diagnostics` is its counterpart to the verification tests — twenty-two cases, each
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

* **The diagnostics are in the editor** (`src/Pal.Analyzers`, `test/analyzer`). The
  analyzer states no rule of its own: it runs the compiler's own passes over the
  compilation the IDE already has, and turns each `PalDiagnostic` into a Roslyn one.
  Everything `palcs` refuses, the editor underlines, in the same words and at the same
  span — including a span *inside* a specification string, which is why `IrLoc` has
  carried an end position since M1. There is no second copy of the subset, so there is
  nothing to drift.

  *Its own passes* includes the emitter, whose output is then thrown away. This was not
  the first design and the correction is worth recording: stopping at the checker looks
  right, since an editor has no business writing files, but eight of the thirty-six
  diagnostics — R5.3's unbridgeable type, F3's measure over an existential, an unsupported
  specification term — are only discovered while emitting. An analyzer that reported the
  other twenty-eight would be worse than none: it would tell a user who had cleared every
  squiggle that the program was ready, and the build would then disagree. The parity is
  cheap, because emission is string building over an IR already in hand. What the analyzer
  still does not do is write anything or run F\*: verification is a separate, slow,
  deliberate act, and what an editor can give for free is the answer to "is this program
  inside the language at all".

  The gap was found by the wiring in §8's editor note rather than by `test/analyzer`,
  which is the more useful lesson: the acceptance test picked its cases by hand, and a
  hand-picked set is exactly what fails to notice a whole pass going unrun. It now checks
  that every directory of `Pal.Compiler` that raises an id is represented among its cases,
  so a pass added later, or one the analyzer stops running, fails the build.

  It bails out twice before doing any work: on a project that does not reference
  `PalLang`, and on a compilation C# itself has already rejected — the second for the same
  reason `palcs` does it, that reporting a binding error a second time in worse terms
  helps nobody.

  What Pulse said arrives rather than being computed. An analyzer cannot run a prover — it
  is asked to answer between keystrokes — but it can read the last answer, and Roslyn has
  a sanctioned way to depend on a file: `AdditionalFiles`, which it tracks for changes and
  re-runs analysis over. So `palcs report` writes `verification.txt` when the proof runs
  (R2.3), `test/pal-tests.props` lists it, and the analyzer reports each message at the
  C# span it was mapped to, as `PALCS0600`. Run `make`, watch the squiggles change. The
  alternative — an analyzer opening the file itself — reads something Roslyn does not know
  it depends on, so the result gets cached against a key that does not include it and the
  squiggles go quietly stale, which is the one failure mode worse than having none.

  Two things had to be arranged, and neither is a translation concern. A Roslyn analyzer
  is loaded into whatever process is compiling, which may be .NET Framework, so it must be
  `netstandard2.0`; `Pal.Compiler` was `net10.0` for no better reason than that it was the
  default when the only consumer was a command-line tool. It uses no API newer than
  netstandard2.0, so multi-targeting it cost one `#if`'d shim file — `Index`, `Range`,
  `IsExternalInit`, and four BCL overloads — and changed no real code. And an analyzer must
  declare its diagnostic ids before it has seen a program, which is a list, and a list
  drifts: `Diagnostics/Catalog.cs` holds the ids and *only* the ids, with the message still
  written where the rule is checked, and `test/diagnostic-ids.sh` greps the passes for
  `"PALCSnnnn"` literals and fails the build if the two sets or the two severities disagree.

  `test/analyzer` builds real projects with the analyzer loaded, using
  `test/diagnostics`'s own cases so that the expectation is shared rather than restated. It
  checks the half a negative test cannot state as well: a program that is inside the
  language builds clean, with no pal-csharp diagnostic of any severity — and *builds*,
  which asserts the project's core invariant against the C# compiler rather than against a
  document.

  Using it is a matter of the editor loading a project that has it. The test directories
  deliberately carry no `.csproj` for the build — `test/build-cs.sh` synthesises a *stock*
  one, because the obligation it checks is that annotated C# is ordinary C#, which a
  project loading pal-csharp's own analyzer would no longer be checking. So the editor
  gets its own, generated by `test/cs-projects.sh`: one project per directory (the tests
  reuse type names across directories on purpose, so a single project would not compile),
  each four lines deferring to `test/pal-tests.props`, plus a `Pal.Tests.sln` listing them
  and a `.vscode/settings.json` pointing at it. `Pal.slnx` stays the product-only solution
  that `make` and CI build. `cs-projects.sh --check` runs in the lint beside
  `fst-configs.sh --check`, and for the same reason: an editor that disagrees with the
  build about what a directory contains is worse than an editor that knows nothing about
  it.

* **A refusal that was in the wrong place is gone** (`test/pulse_refusals`). `PALCS0520`
  detected an aliased call and refused it, so that F* would not have to explain itself in
  Pulse names. R3.13 records why that was a mistake in full; the short version is that a
  syntactic check for `f(a, a)` is not the rule it was standing in for, and that the case
  it guarded had been hiding a second bug for as long as it existed. The rule is now
  Pulse's, and what was really wanted — the message on the right C# line — is R2.3.

  `test/pulse_refusals` is the suite that became possible once refusing was not the
  answer: three programs that translate cleanly, fail in F*, and must fail *for the stated
  reason* and *on the marked line*. Aliasing, a self-call with the invariant unfolded, and
  ownership transfer into a field — the last two had been documented in this file for
  milestones without ever being executed, because there was nowhere to put a test whose
  expected outcome was a proof failure. Its check that each case still compiles as ordinary
  C# is the same core invariant every other test directory asserts.

  The third case is worth singling out. Its message lands on the *constructor*, not on the
  assignment inside it, because what cannot be discharged is the constructor's exit — where
  it owes both `this`'s invariant and the parameter's back. The line map got that right
  without being told, which is the evidence that R2.3's containment rule is the right one
  and not a rounding.

* **Object invariants are indexed by a permission** (R3.10c–R3.10e, R4.9a, R4.11b, R5.13),
  so an object can be *observed* rather than owned, and two names can observe one object at
  once. `test/frac_alias` is the acceptance test: two `[Frac]` object parameters called on
  one object, an owner observed through a fraction whose two parts are read through the
  same fraction, the array case that closes `test/compare_elements`'s standing gap, and a
  variant that reaches the alias through a local.

  The feature is textually additive, and F21 is why: the permission binder is
  *meta-argument-defaulted*, exactly as `Box.pts_to`'s is, so `class_C__inv x m` still means
  full ownership and every rule that existed before this one emits what it emitted before.
  Every class test verified unchanged.

  Four things the probes forced, none of them anticipated. **F23's composition**: a nested
  `gather` needs its permissions as *explicit* parameters and needs the second view renamed
  onto the first with `pts_to_injective_eq` *before* either is gathered — both are matching
  problems, both are invisible at one level of nesting, and a class owning a class is the
  smallest thing that catches them. **F25**: Pulse does not split a permission at a call
  site, for objects or for arrays, which means R4.9's claim since M1 that "the same array
  may be passed to two parameters at once" was never actually reachable; R5.13's
  `Pal.Share`/`Pal.Gather` is what makes it so. **F26**: generalising read-only methods over
  the permission is not an optimisation but the thing that makes R3.10c compose, because a
  fractional owner reads its own parts at its own permission. **F27**: two simultaneous
  views are the limit — a third makes the matcher ambiguous — so more observers are reached
  by nesting share/use/gather, and R3.10e says so rather than claiming otherwise.

  One rule was found by the variant test rather than by design. **R4.14b**: `C x = y;` binds
  a second name to one object, so it emits nothing and shares the slot. Before that, R4.14
  discarded the alias's invariant at the end of the method — taking the resource the method
  had to hand back. The §7.2 detector doing exactly what it is for.

### Not yet done

* **Packaging the analyzer as a NuGet package.** It is wired into `test/analyzer` as
  `Analyzer` items, which is enough to run it and enough to test it, but a user still has
  to point at the built assemblies. A package also has to carry `System.Text.Json` and
  `System.Memory` for a .NET Framework host, where they are not in the shared framework;
  under `dotnet build` they resolve today.
* **Live squiggles are per-compilation work.** The analysis is whole-program — a call needs
  its callee's contract — so it runs once per compilation and is then reported per file.
  On the programs in `test/` that is milliseconds; nothing has been measured at a scale
  where it would not be.
* `Span<T>` and `ReadOnlySpan<T>`. A method mentioning either is rejected with a diagnostic
  rather than mistranslated; fractional permissions are reached through `[Frac]` instead
  (R4.9).
* A struct field must be a value — a scalar or another translated struct. An array or
  class field is **PALCS0511**, and that is the model rather than a shortcut: a struct
  copy would duplicate ownership of the same memory. Storage therefore travels alongside
  the state it describes, as in `test/circular_buffer`. A *class* has no such restriction
  (R3.10a), so `test/stack_class` is what `test/circular_buffer` wanted to be.
* Generics, interfaces, `string`, and `float`/`double` remain unspecified as well as
  unimplemented. §3.4 itself is now complete for the field kinds it admits: a class field
  may be a value, an array (R3.10a) or another annotated object (R3.10b). What is refused
  is a spec-only field type (PALCS0531) and a class with no `[Model]` (PALCS0500), and
  neither is a gap — there is no resource to own in the first case and no model in the
  second.
* **Object abstraction is deliberately deferred.** `class_C__inv` is specified as a
  *concrete* definition in the class's own module. Hiding it behind an `.fsti`
  (`val class_C : Type0`, `val class_C__inv : class_C -> model_M -> slprop`) works
  and needs no F\* `friend`, but it requires a module shape the emitter does not have
  today, and C# `private` already hides the representation at the source level. The step is
  available when proof performance or genuine information hiding demands it.
* **An object may not be allocated in a block that closes around it** (R4.14a,
  `PALCS0001`). F19 is a limitation of Pulse's inference, not of the scheme, and the
  workaround — allocate in the method's block, or in a branch that returns — is usually
  what the code wanted anyway. `test/ring_class/RingScope.cs` covers what does work,
  including two buffers on two arms of one `if`.
* **A field is not yet nameable in a spec position outside a loop or a ghost statement.**
  R5.11a and R5.12 bind `this.f` where the emitter has just named the representation; a
  `[Requires]` or `[Ensures]` still reads against the model (R3.9c), which is right, but
  there is no third context in which a field is in scope. Nothing so far has wanted one.
* **Object lifecycle is unspecified.** A class with two-phase initialisation or `Dispose`
  wants a *state*-indexed invariant — `class_C__inv this st m` — and nothing in M2 has one.
  R4.13's `sealed`-only restriction keeps it out of scope for now.

  Note that **calling an instance method on `this` is not on this list**. It is settled, by
  design: R4.10 translates it faithfully, its precondition asks for a folded invariant, the
  window it runs in has an unfolded one, and Pulse reports the mismatch. There is nothing
  for the emitter to add.
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
