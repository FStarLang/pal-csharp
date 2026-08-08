# The pal-csharp translation scheme

This document defines `⟦·⟧`, the translation from annotated C# to Pulse. It is the
**specification of the emitter**: `Pal.Compiler` is an implementation of the rules below,
and anything the emitter does that is not justified by a rule here is a bug.

Every rule is **compositional**: it is defined by the shape of a C# construct alone,
independently of any example and of its surrounding context.

Rule ids (`R<section>.<n>`) are cited from `Pal.Compiler`, from the Pulse library and from
`test/`, so they are stable: a section may be reorganised, but a rule is never renumbered.
The numbering is therefore not contiguous where a rule was withdrawn. Facts (`F<n>`) are
Pulse behaviours probed and pinned in `test/pulse_facts/` before the rule that relies on
them was written; §1 lists them all.

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

Two mechanical detectors back these up — **variant tests** and the **provenance lint** —
stated in §7.2.

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
| F7 | `Pulse.Lib.Array` provides no SMT-patterned link between `Array.Core.length a` and `Seq.length s`; `pts_to_len` must be invoked explicitly. Modelling `a.Length` as a *pure* function of the array (sound, because a CLR array's length is immutable) avoids needing it at every guard. | `Pulse.Lib.Array.fst:38,65,117` all call `pts_to_len` by hand; `Pulse.Lib.CSharp.Array.arr_length` takes the pure route. |
| F8 | A **stateful block may appear in term position**, as the scrutinee of a `let`: `let t = if (c) { <stateful block> } else { e };` is well-formed Pulse. This is what makes the short-circuit rule R6.3 compositional — the same lowering serves a loop guard, an `if` condition and an assignment right-hand side, with no context-dependent special case. | `test/pulse_facts/PulseFacts.fst:short_circuit_in_term_position`, verified; relied on by every generated short-circuit. |
| F9 | A `decreases` measure may dereference a mutable local, but **not underneath an `if`**. `decreases (if !b then 0 else I32.v !r)` is rejected with "Expected type `FStar.Int32.t` but `!r` has type `fn …`", because the `!` sugar is elaborated only outside the branches. A conditional measure must keep its dereferences out of the branches. | `test/pulse_facts/PulseFacts.fst:decreases_conditional_without_deref`, verified; the failing form was reproduced while writing `test/binary_search`. |
| F10 | F\* resolves **module-qualified record syntax** in all three positions — projection `e.M.f`, update `{ e with M.f = v }`, and literal `{ M.f = a; g = b }` — without the defining module being `open`ed. So a generated struct module needs no `open` anywhere, and two structs may share a field name with no ambiguity. | `test/pulse_facts/PulseFacts.fst` + `test/pulse_facts/StructFacts.fst`, verified. |
| F11 | A record **update's source must be a pure term**: `{ !r with M.f = v }` is rejected ("Ill-typed term … got expression of type `fn … returns …`"), because `!r` is a stateful operation and the update is a term former, not a statement. The deref must be let-bound first. This does not contradict F8: F8 is about a stateful block as the *scrutinee of a `let`*, which is precisely the form that fixes this. | `test/pulse_facts/StructFacts.fst:struct_field_write`, verified; the failing form was reproduced while writing R3.4. |
| F12 | A Pulse `fn` **must have at least one binder**. A parameterless one fails in the elaborator, not the solver: "Tactic failed — main: FnDefn does not have binders". So a C# method with no parameters takes `()`. | `test/pulse_facts/StructFacts.fst:no_parameters`, verified; the failing form was reproduced by `test/point_struct`'s `Origin()`. |
| F13 | `preserves p` is a genuine `fn` spec clause, meaning exactly `requires p ensures p`, and it composes with `requires` and `ensures` on the same `fn`. | `test/pulse_facts/ObjectFacts.fst:count`, verified. Relied on by R4.11. |
| F14 | `Pulse.Lib.Box` is the **sound** heap cell and the right model of a CLR object. `Pulse.Lib.Reference.alloc` is marked `[@@deprecated "…is unsound; only use for model implementations"]` and may not appear in generated code; `Box.alloc` carries no such marker. `Box` additionally supplies `null`, a *pure* `is_null`, and `pts_to_not_null`, so a nullable object reference needs no new machinery. | `tools/fstar/lib/fstar/pulse/pulse/lib/Pulse.Lib.Reference.fsti:87` and `Pulse.Lib.Box.fsti:31-53,90-110`; `test/pulse_facts/ObjectFacts.fst:ownership_implies_non_null`, verified. Relied on by R3.8 and R3.11. |
| F15 | Pulse slprops are **affine**: `Box.free` exists but nothing compels a caller to reach it, and a leftover resource is discharged by `drop_`. So modelling a garbage-collected heap needs **no axiom at all** — allocate, never free. | `test/pulse_facts/ObjectFacts.fst:alloc_without_free`, verified: it allocates an array and a box, returns, and frees neither. Relied on by R3.12. |
| F16 | An object resource is linear, so passing the same object to two owned parameters is **unprovable**, reported as a bare `Error 228: Cannot prove: class_C__inv a _`. Aliasing is thus safe but incomprehensible, which is why R3.13 requires the emitter to diagnose it first. | `test/pulse_facts/ObjectFacts.fst:aliasing_is_unprovable` documents the rejected call; the failure was reproduced against the pinned toolchain. |
| F17 | A fact about the **model alone** is visible to a caller only if it lives in the model type as a *refinement*. Placed instead inside the object invariant it is unreachable: a caller holding `class_C__inv this m` cannot derive it without unfolding, and F* reports `Error 19` at the postcondition. | `test/pulse_facts/ObjectFacts.fst:client_sees_model_invariant`, verified; weakening `model_StackModel__pred` to `True` reproduces the `Error 19`. Relied on by R3.9d. |
| F18 | F15's affinity is a **permission to discard, not an automatic discard**. A method that allocates an object and does not return it still holds the invariant when it ends: `Error 228: Leftover resources: class_C__inv x _`. Writing the discard needs a name for the model the context holds — an existential witness the emitter never chose — which `with m. assert p;` binds. | `test/pulse_facts/ObjectFacts.fst:allocate_and_discard`, verified; the failure was reproduced by `test/counter_client`'s `FreshIsZero` before R4.14 existed. Relied on by R4.14. |
| F19 | F18's idiom works only where the postcondition is **known**. Inside a block in statement position Pulse is still solving for that block's post, and unifying the object's model existential against a uvar fails: `Error 339: Cannot find witness for …; Cannot check relation with uvars`. Binding the witness at the allocation, discarding `exists* m. inv x m` directly, and annotating the branch `ensures emp` all fail (the last one succeeds only for a branch that touches nothing else). | `test/pulse_facts/ObjectFacts.fst:allocate_in_a_returning_branch`, verified; the failing shape is `test/diagnostics/cases/ObjectInNestedBlock.cs`. Relied on by R4.14a. |
| F20 | An object's invariant may **contain** another's, and nesting needs no new device: the outer invariant existentially quantifies the sub-object's *model* exactly as R3.10a quantifies an array's *contents*. Inside the outer `unfold` window the sub-object stays **folded**, so calling its methods is an ordinary call. The closing `fold` must re-name the sub-models where it happens, because a call may have moved one. A bound on a sub-model reaches a call site only as a **refinement on the model type** — F17 again, and not optional: as a `pure` conjunct inside the sub-invariant it is behind a folded slprop and does not reach. | `test/pulse_facts/ObjectFacts.fst:ranked_mk`, `ranked_bump_left`, verified. Relied on by R3.10b. |
| F21 | An slprop `let` may take a **meta-argument-defaulted** permission binder, as `Box.pts_to` does: `let inv (this: C) (#[T.exact (`1.0R)] p: perm) (m: M) : slprop`. `inv x m` then *means* `inv x #1.0R m`. So indexing every class invariant by a permission changes no existing emission — full ownership stays what you get by not asking. | `test/pulse_facts/ObjectFacts.fst:frac__inv`, `frac_default_is_full`, verified. Relied on by R3.10c. |
| F22 | A per-class `share` is provable from `Box.share`, `Array.share` and each sub-object's own `share`. Each closing `fold` **must** be preceded by an `assert` naming the resources it consumes: the invariant's existentials are solved by matching against the context, and after a share the context holds two candidates for every one of them. | `test/pulse_facts/ObjectFacts.fst:frac__inv_share`, `frac_outer__inv_share`, verified. Relied on by R3.10d. |
| F23 | A per-class `gather` proves the two models **equal**. Not an extra hypothesis and not a choice: R3.9's invariant pins `m` to the abstraction function of the representation, `Box.gather` proves the two representations equal, and a function of equal arguments is equal. Two read-only aliases of one object therefore necessarily agree about it. It composes only if the two permissions are **explicit** parameters and the second view is renamed onto the first with `pts_to_injective_eq` *before* either is gathered — both matching problems, invisible at one level of nesting. | `test/pulse_facts/ObjectFacts.fst:frac__inv_gather_gen` and `frac_outer__inv_gather_gen` (a class owning a class, the smallest configuration that catches it), verified. Relied on by R3.10d. |
| F24 | Pulse normalises `p /. 2.0R +. p /. 2.0R` to `p` for `pts_to`, which has prover support, but **not** for a user-defined slprop, which is matched syntactically. | `test/pulse_facts/ObjectFacts.fst:frac__inv_gather` needs the arithmetic discharged by an explicit `rewrite`; `PermProbe`-style `Box.share; Box.gather` round-trips without one. Relied on by R3.10d, which states `gather` as `share`'s exact inverse so the arithmetic is discharged once. |
| F25 | Pulse does **not** split a permission at a call site. `f s s`, where `f` takes two independently-fractional parameters, fails with `Cannot prove: …__inv s _` against a context holding exactly that resource — for an object *and* for an array. Splitting is a proof step, and Pulse does not guess it. | `test/pulse_facts/ObjectFacts.fst:frac_alias`, `frac_alias_array`, verified with the `share` and failing without it. Relied on by R5.13. |
| F26 | Generalising a **read-only** method over the permission is a *pure* generalisation: a caller holding full ownership calls it unchanged, because Pulse instantiates the binder at `1.0R`. It is also **necessary for composition** — R3.10c propagates the outer fraction into a sub-object's invariant, so an owner's reader can only call its parts' readers if those are generalised too. | `test/pulse_facts/ObjectFacts.fst:frac_peek`, `frac_full_owner_reads`, `frac_outer_peek`, verified. Relied on by R4.11b. |
| F27 | **Two** views of one object may be in scope at once; **three** may not. Matching an slprop against the context is a search for a *unique* candidate, so after a second `share` there are three resources with the same head and the same name and the next call is refused. Two is what read-only aliasing needs, and more is reached by nesting share/use/gather. The permission itself splits without bound — it is simultaneity that is limited. | `test/pulse_facts/ObjectFacts.fst:frac_two_views` (verified), `frac_three_views` (`expect_failure`), `frac_split_thrice` (verified). Relied on by R3.10e. |
| F28 | **A vtable cannot be a `Box` payload.** `slprop : Type u#4`, so a record with an invariant field lives far above `Type0` — and `Box` needs a `Type0`. So an object reference cannot simply be a box of its vtable, which is what forces F29's `dyn`. (F28b: the restriction is `Box`'s, not Pulse's — a *plain* record is unaffected.) | `test/pulse_facts/InheritanceFacts.fst:49-82`, verified. Relied on by R9.8. |
| F29 | **`FStar.Dyn.dyn : Type0`, and `mkdyn` is universe-polymorphic.** Lowering a vtable-carrying object into `dyn` puts it back in `Type0`, so a reference into a hierarchy is boxable, arrayable and legal as a field. `mkdyn` is *not* injective (it cannot be, on pain of Cantor), which is the source of every remaining difficulty. | `test/pulse_facts/InheritanceFacts.fst:84-96`, verified. Relied on by R9.8, R9.11. |
| F30 | **`FStar.Dyn.undyn` cannot be called from Pulse.** It is in `Dv`, and `Dv` results cannot be equated in specifications, so recovering the object needs an axiom (`recover`) rather than a definition. It must be stated in `stt`, not `stt_div`: `stt_div a emp post` is inhabited for *every* `post` (F30b, verified by a hang), so an `stt_div` axiom would be free and worthless. (F30c: `stt` itself is a `Type0`.) | `test/pulse_facts/InheritanceFacts.fst:113-201`, verified. Relied on by R9.9, §8.4's one assumption. |
| F31 | **A stored Pulse computation must be let-bound before it is applied.** `ob.pkg.area x` does not run; `let f = ob.pkg.area in f x` does. Pulse runs an `stt`-valued term only as the head of an application. | `test/pulse_facts/InheritanceFacts.fst:203-256`, both polarities verified. Relied on by R9.12. |
| F32 | **The model may not be fixed per hierarchy.** A vtable fixes one model type, but a subclass needs its own; the base invariant existentially quantifies the subclass model and relates it by a pure forgetting function. This is R3.9's abstraction function one level up. | `test/pulse_facts/InheritanceFacts.fst:257-316`, verified. Relied on by R9.5, R9.6. |
| F33 | **A pack site must eta-expand every vtable slot.** F21 gives every class invariant a meta-argument-defaulted permission binder, which does not match a vtable field type until the slot is eta-expanded. | `test/pulse_facts/InheritanceFacts.fst:317-340`, verified. Relied on by R9.13. |
| F34 | **An upcast moves no memory.** `Shape s = c;` is a pure re-reading of the same reference, so it is a `ghost fn` and free at runtime — which is what C# requires of a reference conversion. | `test/pulse_facts/InheritanceFacts.fst:341+`, verified. Relied on by R9.14. |
| F35 | A `type … and …` group may **mix a record definition with a type abbreviation**, so a recursive class's representation, its reference type and its nullable form come out as one mutually recursive group and nothing new is needed to tie the knot. | `tools/fstar/lib/fstar/pulse/pulse/lib/Pulse.Lib.LinkedList.fst:14-16`; `test/pulse_facts/RecursiveFacts.fst:class_Node__raw`, verified. Relied on by R10.1. |
| F36 | An inductive ownership predicate must recurse on the **model**, not on the reference. By cases on the reference there is no measure F\* can see, because the sub-model is related to the model by a `pure` equation rather than by a pattern; by cases on the model the sub-model *is* a sub-term and `decreases m` is discharged with nothing written by the user. | `test/pulse_facts/RecursiveFacts.fst:class_Node__inv_opt`, verified. This is the fact that fixes §10's whole shape, and the reason R10.5 asks for the model as a function of the fields. |
| F37 | The five case lemmas of R10.4 are provable from the definition alone, and are placed by the **null test the C# already writes**. R4.10 opens a window around a field access; R10.6 opens the same window around the `else` branch of a null test. | `test/pulse_facts/RecursiveFacts.fst:class_Node__nil_case`, `elim_nil`, `intro_nil`, `elim_cons`, `intro_cons`, `cases`, all verified. Relied on by R10.4 and R10.6. |
| F38 | `decreases` on an **erased** model binder is accepted for a `fn rec`, and the recursive call's obligation is discharged by SMT from the `pure (m == hd :: tl)` that `elim_cons` hands back. So a recursive method needs no measure beyond naming its model. | `test/pulse_facts/RecursiveFacts.fst:func_Lists_Length`, `func_Trees_Size`, verified. Relied on by R10.6. |
| F39 | The ordinary field-write idiom (R3.12's `B.op_Colon_Equals var ({ t with … })`) composes with R10.4 unchanged: the window opened by a null test is exactly the window a field write needs. This is what makes a **destructive** traversal — `Append`, an in-place BST insert — verifiable. | `test/pulse_facts/RecursiveFacts.fst:func_Lists_Append`, `func_Trees_Insert`, verified. Relied on by R10.6b. |
| F40 | R3.10d's `share`/`gather` survive the induction: a `ghost fn rec` recursing on the model proves both, using the class's own case lemmas rather than `unfold`. | `test/pulse_facts/RecursiveFacts.fst:class_Node__inv_opt_share`, `class_Node__inv_opt_gather`, verified. Relied on by R10.7. |
| F41 | R3.10b — "a field of class type contributes that class's invariant at an existentially bound model" — applies **verbatim** when the field's type is nullable and recursive; only the predicate's name changes. So an ordinary M2 handle class over a recursive one needs no new rule. | `test/pulse_facts/RecursiveFacts.fst:class_LinkedList__inv`, `func_LinkedList_Push`, `func_LinkedList_Count`, verified. Relied on by R10.8. |
| F42 | Two recursive occurrences are no harder than one: the two sub-invariants sit side by side under `**`, which is what makes the two subtrees separately owned and hence what makes an in-place tree insert verifiable. | `test/pulse_facts/RecursiveFacts.fst:class_TreeNode__inv_opt`, `func_Trees_Insert`, verified. Relied on by R10.3. |
| F43 | A **back pointer** is expressible with no new device: the predecessor becomes an extra *index* of the predicate, the back pointer is constrained (`pure (r.fld_prev == left)`) rather than owned, and the recursive call passes the current reference as the new index. Reading the index *off the field* in `intro_cons` is what makes a write to `prev` a legal proof step. | `test/pulse_facts/RecursiveFacts.fst:class_DNode__inv_opt`, `func_DLists_Length`, `func_DLists_PushFront`, verified. Relied on by R10.10. |
| F44 | `[]` and `::` are *notation* for the ordinary prefix constructors `Nil` and `Cons`, which work in every position the notation does — as a term, as a **pattern**, and under the discriminator `Cons?`. So a scheme phrased over "the empty constructor" and "the non-empty constructor" covers `list` with no special case, and the emitter needs only a constructor *name* and an arity. | `test/pulse_facts/UserSpecFacts.fst:nil_is_prefix`, `cons_is_prefix`, `length_prefix`, `cons_test`, verified. Relied on by R11.5. |
| F45 | §10's whole encoding — the inductive invariant, all eight lemmas, the window, a recursive traversal and a destructive one — works verbatim over an inductive the **compiler has never heard of**, at a constructor arity that is neither a list's nor a tree's (two pure arguments and one recursive). Nothing in the template depends on which model type it is instantiated at. | `test/pulse_facts/UserSpecFacts.fst:class_Pair__inv_opt`, `class_Pair__elim_cons`, `func_Pairs_Count`, `func_Pairs_Set`, verified. Relied on by R11.6. |
| F46 | `FStar.Int.Cast` supplies a total function for every machine-integer width pair pal-csharp maps, and each is *modular*, not partial: it carries no precondition and truncates. So an explicit C# cast has a translation with no side condition attached — which matters, because C#'s default `unchecked` context defines the same truncation. | `test/pulse_facts/ConversionFacts.fst:cast_is_total`, `cast_truncates`, verified. Relied on by R13.1. |
| F47 | A cast is the identity on the mathematical value exactly when **every value of the source type is a value of the target** — which is strictly narrower than "the target is wider". `uint8 -> int8` and `int32 -> uint32` are both same-width and both lossy. | `test/pulse_facts/ConversionFacts.fst:widening_is_identity`, `same_width_is_not`, verified. Relied on by R13.2. |
| F48 | A *narrowing* cast's mathematical value is `% pow2 n` when the target is unsigned and `FStar.Int.op_At_Percent` when it is signed; the two do not coincide. | `test/pulse_facts/ConversionFacts.fst:narrowing_unsigned`, `narrowing_signed`, verified. Relied on by R13.2. |
| F49 | When the source value is already in the target's range, the modular reading collapses back to the exact one, so a user who proves the range gets exactness with no extra rule. | `test/pulse_facts/ConversionFacts.fst:narrowing_in_range`, verified. |
| F50 | `FStar.Int` has **no** `logand_mask`. The route to a masking fact is `Int.logand a b == Int.from_uint (UInt.logand (Int.to_uint a) (Int.to_uint b))`, which holds by `()` because `to_vec`, `from_vec` and `logand` are plain reducible `let`s, followed by `FStar.UInt.logand_mask`. | `pulse/Pulse.Lib.CSharp.Casts.fst:int_logand_as_uint`, verified. Relied on by `byte_mask_ff`. |
| F51 | `FStar.UIntN.shift_left` takes its shift amount as a **`UInt32.t` whatever the operand's width is**, so a shift whose amount C# writes as an `int` needs a conversion on the amount and only on the amount. | `test/pulse_facts/ConversionFacts.fst:shift_amount_width`, verified. Relied on by R13.5. |
| F52 | `FStar.UInt.logor_disjoint` needs a **positive** shift amount; at zero the lemma does not apply even though the equation still holds. A general packing lemma must exclude `0`. | `pulse/Pulse.Lib.CSharp.Casts.fst:logor_shift_disjoint`; the `m: pos` requirement was reported by the checker. |
| F53 | An SMT pattern may be placed on the **idiom** rather than on a named lemma — `[SMTPat (int32_to_uint32 (logand (uint8_to_int32 b) 255l))]` fires on the shape `(uint)(b & 0xff)` compiles to. This is how a language-level idiom is made free of annotation without the emitter knowing anything about it. | `pulse/Pulse.Lib.CSharp.Casts.fsti:byte_mask_ff_bound`, `logor_shift_disjoint`; relied on by `examples/adler32`, which needs no annotation for either idiom. |
| F54 | SharpZipLib's Adler-32 comment is **arithmetically wrong in the unsafe direction**: the true supremum of `s2` before the deferred modulo is 2 090 626 020, not the 2 090 079 800 the comment claims — larger by 546 220, because "median(s1)" approximates a triangular sum. The conclusion (`< 2^31`) survives, with 2.65% headroom rather than 2.68%. The claim about `s1` (max 1 034 520) is right. | `test/pulse_facts/ConversionFacts.fst:tri`, `tri_closed`, `adler_s2_bound`, `adler_comment_understates`, verified. |
| F55 | A `[Spec]` function's parameters are all mathematical (R4.6) whatever their C# types, but a `[Lemma]`'s binders keep the types they were declared with (R4.7). Argument coercion is therefore **not** a property of the argument alone. | The two emitted signatures differ: `Let_RingVariant_Slot` takes `(var_head: int)` from a C# `int`, `Let_Adler32_Step` takes `(var_off: I32.t)` from the same C# type. Relied on by R13.6. |
| F56 | A slot is a *binding*, and a binding introduced inside a block is out of scope once the block closes — including for R5.13's resource-naming bracket, which would otherwise assert `pts_to` for a cell whose Pulse binder no longer exists ("Identifier not found: var_n"). | Reproduced by a `Pal.Assert` placed after a loop whose body declared a local; fixed in `CodeEmitter.Scoped`. |
| F57 | A pass that analyses a body and a pass that rewrites it are **ordered**, and the analysis must see the rewritten form. R5.7 asks whether a loop body escapes, in order to decide whether the `for` step goes in the body or in its own slot; asked of the body *before* R5.14 has run, the question is answered "no" for a `continue` still sitting inside a `switch`, the step is appended to the body, and the step is then skipped on the very iterations that continue — so the measure stalls and termination fails. | Reproduced by `test/switch_stmt:Count`, whose `case 7: continue;` failed with `pow2 31 - (match … with \| true -> i+1 \| false -> i) << meas`. Fixed by asking `Escapes` of the normalized body. |
| F58 | A desugaring that introduces a binding must **splice** into its enclosing block, not nest inside a fresh one. R5.14's scrutinee binding wrapped the if/else chain in a block, and R5.5b absorbs a tail only into a chain that is a statement of the same block — so `switch (t) { case k: return e; } return d;` was rejected even though every piece of the rule was right. | Reproduced by `test/switch_stmt/SwitchVariant.cs:WeightOf` (three `PALCS0001`s). Fixed by carrying the binding in `IrSwitch` and splicing the expansion in `Normalize`. |
| F59 | Pulse's `match` **can** scrutinise a machine integer, since FStarLang/FStar#4374 (merged 2026-08-02); before it, `0l` in pattern position was read as a `Prims.int` and rejected against an `Int32.t` scrutinee. But an arm's hypothesis is just the equality `I32.v k == 0` — a machine integer is not an inductive type, so there is no case split to be had that an `if` does not already give. | `test/pulse_facts/MatchFacts.fst:match_i32`, `match_u8`, and `match_gives_equality` beside `chain_gives_equality`, which discharge the same assertion. Requires the toolchain pinned at 2026-08-05 or later. |
| F60 | **Pulse has no or-patterns**, though F\* does. `match k { 0l \| 1l -> … }` is a syntax error, while `let f n = match n with \| 0 \| 1 -> 10 \| _ -> 1` verifies. A C# section carries a *set* of labels, so `match` can express `case 0: case 1: S; break;` only by duplicating `S` once per label, without bound. | `test/pulse_facts/MatchFacts.fst` §4 records the error (`Error 168: Syntax error`) and the disjunction that replaces it. This is what decides R5.14 against `match`. |
| F61 | **C's implicit fallthrough is what forces PAL's `hit` flag.** `pal/cpp/impl.cpp` desugars `switch` into a *sequence* of `if (!brk && (hit \|\| scrut == v))` guards with two threaded flags; C# forbids fallthrough (CS0163), so its sections are disjoint and a plain if/else chain suffices with neither flag. | Read from `pal/cpp/impl.cpp:1834`. This is why R5.14 does not import PAL's machinery, and why `goto case`/`goto default` — the one way back into fallthrough — are refused rather than approximated. |
| F62 | **`Pulse.Lib.CSharp.Array` already works at an abstract element type.** `CA.read`/`CA.write` are declared `(#t: Type0)`, so a Pulse `fn` polymorphic in `t` can call them with the type variable it was given. A generic method over `T[]` therefore needs no new library. | `test/pulse_facts/GenericFacts.fst:generic_get`, `generic_set`. This is the fact that makes generics a frontend milestone rather than a library one. |
| F63 | **A generic struct is an ordinary parameterised record.** `noeq type segment (t: Type0) = { arr: A.array t; off: I32.t; cnt: I32.t }` and a pure predicate over it both typecheck, and a Pulse `fn` over the record verifies. This is the `ArraySegment<T>` / `Span<T>` shape. | `test/pulse_facts/GenericFacts.fst:segment`, `seg_ok`, `seg_first`. `examples/adler32` had to spell `ArraySegment<byte>` out as three parameters; this is why it will not have to. |
| F64 | **Instantiation composes.** A generic `fn` may call a generic `fn` at its own type variable, with the type argument inferred exactly as a concrete one is today. So generic methods calling generic methods need no monomorphising pass. | `test/pulse_facts/GenericFacts.fst:generic_swap`, which calls `generic_get`/`generic_set` at `t`. Without it the emitter would have to specialise every instantiation, losing the module-per-method structure §2 depends on. |
| F65 | **A C# `string` needs no separation logic.** It is immutable, so there is nothing to own: it is a pure value, `Seq.seq char` is an adequate model, and a Pulse `fn` takes and returns one under `requires emp`. | `test/pulse_facts/StringFacts.fst`. Recorded as the road not taken in M8: the *encoding* is cheap, and the cost of strings is the library surface (`Substring`, `IndexOf`, `Split`, concatenation), not the model. |
| F66 | **A mutually recursive type group may be parameterised.** R10.1's record, its `box` abbreviation and its `option` abbreviation each repeat the binder, and the recursion is at the *same* type argument — which is all a C# `Node<T>` can say, since `Node<T>.next` is a `Node<T>?` and never a `Node<U>?`. | `test/pulse_facts/GenericClassFacts.fst:class_Node__raw`. |
| F67 | **A model type carries its refinement across parameterisation.** R3.9d's `[Refine]` predicate is a predicate *on the model*, so it is parameterised exactly as the model is: `class_Node__model (a: Type0) = m: list a { pred m }`. | `test/pulse_facts/GenericClassFacts.fst:class_Node__model`. |
| F68 | **A class's type parameter is *implicit* on every generated definition, and that is not a hope about inference.** Each of the twelve definitions R10.4/R10.8 emit has a value argument whose type already mentions the parameter (`x: class_Node__opt a`), so it is determined by unification with an argument the emitter writes down anyway. The payoff is that every *call site* §10 emits stays character for character what it already is. | `test/pulse_facts/GenericClassFacts.fst` F68–F70: `class_Node__inv_opt`, the six case lemmas and the recursive share/gather all take `(#a: Type0)`, and `func_Lists_Length` calls them with no type argument at all. |
| F69 | **A generic method over a generic class composes the two rules and needs no third.** An explicit `ty_T` binder (R14.2) applied to a class type (`class_Node__opt ty_T`), with the class's own lemmas inferring `a` from it. | `test/pulse_facts/GenericClassFacts.fst:func_Lists_Length`. |
| F70 | **A probe written outside the emitter's idiom measures the probe.** The first draft of F69 failed with "Application of a stateful or atomic computation cannot have a ghost effect"; a control at a *fixed* element type failed identically, and both succeeded once rewritten in R10.7's actual shape — an `erased` model with `requires`/`ensures` spelled out rather than `preserves`. Generics were never involved. | `test/pulse_facts/GenericClassFacts.fst:ctrl_Length`, kept beside `func_Lists_Length` as the control. |
| F71 | **The part of a structure a loop has walked is a function of the loop counter.** So it can be named by a total function (`Take`/`Drop`; `Ctx`/`Sub`) rather than accumulated in a ghost variable, and closing it at the end is an ordinary lemma about the user's segment predicate — not the magic wand §10.7 refused for. | `test/pulse_facts/CursorFacts.fst`, `test/pulse_facts/TreeCursorFacts.fst:knot_find`, verified. Relied on by §16. |
| F72 | **A branching cursor needs no more loop machinery than a linear one.** A *search* path is determined by the tree and the key, both fixed for the loop, so a one-hole context is as much a function of the counter as a prefix is. The context lemmas recurse on the **tree** (`decreases t`), which keeps the counter an unrefined `int`. | `test/pulse_facts/TreeCursorFacts.fst:dsub`, `dctx`, `path_append`, `path_close`. |
| F73 | **An `exists*` binder that appears only inside `pure` can never be solved.** Pulse's matcher recovers a binder from the `pts_to`s it unifies; folding a predicate whose existential has no resource to be recovered from fails with "Cannot check relation with uvars". This is what decides whether a predicate may hide a machine value (R16.3). | Reproduced while writing `TreeCursorFacts.knot_open`; resolved by the explicit-field-plus-wrapper shape now in `KnotPath.fst`. |
| F74 | **Pulse cannot disambiguate two conjuncts of one predicate whose only difference is a pointer just read from the heap.** The fix is definitional, not a lemma: make each conjunct's model half a total projection (`subl`/`subr`) of a model the invariant already names (R16.2). | Reproduced in `TreeCursorFacts.knot_open`; the projections are in `KnotPath.fst`. |
| F75 | **A Pulse `let mut` needs a postcondition at the end of its scope.** A field read inside the non-null branch of a test binds a cell, so the same branch is typable as a method's tail and untypable one statement short of it — which is why a loop body's last statement must be emitted in tail position (R5.8d). | Diagnosed by hand-editing `test/tree_cursor/out/Func_Search_Find.fst`: removing the *outer* trailing `()` was the change that mattered. |
| F76 | **A Pulse `box` is already a nullable pointer.** `Pulse.Lib.Box` exports `null`, `is_null (r: box a) : b:bool{b <==> r == null}` and `pts_to_not_null`. So `option (box …)` is a *second* nullability layer over one that already exists, and its entire content is the two coercions R10.2b/R10.2c used to describe. Replacing it with a refinement (`class_C = b: class_C__opt { not (B.is_null b) }`) makes both coercions the identity text, deletes a `pure`-trapped existential from every recursive invariant (cf. F73), and lets each user-written cursor lemma take its cursor once instead of twice. | `test/pulse_facts/NullFacts.fst` N1–N7, verified; `tools/fstar/lib/fstar/pulse/pulse/lib/Pulse.Lib.Box.fsti:33,35,108`. Relied on by R10.2, R10.2b, R10.2c, R10.2d. |
| F77 | **Pulse does not see through an ordinary `let` when matching resources.** `class_C__inv this p m` and `class_C__inv_opt this p m` are the same term after delta, but a goal stated with one is not found in a context holding the other; an explicit `rewrite … as …` is required. This is why R10.2b being the identity *conversion* still leaves `class_C__as_opt` and `class_C__intro` in place as one-line rewrite lemmas rather than deleting them. | Reproduced in `test/pulse_facts/NullFacts.fst` while writing `inv_share`/`inv_gather_gen`. |
| F78 | **`Pulse.Lib.Slice` is the `Span<T>` shape, and the whole of what is missing is on the C# side.** A `slice t` is a first-class value with a non-ghost `len`, a `pts_to` over its contents, `split`/`join`, `subslice` with a `subslice_rest` residue, `share`/`gather`, `copy`, and an `is_from_array` provenance token. Returning a subslice is *derivable* from the two `is_split`s `subslice_rest` is defined over — no library request is needed. What is not derivable is knowing *where in a C# program* the split and the join happen. | `test/pulse_facts/SliceFacts.fst` S1–S6, verified; `tools/fstar/lib/fstar/pulse/pulse/lib/Pulse.Lib.Slice.fsti`. Relied on by R17.1 and R17.5. |
| F79 | **A span value may be copied; the span's resource may not.** After `var t = s;` there is still exactly one `pts_to`, so a write through either name is a write to the memory both describe. This is precisely the duplication `PALCS0511` refuses a struct with a reference-typed field (§3.4) — and a `Span<T>` *is* such a struct. So a span cannot go through §3's struct rules; it has to be a **slot kind**, like `T[]`. | `test/pulse_facts/SliceFacts.fst:s4_copy_is_alias`. Note the `rewrite` the probe needs to move the resource between the two names: F77 again, and it is why the aliasing is invisible to Pulse's matcher unless the translation makes it explicit. |
| F80 | **`give_back w` recovers everything by unification.** A ghost operation whose only explicit argument is the window recovers the parent, the permission, the bounds and both contents from the receipt sitting in the context. This is what lets `Pal.Restore(w)` be a one-argument surface intrinsic (R17.6) rather than something that has to restate what was borrowed. | `test/pulse_facts/SliceFacts.fst:s8_restore_by_unification`, verified. Relied on by R17.6. |
| F81 | **A receipt may not be indexed by `SZ.t` if its bounds are `exists*`-bound.** `Pulse.Lib.Slice.subslice_rest` carries the refinement `SZ.v i <= SZ.v j /\ SZ.v j <= Seq.length v`, which cannot be discharged for bounds bound by an existential — the receipt fails to typecheck. Putting the refinement in a `pure` *inside* the `exists*` does not help: it is not available where `subslice_rest` is typed. The fix is to inline `subslice_rest` into a predicate indexed by `nat`, moving the refinement onto that predicate's own binder. | `pulse/Pulse.Lib.CSharp.Span.fst`'s internal `rest`; found while writing `is_range_of`. Relied on by R17.5. |
| F82 | **A `fold` does not normalise its indices.** `fold (rest s w p (I32.v i) …)` fails against a context holding `rest s w p (SZ.v lo) …` even where `SZ.v lo == I32.v i` is known to SMT; an explicit `rewrite … as …` first is required. F77 in a second guise, and the reason the library's borrow operations are written with a `rewrite` before each `fold`. | `pulse/Pulse.Lib.CSharp.Span.fst`, `intro_rest`. |
| F83 | **A pure lemma must be called before the resource step it supports, not after.** `splice_same v i j; restore_range w;` verifies; the reverse order does not — the resource match happens first and has already failed by the time the lemma runs. Erased arguments must be passed `(reveal v)` explicitly. | `test/pulse_facts/SliceFacts.fst:s9_read_only_trip`. |

F1 and F8 together **retire** the plan's original top risk: no `cont`-flag rotation and no
auto-generated short-circuit invariants are needed. F2 introduces a new obligation
(R5.9). F6 and F7 are constraints on the *library*, not on the emitter, and are the reason
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
| `abstract class C` | `Class_C.fsti` (what a subclass and a client may use) and `Class_C.fst` (the encoding — R9.17) |
| `sealed class C : P` | `Class_C.fst`, plus `Vtbl_C.fsti` / `Vtbl_C.fst` for its vtable and casts |
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

**R2.1a (overloads).** C# also lets *one* type declare `Abs` twice. Where the type
qualifier is added always, the signature is added **only to an overload set** — a member
whose `⟦name⟧` is shared by another member of the same type takes a suffix built from its
parameter types, `_`-joined, an empty list rendering `_unit`:

| C# | module |
|---|---|
| `class Over { int Id(int a); }` | `Func_Over_Id` |
| `class Over { int Id(int); int Id(int,int); }` | `Func_Over_Id_int`, `Func_Over_Id_int_int` |
| `class Box { Box(int); Box(); }` | `Func_Box__ctor_int`, `Func_Box__ctor_unit` |

The two halves of the rule are asymmetric on purpose, and the asymmetry follows from what
each protects against. The type qualifier guards against a collision an author cannot see —
`Abs` in another class, written by someone else — so it must not depend on whether that
other class exists. A signature suffix guards against a collision the author is looking
directly at, in one type, and the edit that introduces it is an edit to that very
declaration. Suffixing always would pay for that with `Func_Counter_Get_unit` throughout
every program that has no overload at all, and readable generated Pulse is the property
§2 exists to protect.

Constructors are why the rule is needed rather than merely nice. A method can be renamed
by its author; `.ctor` cannot, so without R2.1a a class may declare exactly one
constructor. That was the state before this rule, and it was not enforced — it *crashed*,
in `SpecBinder`, before any check ran. Which is R18.3 again: **the first pass that reduces
two declarations to one name must be the one that reports it.** Both places that key a
dictionary by this name now tolerate a duplicate and let `PALCS0501` report it, so a
sanitisation that happens to collide (`A.B` and `A_B` reach the same token) is a
diagnostic rather than a stack trace.

The set is computed over *definitions*. A call to `Exchange<int>` presents Roslyn a
constructed symbol which is not equal to the `Exchange<T>` in the type's members, so a
generic method compared naively is an overload of itself — and R15.1 says a generic method
emits one module for all its instantiations, so the suffix would name a module nothing
generates. The suffix is likewise built from the definition's parameter types, which is
what makes `Exchange<int>` and `Exchange<byte>` agree on it.

A parameter type becomes a token by taking its C# spelling and replacing everything that
is not an identifier character with `_`: `int` is `int`, `Span<int>` is `Span_int_`,
`int[]` is `int__`. The tokens are not meant to be pretty, only stable, injective in
practice, and derived from what the author wrote — R2.1's "a pure function of the source
name" applies to the suffix too.

**R2.2 (provenance).** Every emitted construct records the Roslyn `Location` it came from,
written to `source_range_info.json` as
`{module, file, construct, source: {file, range}}`. A module whose whole text is the
user's own Pulse (`[assembly: IncludePulse]`) records the single construct `"*"`.

`test/provenance-lint.sh` reads the generated `.fst` and `.fsti` files — not the compiler's
account of what it did — extracts every top-level `fn`, `let`, `let rec`, `val` and `type`,
and requires each to
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

**R2.4 (the output directory is the translation, not a log of translations).** The set of
`.fst`/`.fsti` files in `-o` after a run is exactly the set R2.1 names for this program.
A module the previous run wrote and this one does not is deleted.

Write-if-changed, which R2.1's naming makes possible and which keeps F*'s checked-file
cache warm, has a failure mode if it is the *only* rule: rename `Shape.Area` to
`Shape.GetArea` and `Func_Shape_Area.fst` stays on disk forever, still listed by the
directory's `Makefile` glob, still verified, still failing — and it fails against a C#
declaration that no longer exists, so there is nothing to fix and no way to see why. The
same thing happens whenever a rule *stops* emitting a module, which is how this was found:
R9.20's collector briefly claimed R9.6's overrides, and the modules it wrote for them
outlived the fix and were caught by the provenance lint, which asks precisely "did any C#
ask for this?".

The other half of the rule is that **the same input emits the same bytes**. That is not
free: the emitter's slot table was an `ImmutableDictionary`, which enumerates in hash order,
and .NET randomizes string hashing per process — so the order the locals were named in a
`with va_5 vindex_6. assert (…)` line differed between runs of the same file, and
write-if-changed rewrote and F* re-verified a module that had not changed, at random, in
about one run in three. The fix is to enumerate in declaration order. The general form of
the rule is worth stating because the same trap is available anywhere in the emitter: **a
hash-ordered collection may be used for lookup and never for emission.**

Pruning is unconditional, including when translation had errors. `TranslationErrors.fst`
already makes an errored output fail, so there is no state worth preserving across a failed
run, and a rule that pruned only on success would leave exactly the case that motivates the
rule — a rename that also introduced an error — behaving as before. Only files matching
R2.1's extensions are removed; `_cache/`, `diagnostics.json` and the two maps are the
tool's own and are left alone.

---

## 3. Types

**R3.1 (scalars).** `bool→bool`, `int→Int32.t`, `uint→UInt32.t`, `long→Int64.t`,
`ulong→UInt64.t`, `byte→UInt8.t`, `sbyte→Int8.t`, `short→Int16.t`, `ushort→UInt16.t`,
`char→UInt16.t`, `nint→PtrdiffT.t`, `nuint→SizeT.t`. `SpecInt→int`, `SpecNat→nat`,
`Seq<T>→Seq.seq ⟦T⟧`, `SlProp→slprop`. `float`/`double` are rejected (§8.5).

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
  Rejected as PALCS0511; see §8.5.

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

**R4.6 (`[Spec]` methods).** A `[Spec]` method is pure, ghost, and
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

The `unfold`/`fold` bracket is the window in which R3.10's invariant may be broken.

**R4.10c — the bracket is opened if and only if the body names a field of the receiver,
and a body that names one may not also call a method on it (`PALCS0597`).** The bracket
used to be emitted unconditionally, on the §0 rule 2 argument that a uniform shape is
better than a conditional one. That argument was wrong here, because the two things a body
can do with its receiver want *opposite* states:

| the body | wants the invariant |
|---|---|
| reads or writes a field | unfolded — the fields are behind it |
| calls a method on `this` | folded — that is what the callee's contract requires |

A body that only delegates (`int Again() => Get();`, or R9.20's `int Width() => Span;`)
therefore had its receiver opened and then handed a representation to a function expecting
an invariant. That is ill-typed Pulse, emitted with `0 error(s)`. Opening only when a field
is named fixes it, and makes true what this section had always claimed: the bracket goes
where the field accesses are.

A refusal was retired by this rule, which is worth recording because the reasoning that
justified it was correct and the conclusion was still wrong. `test/pulse_refusals` held a
case in which `IncrementTwice` calls `Increment` twice on `this`, and its comment argued
that the frontend should *not* rule on it: the frontend cannot see the prover's context,
Pulse can, and a refusal invented by the checker is as bad as a proof step invented by the
emitter (§0 rule 3, pointed the other way). All of that is true. But the premise underneath
it — that the invariant is open there — was not a fact about separation logic, it was a fact
about this emitter, and the emitter was wrong. The case verifies now, unchanged, and lives
in `test/counter_class`. **When a refusal is justified by what the prover cannot do, check
first that the prover was asked the right question.**

The mixed case cannot be fixed the same way, and is refused rather than approximated.
Closing the bracket around the call and reopening it after would be a proof step the
emitter invented: R4.11a's `fold` must hold of the state at the fold point, and R3.10's
`Shift` is the standing counterexample — its invariant is *false* between its two
assignments, which is the whole reason the bracket exists. §0 rule 3 says the fix belongs
in the annotations, and here it is a small one: read the field through the method, or
inline the callee.

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

**R4.11c (`Assigned` is not `Mutated`).** The same three-part test answers a second
question — *which objects in a body have moved by the time the postcondition is stated*, and
which of a loop's objects R5.8b may hold fixed — and it must be the one that answers it.
The tempting shortcut is `Normalize.Assigned`, which is already there; but `Assigned`
answers R4.2, "which names need a mutable cell", where saying yes too often costs a
`let mut` and nothing else. Here it costs the *model*: an object wrongly called mutable is
re-quantified, and a postcondition like `Result == a.TheArea + b.TheArea` becomes
unstateable at the very call site that needs it. The rule therefore lives in exactly one
place, `Normalize.Mutated`, and `Assigned` is never used to answer it. Note also that
"errs strict" reverses here: for a *loop*, holding an object fixed is the strong reading,
so the two consumers need the same precise answer for opposite reasons.

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

The rule is not the constructor's, it is *the class-typed return's* — R9.15d — and the
constructor is its first instance. Any method whose return type is a class owns the
returned object in its postcondition, existentially at its model; the constructor differs
only in binding that model to `this`, which is what lets its `[Ensures]` read like every
other method's.

Freshness is free and needs no emitter work: the frame rule gives every caller
`frame ** class_C__inv x m₀`, so a newly constructed object is automatically separate from
everything that already existed.

**R4.12c (chaining).** `C(…) : this(args)` **is** the call `ctor_C_sig(args)`, and the
chaining constructor's whole body is that call:

```
fn func_Box__ctor_unit ()
  requires emp
  returns  x : class_Box
  ensures  exists* m. class_Box__inv x m ** pure ⟦Q⟧
{
  let t0 = func_Box__ctor_int 0l;
  t0
}
```

There is no new rule here, which is the point: R9.15d already says a method returning a
class owns the returned object at an existential model, and a chaining constructor is such
a method whose body is one call. The chaining constructor's own `[Ensures]` is then
discharged from the chained one's, by Pulse, from the contract alone — so a convenience
overload is checked against the general constructor rather than re-proved.

**Only when nothing follows the call (`PALCS0598`).** `C() : this(0) { extra = 1; }` is
refused. The chained constructor returns the object with its invariant already established,
so an assignment after it needs the representation back, and R4.10c's argument applies
unchanged: this constructor is not the one that closed the bracket, and reopening an
invariant it never established would be the emitter choosing an unfold point on the user's
behalf. The fix is in the source and it is small — chain to a constructor that does the
work, or assign every field here.

`: base(...)` is a separate question and waits on a base class that has fields at all
(§8.6, and R9.2 is why).

**R4.12d (field initialisers).** `private int x = 7;` **is** the assignment `this.x = 7;`
placed at the head of the constructor, ahead of its body. That is where C# runs it, so
R4.12 continues to read one list of assignments and needs no case of its own; a field the
initialiser sets and the body sets again is set twice in that order, and the second wins,
because assignments are sequential and nothing here made them otherwise.

It runs in exactly the constructors C# runs it in — those that do **not** chain with
`: this(...)`. That is not a choice either: a chaining constructor's initialisers ran in
the constructor it chained to, and running them again would build a representation twice.
R4.12c's shape already says so, since a chaining constructor's body is a call and has no
allocation in it at all.

**R4.12b (a constructor consumes its object parameters).** A constructor body may only
initialise fields (R4.12), so an object it is *given* has nowhere to go except into the
representation it is building. Ownership therefore moves, whether or not the author wrote
`[Consumes]`, and the rule is read off the shape of a constructor rather than off an
annotation. Keeping the argument's invariant in the postcondition would ask the caller to
own the same object twice.

**R4.9c/R4.12b on the calling side.** The two ends have to agree, or the resource is owned
twice or not at all, so consumption is one predicate over `(method, parameter)` consulted by
both. At a call site, an argument at a consumed position stops being owned: it is not folded
back by R4.14, and it may not be handed to anything else. C# would leave the name usable —
the reference is still there — so a later use is **PALCS0550**, reported against the second
use rather than left to surface as an unprovable resource in generated Pulse.

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

For an **object**, "assigned" is R4.11c's question, not `Assigned`'s: a loop that only
*reads* an object through a read-only method holds its model fixed. The same shape, one
level up, as the defect R4.11c describes — a loop that dispatches a reader on a shape it
was handed must still be able to return that shape to its caller with the model the caller
named.

**R5.8c (an invariant that owns).** A `Pal.Invariant` clause is sorted by exactly the test
R12.2 applies to a contract: a clause of type `SlProp` is a **resource** and joins the
`pts_to`s; anything else is a proposition and joins the single `pure`. There is no third
case and no analysis of what the clause says.

The rule is small and it is what makes a *cursor* expressible. R5.8's inference computes the
ownership of the loop's **locals**; it has nothing to say about the part of a heap data
structure the loop is standing in the middle of, because that is not a function of the
body's free variables — it is a function of the loop counter. Without R5.8c an invariant
could state facts about values only, and every iterative traversal would stay out of reach
whatever the library offered.

**R5.8d (the last statement of a loop body is in tail position).** Exactly as the last
statement of a method body is. A `let mut` in Pulse needs a postcondition at the end of its
scope, and it has one only where that scope ends in a construct carrying an annotation; an
`if` terminated by `()` is not such a construct, so a `let mut` inside either of its
branches is rejected with *"Allocating a mutable local variable expects an annotated
post-condition"*. Since §12 asks every cursor loop to read fields inside the non-null branch
of a test, and a field read binds a cell, the same body was typable as a method's tail and
untypable as a loop's.

The rule recurses through blocks and two-armed `if`s, so a nest of them is a nest of tails.
Two exclusions, both principled rather than incidental:

* a null test that opens a §10 window is **not** a tail, because the window's closing lemma
  is emitted on the non-tail path — moving it would be a change to R10.7, not to where a
  block ends;
* a loop with a `for` step, a `break` flag or a `continue` flag is **not** a tail, because
  in each of those the body is followed by something.

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

**R5.14 (`switch` becomes an if/else chain).** Like R5.7's `for`, a `switch` is lowered
intact and desugared by Normalize, so the rewrite is one rule applied uniformly rather
than a shape the frontend recognises:

```csharp
switch (e) {                       {
  case k1:                             var t = e;             // once
  case k2: S1; break;          ==>     if (t == k1 || t == k2) { S1 }
  case k3: S2; break;                  else if (t == k3)      { S2 }
  default: S3; break;                  else                   { S3 }
}                                  }
```

Three things in that picture are load-bearing.

*The scrutinee is bound, always.* C# evaluates the governing expression exactly once, and
an if/else chain tests it up to *n* times. For `switch (a[i++])` the difference is
observable, so the binding is not an optimisation to be applied when it happens to matter
— it is what makes the rewrite correct. It is an immutable binding (the `Immutable` flag
R13.3 introduced), because it is written once and read many times, and because a cell
declared here would become a resource in every enclosing block.

*The `default` section moves to the end.* C# lets it be written anywhere among the
sections, and it always means "none of the others". Reordering is sound precisely because
C# requires the case labels to be *distinct constants*: no two arms of the chain can both
be taken, so the order among them carries no information. A `switch` with no `default` has
no final `else`, which is the same fallthrough-to-nothing C# gives it.

*A section's trailing `break` is dropped, and any other `break` is refused.* This is the
one place a naive desugaring is quietly wrong. Inside a `switch`, `break` means "leave the
switch"; inside a loop it means "leave the loop"; and a `switch` inside a loop has both
meanings in scope, distinguished only by which construct encloses the statement. The final
`break` of a section is the section terminator and vanishes with the section. But

```csharp
while (…) { switch (k) { case 1: if (c) break; S; break; …
```

has a `break` whose meaning *changes* under the rewrite: it left the `switch` before and
would leave the `while` after. There is no if/else chain that expresses it — the chain has
no construct to break out of — so it is rejected (PALCS0577) rather than mistranslated.
`continue` needs no such care: it targets the enclosing loop both before and after.

The rest is refusal, and each refusal is a construct with no meaning in the chain rather
than one that is merely unimplemented. Pattern labels and `when` guards (`case int x:`,
`case > 0:`) are rejected: they bind and test rather than compare, and R5.14 is a rule
about equality against constants. `goto case` and `goto default` are rejected as the
arbitrary control flow they are. A section that does not end in `break`, `return` or
`continue` cannot occur — C# itself forbids the fallthrough — and stacked labels
(`case k1: case k2:`) are one section with two labels in Roslyn's tree already, which is
why they need no rule of their own beyond the disjunction above.

What this rule does *not* do is give the solver a case analysis it did not have.
`if (t == k1) … else if (t == k2) …` is exactly the term structure a hand-written chain
would produce, so a proof about a `switch` costs what the same proof about the chain
costs. That is the intended outcome: `switch` is a notation, and R5.14 says it is only a
notation.

The variant test (§7.2) earned its keep twice here, and neither finding was about
`switch`. Both were about *where* the rewrite sits among the rules that were already
there.

* **A rewrite must run before anything that analyses what it produces (F57).** R5.7 asks
  whether a loop body escapes, to decide whether the `for` step belongs in the body or in
  its own slot. Asked before R5.14 has run, it does not see a `continue` still inside a
  `switch`, appends the step to the body, and the step is then skipped on exactly the
  iterations that continue — so the counter stalls and *termination* fails. The symptom is
  a failed measure, four rules away from the cause.
* **A rewrite that introduces a binding must splice, not nest (F58).** The scrutinee
  binding wrapped the chain in a block, and R5.5b absorbs a tail only into a chain that is
  a statement of the *same* block. So a `switch` whose sections `return` was rejected with
  every piece of R5.14 correct. Fixing it generalised R5.5b, which previously absorbed
  only into an `if` with no `else` and now absorbs into a chain of guards — a shape a
  hand-written program can have too, and which it had been silently refusing.

Neither fix is a special case for `switch`: one is an ordering constraint between two
existing passes, the other a rule that was too narrow. That is §0 rule 3 working as
intended — the cost of a new construct is paid in the general rules or not at all.

### Why not a Pulse `match`?

Because a C# `switch` looks like one, and structure-preserving is what §0 asks for, this
is the first question to ask about R5.14 — so it is worth saying what the answer rests on,
which has changed once already.

When R5.14 was written the answer was that Pulse could not do it: `0l` in pattern position
was read as a `Prims.int` and rejected against an `Int32.t` scrutinee. A chain was not
chosen over `match`, it was the only target there was. FStarLang/FStar#4374 (merged
2026-08-02) fixed that, and `test/pulse_facts/MatchFacts.fst` now verifies a Pulse `match`
on `Int32.t` and `UInt8.t` literals. So the question is live, and the chain has to be
argued for rather than assumed.

**It loses on one point, and that point is decisive: Pulse has no or-patterns (F60).**
A C# section carries a *set* of labels —

```csharp
case 0:
case 1:
    S;
    break;
```

is one section with two labels, not two sections. `match` can only express it by
duplicating `S` once per label, and nothing bounds the number of labels. `S` is the user's
code: their `Pal.Assert`s, their lemma calls, their loops. Duplicating it duplicates proof
obligations they wrote once, and reports each failure twice against the same C# span.
`t == k1 || t == k2` is one branch, of any width, at no cost. (F\* itself has or-patterns,
so this is a property of Pulse's `match` and may not be permanent.)

**And it wins nothing to set against that.** The intuition that a `match` gives the solver
a case analysis a chain does not is wrong here: a machine integer is not an inductive type,
so an arm's hypothesis is exactly the equality `I32.v k == 0` that the `if` branch already
supplies (F59). `MatchFacts.fst` discharges the same assertion both ways to make the point
checkable rather than plausible. The other candidate advantages are smaller than they
look. `match` would evaluate the scrutinee once natively, saving the binding — but the
binding is one immutable `let`, and it is what makes the *rewrite* obviously correct.
Pulse would check exhaustiveness — but C# has already done that, and a `switch` with no
`default` is not an error in C# and must not become one here. `default` would still need
hoisting, because match arms are ordered too.

So: the chain, until Pulse has or-patterns. That is the condition to re-open this on, and
it is a fact about Pulse rather than a preference — which is the point of writing it down
here instead of leaving it as a decision nobody recorded.

### What C# rules out, and what PAL has to do about it

The rewrite above is only as simple as it is because **C# forbids implicit fallthrough**
(CS0163). Every section is entered exactly one way — by matching one of its own labels —
so the sections are disjoint and an if/else chain, whose arms are disjoint too, is a
faithful target.

PAL translates C, which has no such rule, and the difference is visible in the shape of
its desugaring. `pal/cpp/impl.cpp` reads:

```
// Desugar: switch (scrutinee) { case v1: s1; case v2: s2; default: sd }
//      --> let scrut = scrutinee;
//          bool hit = false; bool brk = false;
//          if (!brk && (hit || scrut == v1)) { hit = true; s1 }
//          if (!brk && (hit || scrut == v2)) { hit = true; s2 }
//          if (!brk) { sd }
// break inside case bodies sets brk = true.
```

Three of those pieces exist for fallthrough. `hit` is a flag that makes a section run
because an *earlier* one did; the arms are a sequence of independent `if`s rather than a
chain, because more than one may run; and `brk` is a real variable rather than a
structural exit, because `break` has to stop that sequence part-way. pal-csharp needs none
of it: the scrutinee binding is shared, and everything else falls away. That is a language
difference doing real work, not a difference in ambition — and it is worth naming, because
"how does PAL do it?" would otherwise import machinery for a case that cannot arise.

`goto case` and `goto default` are the exception C# leaves open, and they ask for precisely
what the chain cannot express: entry into one arm from inside another. They are refused,
with a message naming the two honest rewrites — stack the labels when the other section
should run *instead*, factor out a method when it should run *as well*
(`test/diagnostics/cases/GotoCaseFallthrough.cs`). Approximating them would mean adopting
PAL's `hit` flag for the one construct C# already discourages.

One further thing PAL needs and pal-csharp does not: a **join contract**. Its
`switch_stmt.c` carries `switch (x) _ensures(_live(x) && _live(result))` — an annotation
at the point where the arms rejoin, because the desugaring's arms are a *sequence* and
the resources have to be re-established between them. A chain has a structural join, which
Pulse's `if` already types, so there is nothing for the user to write.

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
C's, so the scheme fixes:

| Construct | C# runtime behaviour | Obligation |
|---|---|---|
| `x + y`, `x * y`, … | wraps (`unchecked`, default) | **no overflow** |
| `a[i]` | throws `IndexOutOfRangeException` | `0 <= i < a.Length` |
| `x / y`, `x % y` | throws `DivideByZeroException` | `y != 0` |
| `o.f` | throws `NullReferenceException` | `o != null` |

A verified program therefore **throws no exception**; `try`/`catch`/`throw` are rejected. The
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

## 7. Worked derivation, and the detectors

### 7.1 A loop, derived rule by rule

The inner loop of insertion sort. Note that nothing below is a choice: each line cites the
rule that produced it.

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

### 7.2 The two mechanical detectors

A derivation like §7.1 is a claim about one program. Two checks, run by `make`, are what
stop the scheme from quietly becoming a collection of per-example accommodations.

**The variant test.** Every acceptance directory ships a *second, independently worded*
implementation of the same contract, and it must verify **with no translator change**. The
variant is written to differ in every way that should not matter: `for` against `while`,
inverted branches, renamed and reordered members, `++` against `x = x + 1`, an index
computed rather than carried, a list or tree written at the *opposite null-test polarity*.
It is deliberately not a paraphrase — a variant that merely renames locals detects nothing.
This is the single most effective detector of example-fitted output, and it earns its keep
in both directions: several rules exist only because a variant found them missing (R4.14b,
F57, F58), and several apparent translator bugs turned out on inspection to be real defects
in the hand-written variant, caught by an obligation the scheme already emitted.

**The provenance lint.** `provenance-lint.sh` (R2.2) requires every top-level construct in
every generated module to trace back to a C# source span through
`source_range_info.json`. A construct with no provenance was invented by the emitter, and
under Rule 3 an invented construct must either be justified as a scheme rule or removed.

The other four lints (§8.2) check the tree rather than the scheme.

---

## 8. What is delivered

The rules above are the scheme. This section says which of them are implemented, what the
test suite asserts about them, and what is not done — in that order. It is not a changelog:
where a finding is already stated as a rule it is not restated here, and where a decision
was later reversed the reversal is recorded at the rule, not here.

### 8.1 The milestone map

Each milestone delivered a section of this document, an acceptance directory, and an
independently written variant of it (§7.2). None required a change to an earlier rule
except where noted at that rule.

| | Delivered | Section | Acceptance |
|---|---|---|---|
| M1 | Methods, contracts, statements, expressions, arrays, structs | §2–§7 | `swap` … `circular_buffer`, `insertion_sort_sorted` |
| M2 | `sealed` classes: a model, an invariant, instance methods, ownership of arrays and of other objects | §3.4, §4.5 | `counter_class`, `stack_class`, `ring_class`, `nested_class`, `deep_class`, `account_class`, `bag_class`, `interval_class` |
| M3 | Inheritance: abstract classes, virtual dispatch, upcast, checked downcast, depth *n* | §9 | `shape_hierarchy`, `deep_hierarchy` |
| M4 | Recursive data structures: linked lists, binary trees, back pointers | §10 | `linked_list`, `binary_tree` |
| M5 | User-defined specification types | §11 | `user_spec_type` |
| M6 | User-defined ownership predicates (`[Plain]`, `SlProp`) | §12 | `dll_segment` |
| M7 | Numeric conversions, side effects, and a production case study | §13 | `examples/adler32` |
| M8 | Unconstrained generics | §14 | `type_param` |
| M9 | Generic types, and generic list and tree libraries | §15 | `generic_list`, `generic_tree` |
| M10 | Separate Pulse files and typed ghost lemmas for user predicates | §12.5 | `dll_segment` |
| M11 | Cursors: iterative traversal of a linked structure | §16 | `list_cursor`, `tree_cursor` |
| M12 | `null` as a pointer rather than a wrapper | §10.2 | `linked_list`, `binary_tree` |
| M13 | `Span<T>` as a borrowed window | §17 | `array_view` |

`switch` (R5.14) arrived between M7 and M8 and has its own directory, `switch_stmt`.

### 8.2 What the suite asserts

Verification tests are the smaller half. Each of the following asserts something a
verification test cannot.

* **The variant tests (§7.2)** are the contortion detector, and every acceptance directory
  ships one.
* **`test/diagnostics`** is the negative suite: 54 cases, each headed by the diagnostic it
  must produce, each required to exit non-zero, poison `TranslationErrors.fst`, and carry a
  span in the user's own file rather than in generated Pulse.
* **`test/pulse_refusals`** is the suite that became possible once refusing was *not* the
  answer (R3.13): programs that translate cleanly, fail in F\*, and must fail for the
  stated reason on the marked line. Aliasing, a self-call with the invariant unfolded, and
  ownership transfer into a field — the last two had been documented here for milestones
  without ever being executed, because there was nowhere to put a test whose expected
  outcome was a proof failure.
* **Six lints** run in the same `make`: `no-example-names.sh` forbids any acceptance
  directory or method name from appearing in `Pal.Compiler`; `provenance-lint.sh` (R2.2)
  requires every top-level construct in every generated module to trace to a C# span;
  `diagnostic-ids.sh` keeps the analyzer's declared ids in step with the passes that raise
  them; `fst-configs.sh` and `cs-projects.sh` keep the editor's view of the tree in step
  with the build's; `ide-build.sh` requires every test project to compile clean *with the
  analyzer loaded*.
* **Every test directory compiles as stock C#.** `test/build-cs.sh` synthesises a plain
  project — deliberately not one that loads pal-csharp's analyzer, since a project that did
  would no longer be checking the thing that matters. This is the core invariant asserted
  against the C# compiler rather than against a document.

### 8.3 Findings that are not rules

Recorded here because they generalise and have nowhere else to live.

* **A `[Spec]` predicate used in a loop invariant must be total.** A `[Requires]` on a
  `[Spec]` predicate becomes a refinement on its last binder (R4.6), and that refinement
  must then be discharged wherever the predicate appears — including at invariant
  *establishment*, where the counter is often out of range (`i = 1` on an empty array). So
  `Sorted`, `AllAbove` and `Dominated` take no `[Requires]`; the index bounds go into the
  quantifier's antecedent, from which well-typedness of `s[i]` follows. This is the single
  most common cause of a failed invariant that looks like a prover problem and is not.
* **Pulse matches resources syntactically, which constrains the emitter twice.** A local
  that owns something is initialised *into its own binder* rather than aliasing a temporary
  (F77; R12.4 for allocation, R17.5 for a span borrow). And only the *receiver* of a
  class's own methods is unfolded — an object that merely passes through stays folded,
  because every function taking it expects its invariant and not its representation.
* **An analyzer must run the emitter too.** Stopping at the checker looks right, since an
  editor has no business writing files, but eight of the diagnostics — R5.3's unbridgeable
  type, F3's measure over an existential, an unsupported specification term — are only
  discovered while emitting. An analyzer reporting the rest would be worse than none: it
  would tell a user who had cleared every squiggle that the program was ready, and the
  build would disagree. Parity is cheap, because emission is string building over an IR
  already in hand; the output is thrown away.

  The gap was found by wiring, not by `test/analyzer`, which is the more useful lesson: a
  hand-picked case set is exactly what fails to notice a whole pass going unrun. The test
  now requires every directory of `Pal.Compiler` that raises an id to be represented among
  its cases.
* **What Pulse said must arrive, not be recomputed.** An analyzer cannot run a prover, but
  it can read the last answer, and Roslyn has a sanctioned way to depend on a file:
  `AdditionalFiles`, which it tracks and re-runs analysis over. `palcs report` writes
  `verification.txt` (R2.3) and the analyzer reports each message at its mapped C# span. An
  analyzer that opened the file itself would read something Roslyn does not know it depends
  on, so the result would cache against a key that omits it and the squiggles would go
  quietly stale — the one failure mode worse than having none.
* **Two views of one resource are the limit** (F27): a third makes Pulse's matcher
  ambiguous, so more observers are reached by nesting share/use/gather. Relatedly, Pulse
  does not split a permission at a call site (F25), for objects or for arrays — which is
  why R4.9's claim since M1 that "the same array may be passed to two parameters at once"
  was unreachable until R5.13's `Pal.Share`/`Pal.Gather` existed.
* **A model-level fact is unreachable from inside an invariant** (F17), and fails much
  later, in an unrelated client file. `PALCS0527` refuses an `[Invariant]` clause that
  mentions no field for this reason — a diagnostic whose whole value is moving a failure to
  where it can be understood.

### 8.4 The inheritance studies: the probe record for §9

§9 is the scheme; this is what it was derived from. Before any C# surface for
`abstract`/`virtual`/`override` was proposed, the encoding was worked out **directly in
Pulse** and verified end to end: `test/pulse_facts/ShapeHierarchy.fst` is a complete
`Shape`/`Circle`/`Square` hierarchy with a heterogeneous `Shape[]`, and
`test/pulse_facts/InheritanceFacts.fst` pins the facts (F28–F34) it rests on. Every
construct carries the C# it stands for in a comment.

It is kept because §9's restrictions are only intelligible against it: each of R9.2, R9.3
and R9.4 is a refusal to translate something the studies did not probe, and this is the
record of what they did.

The encoding, in one line: a class is a **vtable record** carrying its representation
type, its invariant and its methods, and an object is that record paired with its
representation, **lowered to `Type0` through `FStar.Dyn`**.

| C# | Pulse | Cost |
|---|---|---|
| `abstract class Shape` | `t_shape`, a record of `impl: Type0`, `inv: impl -> perm -> model -> slprop`, and one field per virtual member | — |
| a `Shape` reference | `shape = FStar.Dyn.dyn`, i.e. `Type0` — so it is boxable, arrayable, and a legal field | one axiom (below) |
| `shape__inv s #p m` | `exists* o. pure (s == mkdyn o) ** o.pkg.inv o.rep p m` | — |
| `class Circle : Shape` | a concrete invariant `circle__inv` plus a packaged `t_circle` | both faces are needed |
| `Circle`'s own model | its own record, plus a pure forgetful map to `Shape`'s model | F17 one level up |
| `override int Area()` | a field of the vtable | — |
| `s.Area()` | project the slot, **let-bind it**, then apply | F31 |
| upcast `Shape s = c;` | a `ghost fn` | free at runtime, as C# requires |
| `new Circle(r)` | a *static* `fn`: allocate, fold the concrete invariant, upcast | a constructor is not a vtable slot |
| `Shape[] a` | `A.pts_to a sq ** forall+ k. shape__inv sq[k] #p ms[k]` | `Pulse.Lib.ForEvery.Range` |
| `Pal.Share(s)` / `Pal.Gather(s)` | `stt_ghost` vtable slots | ghost, so aliasing a `Shape` is free |

Five findings that the study settled, each of which would otherwise have been guessed:

1. **The model may not be fixed per hierarchy.** A subclass keeps its own model and
   supplies a pure forgetful map; the base invariant is
   `exists* cm. sub__inv c #p cm ** pure (forget cm == m)`. This is exactly R3.9's
   abstraction function, applied one level up.
2. **`share`/`gather` are not derivable from `inv`** — how a permission distributes over
   an object's parts is the implementation's business — so any hierarchy that supports
   read-only aliasing must carry them in the vtable. They can be `stt_ghost`, and a
   `ghost fn` can project the ghost package and run them, so R3.10e's aliasing story
   survives inheritance at zero runtime cost. This was the main open question and it
   resolved favourably.
3. **`gather` forces a ghost index.** Two views of one `Shape` unfold to two *separate*
   existential witnesses, related only by `s == mkdyn o1` and `s == mkdyn o2`; concluding
   `o1 == o2` is injectivity of `mkdyn`, which is Cantor-inconsistent and which
   `FStar.Dyn` therefore omits. The fix is not another axiom but an extra ghost index —
   `shape__inv_at s o p m` names the implementation package, so two views are at the same
   `o` by construction. `shape_gather_unindexed` is pinned as an `expect_failure` and
   `shape_gather_at` verifies. This also states something true: a CLR object's dynamic
   type is fixed for its lifetime. **Methods must therefore be stated at the indexed
   invariant and the plain form derived**, because a client that passes through the plain
   form loses the index and can never gather again.
4. **A mutating traversal cannot borrow.** `total_area` borrows each element with
   `range_focus` and closes the trade; `double_all` cannot, because the model changes and
   the trade will not close, so it carries two ranges and peels/appends. Both verify.
5. **`null` is a real open problem.** `new Shape[3]` fills with `default(Shape)`, of
   which no object invariant holds. The study allocates with a `null_shape` placeholder
   and immediately overwrites every slot; a C# surface needs either definite-assignment
   analysis over array initialisation or an explicit `null` model.

**The one thing assumed** is `recover`, which belongs in `Pulse.Lib.CSharp.Assumptions`
but in its own section, because unlike `SizeTFitsU32` it is a *computation*, not a
`Lemma`:

```fstar
val recover (#a: Type u#a) (#x: erased a) (d: dyn { d == mkdyn (reveal x) })
  : stt a emp (fun y -> pure (y == reveal x))
```

*The CLR object header faithfully records the dynamic type.* It is needed because
ownership is about a *particular* value: without `y == x` you hold a well-typed reference
owning nothing, and the proof does not fail conservatively — it does not go through. It
is unprovable rather than merely unstated, since `FStar.Dyn.undyn` returns in `Dv` and
`Dv` results cannot be equated in specifications (F30). Stating it in `stt` rather than
`stt_div` matters: `stt_div a emp post` is inhabited for *every* `post` (F30b, verified
by a hang), so an `stt_div` axiom would be free and worthless, and F2 already requires
every emitted `while` to carry `decreases` precisely to stay in `stt`. It does **not**
imply injectivity of `mkdyn`, because each `recover` is a separate computation — which is
why finding 3 above is a genuine constraint and not a consequence.

**Consequences, and what §9 did with them.** A class needs *both* faces — a concrete
invariant for its own methods (R4.10) and a package for its clients — and the choice had
to be **pay-as-you-go**, since a `sealed` class must keep M2's translation verbatim or the
"textually additive" property is lost. §9 is that choice, and R9.1 is where it is drawn.
The cheaper alternative was a **closed-world sum of representations** over a hierarchy
whose subclasses are all in the compilation, needing no axiom at all; it was rejected
because it supports neither separate compilation nor open extension.

The study's closing recommendation — do **interfaces first**, where there is no
representation to inherit and no `base` call to model — was not followed, and §8.6 records
why: an interface adds *multiple* implementation, which R9.8 pins as hard, and the
motivating example needs ownership in a virtual method's signature (R9.9a), which is a
separate problem again.

#### Depth three: `test/pulse_facts/DeepHierarchy.fst`

The two-level study leaves the central question of inheritance untouched, because a
leaf class is only ever a subclass. `DeepHierarchy.fst` is the same encoding taken to

    Shape
     +-- Circle
     +-- Quadrilateral            (abstract, with methods of its own)
          +-- Square
          +-- Rectangle

so that `Quadrilateral` is a subclass *and* a superclass at once: it is packaged into
its parent's vtable and is itself a vtable that further classes instantiate. It
verifies, including a heterogeneous `Shape[]` whose elements sit at two different
depths, a client written against `Quadrilateral` that names no leaf class, and an
end-to-end `demo` proving the concrete result `66`.

Three things had to change, and each is a finding.

1. **The reference is always `mkdyn`'d at the root's object record.** A dyn is made at
   exactly one witness type, so a value made at `quad__obj` can never be viewed as one
   made at `shape__obj` — that is `mkdyn` injectivity again, which finding 3 above rules
   out. An upcast therefore cannot rebuild the dyn, and `Quadrilateral` cannot have a
   reference type of its own. `quad` and `shape` are the *same* F\* value; only the
   invariant differs, which is exactly the C# semantics of a reference conversion.
2. **The root object record needs one extension point**, a single `sub: Dn.dyn` field
   that `Shape` declares and says nothing about. An intermediate class stores its own
   object record there and its own invariant says what is in it. This is what keeps the
   scheme open-world: `Shape` is compiled once and admits subclasses that do not exist
   yet, which a sum over the known subclasses would not. It hangs off the *object*, not
   the vtable, because what a descendant must recover is a vtable already applied to a
   representation — recovering a bare vtable would leave its `impl` only propositionally
   equal to `pkg.impl` and every use would need a coercion.
3. **An intermediate vtable lists every method visible at its level**, inherited ones
   included, read at *its* model — as a real vtable re-lists the slots it inherits.
   That is what lets a `Quadrilateral`-typed reference call `Area()` and keep its
   bounding box, which a client that upcast to `Shape` and back could not. The four
   inherited slots are then derived **once**, generically, by `quad_as_shape_pkg`, so
   `Square` and `Rectangle` implement the quadrilateral vtable only and get their
   `Shape` vtable for free. That derivation is what "inherits" means here.

Dispatch at level *k* costs *k* recoveries — one to reach the root object, one per
`sub` hop — and each is a cast on the same reference. F31's let-binding rule applies at
every hop.

Two further findings came out of writing it.

* **A virtual method's precondition, written at the base model, must be strong enough
  for every subclass's model.** `Shape.Double` requires `ok32 (4 * Area)`, and from that
  a quadrilateral can prove its *bounding box* doubles safely (`2*W <= 4*W*H` when
  `W, H >= 1` — the same argument `double_fits` makes for a radius), but it cannot prove
  anything about a *perimeter*: isoperimetry gives `P^2 >= 16*A` and no upper bound at
  all, so a 1-by-n rectangle has perimeter about twice its area. `Quadrilateral`'s model
  is a bounding box for exactly this reason. Where a subclass genuinely needs more, the
  base must either state the precondition abstractly (a vtable-supplied predicate over
  the representation) or expose a virtual query — `if (s.CanDouble()) s.Double();`. A C#
  surface should push users towards models whose quantities are bounded by the base's.
* **A non-virtual method of an intermediate class needs nothing new.**
  `quad_semi_perimeter` calls the virtual `Perimeter()` on its own receiver and is an
  ordinary `fn` over `quad__inv` — no vtable slot, no recovery of its own, and it works
  for subclasses written later. This is also the first place in either study where a
  method calls a virtual method on `this`, which was on the not-probed list; it is
  settled, and settled by R4.10 doing nothing special.

**An *unchecked* downcast is impossible; a *checked* one needs no new assumption.**
`§13` pins the first as `downcast_is_not_free`: holding `shape__inv s #p m` says `s` is
some root object and says nothing about whether it is a quadrilateral, because the
information was discarded by the existential when the reference was upcast, which is
what an upcast means. `§14` then supplies the second.

Be precise about what "checked" means here, because it is *not* "we prove the runtime
test succeeds". `recover` has no failure mode — it is not "test the header and maybe
fail" but "given a proof the header matches, hand back the value", its argument refined
by `d == mkdyn x`. `quad__inv_at` carries that refinement at each hop, so the cast
cannot fail; but it cannot fail because the encoding only lets you *write* the casts
whose test is redundant. A cast that might fail is not one this study proves safe, it is
one this study cannot express. That is the right stance for a verifier — a verified cast
is one that cannot throw, consistent with exception-freedom (§6) — but it is a
restriction on the source language, not a theorem about C#.

Nor is the cast free at *runtime*: depth `k` costs `k` recoveries where the CLR does one
header check. What is free is the **proof**, and the details are:

* **The precondition *is* the knowledge, and it is the ghost index `gather` already
  forced.** `quad__inv_at s qo p qm` names the object record; `downcast_square` requires
  it at `square__obj c` and returns `Square`'s own invariant plus `r == c`. This is not
  a coincidence: `gather` needs a client to know *which* implementation the two halves
  came from, and a cast needs it to know *which* implementation it is narrowing to. Both
  are satisfied by remembering rather than by testing, which is why the checked cast
  costs no axiom. A constructor that keeps the index (`new_square_at`) and one that
  forgets it (`new_square`) are the same code plus one ghost step.
* **The indexed method is the primitive and the plain one is derived.** `quad_area_at`
  dispatches; `quad_area` is `quad_area_at` composed with `quad_forget_impl`. Indexing
  therefore costs nothing in expressiveness — a client that never downcasts forgets at
  every call — and a C# emitter can generate one dispatching body per virtual method,
  not two.
* **Forgetting is irreversible even to a client that can say what it forgot.**
  `quad_remember_impl` is pinned `expect_failure`: from `quad__inv s` you get an
  anonymous `qo'` with `s == mkdyn (shape_view qo')`, and equating it with a known `qo`
  is `mkdyn` injectivity. So an upcast is a real, one-way commitment, and the C# reading
  is exact — a `Quadrilateral`-typed variable carries no static evidence of its dynamic
  type.
* **A checked cast is a chain of recoveries, one per level**, because each level's
  object record is a distinct value: `quad_rep` recovers the root object, follows `sub`
  to the quadrilateral object, and re-boxes its representation with
  `quad_box qo = mkdyn qo.qrep` so that congruence — not a `coerce_eq` across a merely
  propositional type equation — delivers the equality the final `recover` wants. The CLR
  does the whole thing with one header check; that gap is the price of erasing the
  dynamic type into `dyn`, and it is paid in casts, not in memory.
* **`is` is a proposition, and only ever a positive one.**
  `is_square qo = exists (c: square). qo == square__obj c`; `as_square` turns it back
  into the named index by classical choice, free and ghost. The negative direction is
  *not* available — `a_rectangle_is_not_a_square` is pinned `expect_failure`, since F\*
  cannot generally refute an equation between values of two abstract representation
  types. That is sound (the caller still cannot cast) and is the right shape: what makes
  a cast safe here is a positive record of the construction, never the failure of an
  attempt to disprove it.
* **A *failing* cast is still out of reach**, per the caveat above: `q as Square`
  returning `null`, or a checked cast throwing, is a runtime test whose *negative*
  answer must be trusted, and would need `recover` strengthened to report a mismatch.
  Nothing in either study needs it and it is not assumed. A C# surface therefore has a
  real choice to make — reject `as` and failing casts outright, or admit them and pay
  for the stronger axiom.

Still not probed, and still to be probed before any rule admits them — these are exactly
the restrictions R9.2, R9.3 and R9.4 impose: `base.M()`; `protected`; a class that
overrides some methods and inherits others (every class in the studies supplies a *full*
vtable, which is correct but says nothing about building one from a partial `override`
list); an `abstract` class with fields, and hence a constructor chain; a class holding a
`Shape` *field* (boxable per F29, but nested-invariant composition à la R3.10b is
untested); and a cast that may fail.

### 8.5 Not yet done

**Language constructs outside the subset.** `string` and `float`/`double`; `interface`
declarations; *constrained* type parameters (§14 delivers unconstrained ones, and §14.4
says why a constraint is a typeclass obligation rather than a syntactic one);
`IEnumerable<T>` and `foreach`; delegates and lambdas in executable position; `async`;
`goto`; `try`/`catch`/`throw`; `Memory<T>` and `ArraySegment<T>` (§17.5); `stackalloc`
(R17.7); a non-tail `return` **inside a loop** (R5.5b reaches every other position); and a
`switch` label that is a pattern or carries a `when` guard.

**Gaps in the scheme, each with its reason.**

* **A struct field must be a value** — a scalar or another translated struct. An array or
  class field is `PALCS0511`, and that is the model rather than a shortcut: a struct copy
  would duplicate ownership of the same memory. Storage travels alongside the state it
  describes. A *class* has no such restriction (R3.10a, R3.10b), which is why
  `test/stack_class` is what `test/circular_buffer` wanted to be.
* **Object abstraction is deliberately deferred.** `class_C__inv` is a *concrete*
  definition in the class's own module. Hiding it behind an `.fsti` works and needs no F\*
  `friend`, but requires a module shape the emitter does not have, and C# `private` already
  hides the representation at the source level. Available when proof performance or genuine
  information hiding demands it.
* **An object may not be allocated in a block that closes around it** (R4.14a,
  `PALCS0001`). F19 is a limitation of Pulse's inference, not of the scheme, and the
  workaround — allocate in the method's block, or in a branch that returns — is usually
  what the code wanted. `test/ring_class/RingScope.cs` covers what does work.
* **Object lifecycle is unspecified.** A class with two-phase initialisation or `Dispose`
  wants a *state*-indexed invariant, `class_C__inv this st m`, and nothing has one.
* **Reference identity** — `ReferenceEquals`, and `==` on a class — has no story. `Box`
  supports equality, but nothing relates it to the ownership discipline.
* **A field is not nameable in a spec position outside a loop or a ghost statement.**
  R5.11a and R5.12 bind `this.f` where the emitter has just named the representation; a
  `[Requires]` or `[Ensures]` reads against the model (R3.9c), which is right. There is no
  third context, and nothing has wanted one.
* **A postcondition cannot say why a loop stopped.** R5.10's break flag is internal to the
  translation, so an invariant cannot mention it, and a contract needing "the loop ran to
  completion" is unstatable — see `test/compare_elements`, whose `Equal` carries its exit
  condition in the guard for this reason. PAL's answer is a per-`break` `_ensures`, and the
  C# surface would be a `Pal.Ensures(Q)` leading a `break`.
* **`out` is modelled exactly as `ref`** — `pts_to` at both ends, not `pts_to_uninit`
  strengthening to `pts_to` — so a caller must initialise an `out` argument before the
  call. Sound, but it demands more than C# does.
* **A ghost argument determined only by the pure part of a contract cannot be passed at a
  call site** (R4.5): ghost arguments are resolved by unification, and there is no
  zero-cost C# surface for explicit implicit application.
* **Heterogeneous arrays** — an array whose element type is a base class — need §6's array
  rules to carry an object invariant per element, which the studies do in Pulse
  (`Pulse.Lib.ForEvery.Range`) but §6 has not probed.
* **A recursive user-declared spec type** whose constructor takes the type being declared
  is refused (§11); the induction is not the difficulty, the `[Model]` binding is.

**Tooling.**

* **The analyzer is not a NuGet package.** It is wired into `test/analyzer` as `Analyzer`
  items, which is enough to run and to test it, but a user must point at the built
  assemblies. A package must also carry `System.Text.Json` and `System.Memory` for a .NET
  Framework host, where they are not in the shared framework.
* **Live squiggles are per-compilation work.** The analysis is whole-program — a call needs
  its callee's contract — so it runs once per compilation and is reported per file. On the
  programs in `test/` that is milliseconds; nothing has been measured at a scale where it
  would not be.

### 8.6 What is next

Three candidates, in the order the evidence puts them. All three are on §14.4's rejection
list, and all three appear in the upstream code `examples/adler32` was ported from, whose
`Adler32 : IChecksum` needs an interface, a generic struct and a property at once.

**Constrained generics.** §14 delivers the element-agnostic part of the language —
segments, spans, copies, swaps, containers — which is what the case study wanted, and §15
delivers generic types. What is left is the *constraint*: `where T : IComparable<T>` is a
typeclass obligation, and a generic sort or an ordered container cannot be written without
it. This is the smallest of the three and unblocks the most library code.

**Interfaces.** An interface is very nearly what §9 already has: R9.2 requires an abstract
class to have no fields and R9.3 requires its virtual methods to be abstract, which is the
definition of an interface. What a C# `interface` adds is *multiple* implementation, and
R9.8 pins why that is hard — a `dyn` is made at one witness type and `mkdyn` is not
injective, so one value cannot be viewed at two unrelated roots. But the blocker for the
motivating example is elsewhere and is worth naming: `IChecksum.Update(byte[] buffer)`
takes an array, and **R9.9a restricts a virtual method to plain values**. Interfaces would
therefore deliver the declaration without delivering `IChecksum`; the real prerequisite is
ownership in a virtual method's signature, which is its own design problem.

**`IEnumerable<T>` and `foreach`.** §16's cursors are the manual form of this, and they
verify; what is missing is the surface. A `foreach` over a cursor is a loop whose invariant
mentions a position the user did not write, so the interesting question is whether R5.8's
invariants can be stated about an iterator without the user naming its state — which is
§16.5's open question, now with §17's answer available as a precedent: where a proof step
has no C# spelling, give the author one rather than inferring it.

**Strings, cheaply, whenever.** F65 records that the encoding is nearly free: a string is
immutable, so there is nothing to own, and it is a pure value under `requires emp` where an
array parameter costs a `pts_to` at both ends. Strings are not deferred because they are
hard but because the cost is not in the model at all — it is the library surface
(`Substring`, `IndexOf`, `Split`, concatenation, formatting), each item of which is an
obligation with a specification to get right.

---

## 9. Inheritance

§8.4 records two design studies — `test/pulse_facts/ShapeHierarchy.fst` (depth two) and
`test/pulse_facts/DeepHierarchy.fst` (depth three) — in which the encoding below was
probed before any of it was written down. This section turns those studies into rules.
Every construct named here appears in one of the two studies; nothing is invented.

### 9.1 What is in scope, and why the boundary is where it is

M2's class encoding (§3.4) is a `Box.box` of a record. That encoding admits no
subclassing at all: the representation type is fixed by the reference type, so a
`Shape`-typed variable would have to have *one* field layout. Dispatch needs the
representation to be existential, and that is the whole reason M3 looks different.

**R9.1 — A class is in a hierarchy iff it is `abstract`, or its base list names a
translated class.** A `sealed class` with no base list is M2 and its emission does not
change by one character. This is a genuine fork, and it is drawn by the C# declaration
rather than inferred, so a user always knows which encoding they are getting.

Three restrictions, each traceable to something the studies did *not* probe. Each is a
refusal to *translate*, not a prediction that a proof will fail (§0 rule 3):

* **R9.2 — An abstract class has no fields.** The studies give `Shape` and
  `Quadrilateral` no representation of their own; the representation is entirely the
  leaf's. A base field would make the leaf's representation an extension of the base's
  and force a constructor chain, which is on §8.4's not-probed list.
* **R9.3 — Every virtual method is `abstract`.** In both studies each leaf supplies a
  *full* vtable. A `virtual` method with a body would have to be inherited by a subclass
  that does not override it, and a base method body can only run against a
  representation the base does not have. `base.M()` is refused for the same reason.
* **R9.4 — A leaf is `sealed`.** A non-sealed concrete class is both a vtable *value* and
  a vtable *type*, which the studies never build.

A non-`abstract` method on an abstract class is *not* refused: it is an ordinary method
over the class's invariant, dispatching through its own receiver like any other client
(`quad_semi_perimeter` in the study). This is the C# `sealed`-by-default reading and it
costs nothing.

### 9.2 Models and the forgetting function

**R9.5 — An abstract class's `[Model]` member is `abstract`, and declares only the model
*type*.** It has no body because there is no representation to abstract from. Its
`[Refine]` clauses behave exactly as in R3.9d.

**R9.6 — A derived class supplies its parent's model by `override`ing the parent's
`[Model]` member with an expression over its *own* model.** That override *is* the
forgetting function, and it is written in idiomatic C# with no new attribute:

```csharp
public abstract class Shape          { [Model] protected abstract SpecInt Area { get; } }
public sealed class Square : Shape
{
    private int side;
    [Model] private SpecInt Side => side;              // abstraction from the fields
    protected override SpecInt Area => Side * Side;    // Shape's model from Square's
}
```

Emitted as `class_Square__forget (m: class_Square__model) : class_Shape__model`. It is a
total function of the derived model, which is what makes a subclass a *refinement* of its
parent: the parent's model is recoverable from the child's, and never the reverse.

**R9.7 — A virtual method's contract is written once, on the `abstract` declaration, at
the declaring class's model.** An `override` carries no contract of its own; restating it
would be either a repetition or a Liskov violation, and C# gives it nowhere to go. So the
*implementation* in a leaf is checked against the parent's contract, over the parent's
model — which is exactly how the studies type a leaf's vtable slots.

This has a consequence worth stating because it is the most common way a hierarchy fails
to verify: **a base method's precondition must be strong enough for every subclass.**
`Shape.Double()`'s `4 * Area <= int.MaxValue` bounds a square's side only because a
square's area is `side * side`; for a shape whose model does not bound its representation
the base precondition says nothing and the leaf will not verify. §8 works this out for a
quadrilateral's perimeter. The fix is the user's — strengthen the base contract, or add a
`[Refine]` to the leaf's model — and never the emitter's.

### 9.3 What a reference is

**R9.8 — A reference into a hierarchy is a `dyn`, and the dyn is always made at the
*root's* object record.** `class_Shape = Dn.dyn`, and so is `class_Quadrilateral`: an
intermediate class is a *view* of the same value, differing only in its invariant. This
is exactly C#'s reference-conversion semantics, and it is forced — a dyn is made at one
witness type, so a value made at `class_Quadrilateral__obj` could never be read back as a
`class_Shape__obj` without injectivity of `mkdyn`, which `ShapeHierarchy.fst` §3 pins as
unavailable.

**R9.9 — Each abstract class emits a vtable type, an object record, an ownership
predicate, and an invariant**, in that order:

| Construct | Meaning |
|---|---|
| `class_C__vtbl` | one field per virtual method visible at `C`, at `C`'s model, plus `impl: Type`, `inv`, `share`, `gather` |
| `class_C__obj` | `{ pkg: class_C__vtbl; rep: pkg.impl; sub: Dn.dyn }` — `sub` is R9.18's extension point |
| `class_C` | `Dn.dyn` at the root; the parent's reference type at an intermediate class (R9.18) |
| `class_C__at o p m` | `o.pkg.inv o.rep p m` — ownership of a *known* object record |
| `class_C__inv s #p m` | `exists* o. pure (s == mkdyn (view o)) ** class_C__at o p m` |
| `class_C__inv_at s o p m` | the same with the object record **named** |

`class_C__inv` has the same signature as an M2 class invariant (§3.4), which is why a
*client* of a hierarchy needs no new rules at all: R4.5's model binders, R4.10's
fold/unfold bracket, R3.10b's nested objects and R5.12's loops all apply unchanged.

A slot's type is the virtual method's contract with the receiver read as the vtable's own
`inv x p m`. Three things about it are load-bearing, and all three were found by building
it rather than by reading the studies:

* **R4.8 applies to a slot exactly as it applies to a method.** A slot's `ensures` is
  `pure (REQ ==> ENS)`, because that is what the `Func_` module implementing it produces
  and one C# contract must not be stated two ways. Emitting the bare `ENS` in the slot
  makes the vtable literal fail with an unprovable subtyping check, which is the right
  failure: the two are not definitionally equal even though they are equivalent.
* **A slot is generated apart from `MethodPlan`.** Its `inv` takes the permission
  *positionally* where R4.10's takes it as F21's meta-argument-defaulted implicit, so the
  application shapes differ and there is nothing to share.
* **The binder orders differ, and the eta-expansion is where they meet.** A slot binds
  `#p` before `#m`; R4.10 threads the model binder before R4.11b's permission. F33 already
  forces the pack site to eta-expand every slot, so the reconciliation costs nothing and
  neither side bends towards the other.

**R9.9a — A virtual method takes and returns plain values.** A slot's type is fixed by the
base class, so every subclass would have to own the same resource in the same way; only a
value parameter has a reading that does not depend on the implementation. An `abstract`
method with an array, object or `ref` parameter is refused (PALCS0545) rather than given a
guessed ownership.

**R9.9b — Inside `Class_C`, an observation of `C` is written unqualified.** This is R3.7's
rule about field qualifiers, and it holds for the same reason: a self-qualified name makes
F*'s dependency scan read the module as depending on itself. It first bites here because
§3.4's class module has no reason to mention its own observations, and a vtable slot's
contract has every reason to.

**R9.10 — The indexed invariant is the primitive; the plain one is derived.** Both
studies force this. `gather` needs to know *which* implementation the two halves came
from, and so does a downcast (§9.7); `class_C__forget_impl` throws the index away, and is
one ghost step. Every dispatching wrapper is emitted at the index, with the plain form
derived — one dispatching body per method, not two. Forgetting is *irreversible* even
given the equation (`quad_remember_impl` is pinned `expect_failure`), so an upcast is a
real one-way commitment, which is the honest reading of C#.

**R9.11 — `share` and `gather` are vtable slots, not emitted lemmas.** R3.10d emits them
per class because their proofs recurse into the class's own structure. Behind a dyn there
is no structure to recurse into, so they become dispatched operations like any other, and
the leaf supplies them from the R3.10d bodies it already has. Read-only aliasing of a
`Shape` therefore costs nothing at runtime.

### 9.4 Dispatch

**R9.12a — A call is virtual iff it resolves to an `abstract` declaration**, however the
receiver is written. It is emitted as the dispatching wrapper in `Class_C`, and its
arguments, implicit model binder and permission are found by exactly the rules a direct
call uses, because R9.9 gives the wrapper the same contract shape a direct method has.

**R9.12 — A call on a hierarchy-typed receiver dispatches through the vtable, and costs
one `recover` per level.** For a root-typed receiver:

```
fn class_C_M_at (s: class_C) (#o: erased class_C__obj) …
  preserves class_C__inv_at s o p m
{ unfold …; let ob = recover #class_C__obj #o s; let f = ob.pkg.fld_M; let v = f ob.rep …; fold …; v }
```

Three facts from §1 are load-bearing here and the emitter obeys all three without knowing
why: F31 (a stored Pulse computation must be let-bound before it is applied — `ob.pkg.f x`
does not run), F33 (a pack site must eta-expand every slot, because F21's
meta-argument-defaulted permission binder does not match a vtable field type), and F34
(name the body of an invariant so that the closing `fold` has a head symbol whose argument
*is* the witness).

At depth *k* the wrapper recovers the root object and then follows `sub` once per level.
The CLR does the whole thing with one header check; the gap is the price of erasing the
dynamic type into `dyn`, and it is paid in casts, not in memory.

**R9.12b — A dispatching wrapper binds the slot's result exactly when the slot has one,
and returns it after the invariant is folded back.** Stated this baldly the rule sounds
like it needs no stating, and for two years it was left implicit. It was implemented only
on the read-only path.

The two paths differ, and the difference is why: a read-only wrapper ends in
`fold (…__inv_at s o p m)` with the *same* model it started with, whereas a mutating one
must first name the post-model the callee produced —

```
let f = ob.pkg.fld_M;
let v = f ob.rep …;                                  // R9.12b: bound because M returns a value
with post_this. assert (ob.pkg.inv ob.rep p post_this);
fold (class_C__at ob p post_this);
… ;
v                                                    // R9.12b: after the fold, not before
```

— and the extra `with`/`assert` between the call and the fold made the mutating path look
like a *statement* sequence, so the value was dropped on the floor. `fold` returns `unit`,
so the wrapper declared `returns ret: I32.t` and its body ended in `()`.

That combination — a virtual method that **both** mutates its receiver and returns a value
— is unremarkable C# (`int Bump() { int was = k; k = k + 1; return was; }`) and was inside
the shipped subset the whole time. Nothing rejected it. `palcs` reported `0 error(s)` and
wrote ill-typed Pulse, which is the failure §18 exists to prevent: the emitter must either
translate a construct or refuse it, and *silently mistranslating* is worse than either.

Three wrappers are subject to the rule and all three had the defect, which is itself the
lesson — R9.10 emits two (the indexed form that dispatches and the plain form that composes
it with forgetting, where the intervening `__forget_impl` is ghost and returns `unit`), and
R9.18 emits a third for each intermediate class (the forwarder that packages that class's
vtable into its parent's, where the intervening step is a `fold` again). Each was written
at a different time and each independently grew a `moves ? … : …` split around the call,
and in all three the value-binding — which has nothing to do with whether the receiver
moves — got captured by that split. **A conditional in the emitter attracts unrelated code
into its branches**; when the same two-armed test appears at three sites, what is common to
the arms deserves to be lifted out of the test rather than duplicated into it.

The regression test is `test/deep_hierarchy`'s `DoubleAndReport`, dispatched at the root
over a leaf of the intermediate class so that all three wrappers are on the path at once.

**R9.13 — `recover` is the one assumption.** `Pulse.Lib.CSharp.Assumptions.recover` says
the CLR object header faithfully records the dynamic type. It is unprovable because
`FStar.Dyn.undyn` returns in `Dv`, and it is stated in `stt` rather than `stt_div` because
`stt_div a emp post` is inhabited for every `post` and so would assume nothing. It does
**not** imply injectivity of `mkdyn`.

### 9.5 The leaf

**R9.14 — A `sealed class C : P` emits its M2 representation *unchanged*, plus five
things**: the forgetting function (R9.6); `class_C__as_P`, which is `class_C__inv` seen at
`P`'s model; one `fn` per `override`, specified over `class_C__as_P` and `P`'s model
(R9.7); the vtable literal `class_C__vtbl : class_P__vtbl`; and
`class_C__obj (c: class_C) : class_P__obj`.

That the leaf's own invariant is untouched is the point: an M2 class and an M3 leaf differ
by a wrapper, so `[Invariant]`, `[Refine]`, arrays, nested objects and R3.10d's share and
gather all keep working inside a hierarchy with no new rules.

The vtable literal must be emitted *after* the method modules and *before* the
constructor's, so it gets a module of its own, `Vtbl_C.fst` (§2). F* computes the order.

### 9.6 Upcast

**R9.15 — An upcast is a ghost fold, and is inserted where C# inserts a reference
conversion**: assignment to a base-typed variable or field, an argument to a base-typed
parameter, a `return` at a base type, and an element store into a base-typed array.

```
ghost fn class_C__upcast_at (c: class_C) … requires class_C__as_P c #p m
                                           ensures class_C__inv_at (mkdyn (view (class_C__obj c))) …
```

The value changes — `c` is a box, and the upcast produces `mkdyn (…)` — where a C#
reference conversion does not. That is a property of the encoding, not of the source
program, and it is invisible to the C# semantics because the box is unreachable
afterwards: the only way back is R9.16, which requires the index.

**R9.15 is recorded by the frontend, not found by the emitter.** C# performs the
conversion silently and Roslyn already says where: at every expression whose
`ConvertedType` is a class other than its `Type`. The lowerer wraps exactly those in an
`IrConvert`, so the emitter has *one* rule applied wherever the node appears — a local
declaration, an argument, a `return` — rather than one rule per position, and a position
nobody thought of is a position that already works. `Shape s = sq;` and
`Square q = (Square) s;` are then the same IR node, told apart by the hierarchy rather
than by the syntax.

**R9.15a — The conversion also has a value form, and that is what a statement uses.**
Pulse matches resources by name, so a ghost upcast followed by `let x = mkdyn (…)` leaves
the invariant attached to the term and not to `x` (Error 228, the same fact R3.8's object
locals are already shaped by). `class_C__to_P_at` is the ghost step followed by the
reference, returning it, so the conversion is one operation:

```
let t0 = func_Square__ctor 5l;
with vs_0. assert (class_Square__inv t0 vs_0);
fold (class_Square__as_Shape t0 (class_Square__forget vs_0));
let var_s = Vtbl_Square.class_Square__to_Shape_at t0;
```

The `with` is not a proof step but the naming R9.6 needs: the view is folded at the
forgetting of *whatever model the constructor established*, and only the prover can name
that. Currently inserted at a local declaration whose declared type is the immediate base;
the other three positions and longer chains are refused with a diagnostic rather than
emitted untested.

**R9.15b — The conversion keeps the index, and the *emitter* is what drops it.** The
`_at` form ensures `class_P__inv_at s (hide (class_C__obj_of t)) p m`, not the anonymous
`exists* o. inv_at s o p m` that R9.3's reference is. Keeping it is what makes R9.16
provable at all, and dropping it is a separate, explicit step, `class_P__forget_impl s o`,
because an indexed reference cannot be handed to a method (whose parameter is anonymous by
R9.3), stored, or returned. The emitter therefore forgets the index of

* every argument of a call except a receiver it is dispatching on,
* a returned object,
* an object local at the end of its scope (R3.8's drop, at the indexed resource).

`class_P__forget_impl` takes the object record explicitly and **leaves both its permission
and its model to inference**: naming the model with a `with` would bind an opaque witness
and sever the link to the constructor's post-state, which is F34/R4.11a again.

**R9.15c — The conversion consumes the derived reference.** C# leaves both names usable;
the encoding cannot, because the derived object's invariant *becomes* the base's. The old
name is marked cast and its next use is **PALCS0548**. Converting a name the method does
not own outright — its own receiver, or an object parameter — would give away the invariant
R4.10 promises to return, and is **PALCS0549** at the conversion. What is left is
**PALCS0546**, a conversion between two classes the hierarchy does not relate at all
(R9.18c makes several levels at once ordinary). A cast *down* in expression
position stays **PALCS0547**, because unlike the upcast it also binds the model equation
the caller reasons with, and an equation needs a name.

**R9.15d — A method may return an object, and R4.12 is where that was already written.**
A constructor's postcondition owns the object it built and calls it `this`; an ordinary
method's owns the object it returns and calls it `Result`. That is the only difference, so
the rule is stated once for both: a class-typed return adds
`exists* post_result. class_P__inv var_result post_result` to the `ensures`, and `Result`
in the contract denotes *the model*, never the reference — `Result.TheArea` means something
only under that reading, and a reference is a thing no specification can say anything about.

A base-typed array is therefore heterogeneous with no extra machinery (`shape_slot` in
both studies), and `total_area` traverses one at a fraction.

### 9.7 Downcast

**R9.16 — A cast to a derived type requires the ghost index naming the object.** It is
emitted as the chain walker plus one `recover`, and it needs no assumption beyond R9.13.
The precondition *is* the knowledge, and it is the same index `gather` already forced.

The base emits two constructs for it, next to `share`/`gather`:

```
let class_P__box (o: class_P__obj) : Dn.dyn = Dn.mkdyn o.rep
fn  class_P__rep (s: class_P) (#o: erased class_P__obj) …
      requires class_P__inv_at s o p m ensures … ** pure (d == class_P__box o)
```

`rep` walks the chain — `unfold inv_at; recover; fold inv_at` — and returns the box rather
than `o.rep` itself, because reading the field needs a coercion across `o.pkg.impl ==
class_C`, which is only propositionally true. Each leaf emits the cast:

```
fn class_C__from_P (s: class_P) (#c: erased class_C) (#p: perm) (#m: erased class_P__model)
  requires class_P__inv_at s (hide (class_C__obj_of (reveal c))) p m
  returns  r: class_C
  ensures  class_C__as_P r #p m ** pure (r == reveal c)
```

and the client is R9.15b's index followed by that cast and R3.8's unfold:

```
let var_s = Vtbl_Square.class_Square__to_Shape_at t0;
let t1 = class_Shape_Double_at var_s;
with vs_1. assert (Class_Shape.class_Shape__inv_at var_s (hide (…__obj_of t0)) 1.0R vs_1);
let var_sq = Vtbl_Square.class_Square__from_Shape var_s;
unfold (Class_Square.class_Square__as_Shape var_sq vs_1);
with vsq_2. assert (Class_Square.class_Square__inv var_sq vsq_2);
```

The `pure (r == reveal c)` is what makes the round trip an identity, so a `Square` cast up
and back is the same reference. Using a name after it has been cast is **PALCS0548**: C#
would let both names live, the encoding does not, and saying so at the C# use is better
than a resource mismatch at the Pulse one.

**The cast recovers the type, never the model.** After `Shape s = new Square(5)` only the
observations R9.6's forgetting kept survive, so `GrowAndMeasureSide` can conclude
`Result * Result == 100` and not `Result == 10`. That is C#'s semantics, not a weakness of
the encoding: an upcast really does lose static knowledge, and a program that needs it back
should not have upcast.

Be precise about what this proves. `recover` has no failure mode: it is not "test the
header and maybe fail" but "given a proof the header matches, hand back the value". So the
cast cannot fail — not because anything proves a runtime test succeeds, but because the
encoding only lets a user *write* the casts whose test is redundant. A cast that might
fail is not one this scheme proves safe, it is one this scheme cannot express, and `as`,
`is` returning `false`, and a throwing cast are all refused. That is consistent with
exception-freedom (§6): a verified cast is one that cannot throw.

**R9.17 — The encoding is an implementation detail, and F* is what enforces that.**
Everything above is a *scheme*, and a scheme's choices are its own business. R9.3 makes a
reference `FStar.Dyn.dyn` and R9.16 recovers from it through an assumption; both are
decisions made for §9's convenience, and neither is anything a C# program can talk about.
So each generated class module is emitted as an interface and an implementation, and the
split is by *who is entitled to know*:

| | Class_C.fsti | Class_C.fst |
|---|---|---|
| the model type and its `spec_C_*` observations | definition | — |
| `class_C__vtbl`, `class_C__obj` | definition | — |
| `class_C : Type0` | `val` only | `= Dn.dyn` |
| `inv`, `inv_at`, `forget_impl`, share/gather, the dispatchers | signature | body |
| `class_C__at`, `class_C__box`, `class_C__rep` | — | all of it |
| `class_C__pack`, `class_C__unpack` | signature | body |

The vocabulary a specification is written in — the model and its observations — is wholly
public, because every contract about the class is stated in it. The vtable and the object
record stay transparent too, but for a different reason: they are the class's *dispatch
interface*, the thing a subclass builds, not its encoding. What becomes private is the
representation of a reference and everything that reads it.

Two new primitives are what make that possible, and they are the interface's whole content
on the subject:

```
fn class_C__pack (o: class_C__obj) (#p: perm) (#m: erased class_C__model)
  requires o.pkg.inv o.rep p m
  returns  s: class_C
  ensures  class_C__inv_at s (hide o) p m

fn class_C__unpack (v: class_C__vtbl) (x: erased v.impl) (s: class_C)
                   (#p: perm) (#m: erased class_C__model)
  requires class_C__inv_at s (hide ({ pkg = v; rep = reveal x })) p m
  returns  r: v.impl
  ensures  v.inv r p m ** pure (r == reveal x)
```

`pack` is R9.15a's ghost step with the dyn taken out of it; `unpack` is R9.16's recovery
with the dyn *and* the assumption taken out of it — its precondition says only "the index
is this vtable applied to this value", which is exactly the knowledge R9.16 already
required. `Vtbl_C` then reads:

```
fn class_Square__to_Shape_at (x: class_Square) (#p: perm) (#m: erased class_Shape__model)
  requires class_Square__as_Shape x #p m
  returns  s: class_Shape
  ensures  class_Shape__inv_at s (hide (class_Square__obj_of x)) p m
{
  rewrite (class_Square__as_Shape x #p m)
       as ((class_Square__obj_of x).pkg.inv (class_Square__obj_of x).rep p m);
  class_Shape__pack (class_Square__obj_of x) #p #m
}
```

with no `Dn.mkdyn` and no `CAs.recover` anywhere in it. The measurable consequence, and the
one worth checking for: in `test/shape_hierarchy`, `FStar.Dyn` occurs in **exactly one**
generated module out of twenty-eight. The subclass modules get interfaces on the same
principle — `obj_of` and the two casts are published, the vtable *value* that implements
them is not.

`class_C__upcast_at`, which R9.15a used to go through, is gone: its `ensures` named
`Dn.mkdyn` and so could not be stated in an interface at all. That it had to disappear is
the encapsulation working — a signature that cannot be written without the encoding is a
signature that was leaking it.

**What is *not* interfaced, and why.** A `sealed` class keeps a single `.fst`. R4.10 has
its methods `unfold` and `fold` `class_C__inv` — and those methods are *separate F\*
modules* (`Func_Square_GetArea`), so an abstract leaf invariant would need its opening and
closing published as ghost functions. That is a real rule, not a difficulty, but it is a
rule about §4 and not about §9, so it is left until there is a client that wants it.


Each of these is a construct with no image under the scheme, diagnosed at the C#
declaration that asks for it, never a prediction about a proof:

| Construct | Rule |
|---|---|
| a field on an `abstract` class | R9.2 |
| `virtual` with a body; `base.M()` | R9.3 |
| a non-`sealed` concrete class | R9.4 |
| a derived class that does not override its parent's `[Model]` | R9.6 |
| a contract on an `override` | R9.7 |
| a virtual method taking or returning a non-value | R9.9a |
| an upcast anywhere but a base-typed local | R9.15a |
| `interface`, multiple bases, generics | not probed |
| a cast *down* in expression position | PALCS0547, R9.15c |
| a use of a reference after it has been converted | PALCS0548, R9.15c |
| converting one of this method's own object parameters, the receiver included | PALCS0549, R9.15c |
| `as`, `is`, a cast that may fail; `Pal.Is<T>` in a contract | R9.16 |

### 9.8 Depth

Everything above is stated for a hierarchy of two levels: an `abstract` root and its
`sealed` leaves. C# hierarchies are deeper, and the class in the middle — `abstract class
Quadrilateral : Shape`, with a model of its own, a virtual method of its own and leaves of
its own — is not a staging post but a real abstraction that clients program against.

**R9.18 — An intermediate class is emitted by the *same* rules as a root, over three
primitives.** The whole of §9.3–§9.7 is written in terms of "the reference `s` denotes the
object record `o`". Name that relation and give it a maker and a reader, and every other
construct is byte-identical text at every depth:

| Primitive | Root | Intermediate `Q : P` |
|---|---|---|
| `class_C__is s o : prop` | `s == Dn.mkdyn o` | `class_P__is s (class_Q__view o)` |
| `class_C__ref o` → `s` | `Dn.mkdyn o` | `class_P__ref (class_Q__view o)` |
| `class_C__obj_at s #o` → `o` | `CAs.recover s` | `class_P__obj_at s`, then `CAs.recover pob.sub` |

`class_C__inv`, `class_C__inv_at`, `class_C__at`, `class_C__forget_impl`,
`class_C__intro_at`, `class_C__elim_at`, `class_C__pack`, `class_C__unpack`, both
dispatcher forms and share/gather are then *one* definition each, emitted unchanged for a
root and for an intermediate class. Depth is therefore not a case in the emitter: there is
one `EmitAbstract`, taking an optional parent.

Three consequences are worth stating, because each was a design decision that could have
gone the other way:

* **The dyn is made once, at the root** (R9.8). `class_Q = class_P`, so a `Quadrilateral`
  reference *is* a `Shape` reference — which is what makes the upcast a ghost step and
  matches C#, where the conversion changes no bits.
* **`sub` hangs off the object record, not off the vtable.** It holds
  `Dn.mkdyn qo` — the record one level down, vtable *applied to* its representation — so
  what a descendant recovers is a working object, not a package it would have to re-apply.
  A direct leaf of the class stores `Dn.mkdyn ()`.
* **`class_C` stays abstract in the `.fsti` at every depth** (R9.17). Transparency would
  be needed only if a client crossed between two classes' reference types, and the only
  crossings are R9.18's own casts, which live inside `Class_Q`.

**R9.18a — Each edge emits a derived vtable, and its proof obligation is discharged by
SMT.** `Q` gives `P` a package built from `Q`'s: `class_Q__as_P_pkg` keeps `impl`
definitionally equal and replaces each inherited slot by a wrapper whose contract is stated
at `P`'s model. The wrapper's obligation is exactly R9.19's re-reading — the inner slot's
contract at `Q`'s model *is* the outer one composed with `class_Q__forget` — so the view's
`pure (m == class_Q__forget own)` is all the prover needs, and no lemma is emitted.

The ownership the wrapper is written over is `class_Q__as_P qp x p m`, a predicate over a
*vtable and representation* rather than over `class_Q__inv`. That is not a stylistic
choice: `class_Q__inv` is defined through `class_Q__is`, which is defined through `P`, so
using it here would close a cycle.

**R9.18b — Each edge emits two casts, and the upcast returns the reference it was
given.** `class_Q__to_P_at`, `class_Q__to_P` and `class_Q__from_P` sit beside `Q` (there is
no vtable module for an abstract class). The upcast is `elim_at`, fold `as_P`, rewrite,
`class_P__intro_at` — it must *return `s`*, because building the result with
`class_P__pack (class_Q__view qo)` would take `Dn.mkdyn` of an erased value, which does not
extract. The downcast's postcondition is existential, `exists* own. inv_at r o p own **
pure (m == class_Q__forget own)`, because forgetting is not injective: a `Shape` model does
not determine the `Quadrilateral` it came from.

**R9.18c — A conversion across several levels is the composition of the one-edge rules.**
C# writes one conversion where the hierarchy has several edges; the emitter walks the
chain and applies R9.15 (or R9.16) once per edge, in order. `Shape s = new Square(5);` and
`Square sq = (Square) s;` are therefore ordinary, and the intermediate references are the
same ones the reader would get by writing the steps out. No rule is added for depth.

**R9.18d — A virtual call goes to the dispatcher of the receiver's *static* class; the
member keeps the name its declaring class gave it.** `q.GetArea()` on a `Quadrilateral`
must reach `Quadrilateral`'s wrapper, because a wrapper's contract and invariant are
written at its own class's model and `Shape`'s would demand an invariant the caller does
not hold. The *slot* reached is the same either way, which is why the slot's name comes
from `DeclaringClass` and is stable all the way down. Concrete methods of an abstract class
(R9.13) have bodies and no slot, so they are called directly even though the receiver is
abstractly typed — "virtual" is decided by the `abstract` declaration (R9.12a) and never by
the receiver's type.

**R9.18e — Calling an `override` at the leaf's own static type opens R9.14's view.**
R9.7 writes an override's contract at the base's model, so its receiver is owned through
`class_L__as_B` and not `class_L__inv`. A caller naming the override directly — which is
what `sq.Perimeter()` on a `Square` is — hands the receiver over the same way: `fold` the
view at `class_L__forget own` before the call, `unfold` it after. It is the same two ghost
steps R9.15 emits, for the same reason, and it is the rendering of "this reference is being
used as a `B`", not a proof step.

**R9.19 — An inherited observation is re-read by composing the forgetting functions along
the chain.** `[Ensures("Result == @this.TheArea")]` is written once, on `Shape.GetArea`. At
`Quadrilateral` it means `spec_Shape_TheArea (class_Quadrilateral__forget m)`; at `Square`,
one more `class_Square__forget`. The spec emitter walks the base chain from the class the
model belongs to up to the class the observation was declared on, and composes. This is
R9.6 iterated, and it is what makes a base's contract mean something at every model below
it.

**R9.19a — A base's model must be strong enough to bound every subclass's
representation.** `Quadrilateral`'s model is a bounding box, not `{Area, Perimeter}`, and
`Shape.Double`'s precondition — `4 * Area` representable — bounds a square's side and a
box's sides but says *nothing* about a perimeter. So `Rectangle` cannot carry a class
invariant `2*(w+h) <= int.MaxValue`: no override of `Double` could re-establish it. The
perimeter bound belongs where the C# already puts it, as a precondition of `Perimeter()`.
That is a true statement about the program, and §0 rule 3 says the fix goes in the
annotations, never in the emitter.

### 9.9 Computed properties

**R9.20 — A computed property is its accessor, translated as the method the accessor is.**
C# has three property forms and §9 used to translate one of them. An *auto*-property is a
field with a generated accessor pair, and R3.4 already reads it as a field. A `[Spec]`
property is an observation of the model, and R3.9c already reads it as one. The third — a
property with an accessor *body*, over the representation rather than over the model — was
matched by neither, so R18.1 refused it. It is also the form most idiomatic C# uses to
expose state.

The rule is that the third form is not a new construct at all. A read-only property

```csharp
[Ensures("Result == @this.TheW + @this.TheW")]
public int Doubled => w + w;
```

translates exactly as the method the user could have written instead:

```csharp
[Ensures("Result == @this.TheW + @this.TheW")]
public int Doubled() { return w + w; }
```

One module `Func_C_Doubled`, `this` a `Box` of the representation opened by R9.7's frame,
the contract read from the *property* declaration (which is where C# permits an attribute
— an accessor may not carry one), and a body lowered by the ordinary rules. Nothing about
§9 changes: the getter is a nullary instance method, and every rule that speaks about an
instance method already speaks about it.

**R9.20a — A read `o.P` is the call `o.P()`.** In an executable position, a property read
lowers to R9.13's instance call with no arguments. The two spellings therefore produce
identical Pulse, which is what §7.2's variant detector requires of a style choice: the
variant of a class may write `Doubled()` where the original writes `Doubled`, and the
emitter may not be able to tell.

In a *specification* position `o.P` is unchanged: R3.9c reads a `[Spec]` member of the
model and nothing else. A computed property is executable code over the representation, so
a contract cannot mention it, exactly as a contract cannot mention an ordinary method.
That is not a restriction R9.20 adds; it is R3.9c, which is why the example above states
its postcondition over the `[Spec]` observation `TheW`.

**R9.20b — A `set` accessor is refused (`PALCS0591`).** A setter is a method of one
parameter that writes fields, so R9.20 would carry it over unchanged but for one thing:
C# gives the parameter the contextual name `value`, and every rule that binds a parameter
— R4.2's naming, R4.6's ghost arguments, the `@`-qualified spec vocabulary — assumes the
name is one the user wrote and can mention in a contract. `value` is a keyword in exactly
one position and an ordinary identifier everywhere else, and until §4 says which it is in
a specification, a setter has no contract that can be written down. Write the assignment
as a method.

**R9.20c — A property is refused if it is not read-only, and its accessor is not counted
twice.** A getter appears in `GetMembers()` both as the property and as `get_P`, an
`IMethodSymbol` whose `AssociatedSymbol` is the property. The accessor is the thing with a
body and the property is the thing with the attributes, so the two are collected as one
declaration named for the property. R2.1's mangling therefore produces `Func_C_P`, not
`Func_C_get_P`: C# forbids a property and a method of one name in one type, so the name
stays injective.

### 9.10 Status

**Implemented and verified**, by `test/shape_hierarchy`: an `abstract Shape` with two
virtual methods and an observed model, `sealed Square` and `sealed Circle` with unrelated
representations, and a client that reads through dispatch, mutates through dispatch,
dispatches inside a loop, and upcasts a fresh leaf to the base. `ShapesVariant.cs` is
§7.2's detector and passes with no emitter change.

Two failures during the build were fixed where §0 rule 3 says they belong. `RepeatArea`'s
loop re-quantifies the shape's model, so a bound its precondition established has to be
restated as a `Pal.Invariant` — an annotation in the `.cs` file. And an earlier client
whose growth was exponential was dropped, because no invariant its bound could support
existed; that is a true statement about the program, not a gap in the scheme.

`Circle` is the evidence that the translation is not fitted to `Square`: it was added after
the emitter was complete, with a different representation, a different forgetting function
and a nonlinear observation, and needed no emitter change at all.

The checked downcast R9.16 is implemented too, and verified by `Shapes.MakeAndSum` (two
upcast locals whose indices are forgotten at a call) and `Shapes.GrowAndMeasureSide` (upcast,
virtual call at the index, downcast, then a `Square`-only method) — both, again, in the
variant as well.

Building it uncovered a *pre-existing* defect that R9.15b's forgetting made visible: a
read-only object parameter's postcondition was unusable by callers, because the mutation
analysis asked `Normalize.Assigned`, whose answer is "which names need a mutable cell"
(R4.2) and which may therefore say "everything a call touches". For a model that is not a
conservative approximation but a loss: the object comes back anonymous and
`Result == a.TheArea + b.TheArea` cannot be stated. R4.11's rule now lives in exactly one
place, `Normalize.Mutated`, and is used both for a method's parameters and — this is the
same fact one level down — for deciding which of a loop's objects R5.8b may hold fixed.

The conversion now happens wherever C# performs one. `Shapes.SumFresh` converts a fresh
object and a named local at two argument positions; `Shapes.MakeShape` returns one. Both
have variants that convert at the other argument, the other class and the other position,
and needed no emitter change — which is the §7.2 detector doing its job, and is the payoff
of recording the conversion in the frontend rather than recognising it at one privileged
site.

Not yet implemented: heterogeneous arrays — an array of a base type needs R6's array rules
to carry an object invariant per element, which §6 has not probed — and the *cross-method*
downcast, where the index travels in a contract (`Pal.Is<T>`) rather than within one body.

R9.17's interfaces were then applied to the whole of the above and changed no client and no
proof: the same fourteen client methods verify against `val class_Shape : Type0` as
verified against `Dn.dyn`, which is the evidence that nothing outside `Class_Shape` was
depending on the encoding. The provenance lint now reads `.fsti` as well as `.fst`, so a
construct cannot escape §7.2's detector by being declared rather than defined.

**Depth three (R9.18/R9.19) is implemented and verified**, by `test/deep_hierarchy`:
`Shape > Circle` and `Shape > Quadrilateral > {Square, Rectangle}`, where `Quadrilateral`
is abstract, has a two-number model of its own, declares a virtual `Perimeter()` and a
concrete `SemiPerimeter()` that calls it, and inherits `GetArea`/`Double`. The client
programs at all three static types, dispatches an inherited virtual at the intermediate
class, loops, converts at both edges and in one step across both, and casts back down one
and two levels. `ShapesVariant.cs` is §7.2's detector and passes with no emitter change.

`Rectangle` is depth three's `Circle`: a second leaf of the middle class with an unrelated
representation, added after the emitter was complete, and it needed no emitter change —
only the removal of a class invariant its base's contract could not support (R9.19a).

Three defects the two-level suite could not see were fixed while building it, each in the
scheme rather than in an example: a virtual call was going to the *declaring* class's
wrapper rather than the receiver's (R9.18d); a call to an `override` at the leaf's own
static type was not opening R9.14's view (R9.18e); and a concrete method of an abstract
class was being taken for a vtable slot because the test was the name and not the
`abstract` declaration (R9.12a). A fourth was a refusal that had been stated only for the
receiver: converting *any* object parameter gives away an invariant the method's own
postcondition owes back, so PALCS0549 now covers all of them, with
`test/diagnostics/cases/UpcastParameter.cs` as the case.

Depth four and beyond is supported by construction — every abstract class emits `sub`, the
three primitives and, if it has a parent, a derived vtable and two casts — but is untested.

---

## 10. Recursive data structures

A `Counter` owns a number. A `Stack` owns an array. A `Range` owns two `Counter`s. In every
one of those, R3.10's invariant is a *flat* `exists*` over one record, and it is flat
because the class's field graph is finite and acyclic and known at emission time.

A `Node` with a `Node? next` is not. Its invariant has to be an **induction**, and §10 is
about what that induction is, where it comes from, and who writes it.

### 10.1 What PAL does, and what is wrong with it

PAL's answer for C (`../pal/test/recursive_struct/recursive_struct.c`) is to give up and
hand the user Pulse. The user writes

```c
_include_pulse(ListPredicates,
  "let rec is_list (head:list_node_ptr) (p:perm) (l:list int)
     : Tot slprop (decreases l) = match l with … ")
```

then hand-writes three ghost lemmas — `is_list_nil_case`, `elim_is_list_nonnull`,
`intro_is_list_cons` — and then invokes them by hand, with `_ghost_stmt(…)`, at every null
test and around every field read. The predicate, the lemmas and their placement are all the
user's problem, and all three are written in a language that is not C.

That is a reasonable escape hatch and pal-csharp keeps the equivalent one (`[PulseBody]`,
`IncludePulse`). But it is not an *annotation language* for this feature: nothing about the
predicate is specific to the proof, and nothing about the placement is specific to the
program. Both are functions of the class declaration and of the C# control flow. §10's
claim is that the user should write **no Pulse at all** — only the `[Model]` member they
already have to write for every class (R3.9), and the `if (n == null)` they already have to
write for the program to run.

### 10.2 The representation

**R10.1.** A class is **recursive** when at least one of its fields has the class's own
nullable type. Its representation, its reference type and its nullable form are emitted as
one mutually recursive group (F35):

```fstar
noeq type class_Node__raw = {
  fld_value: I32.t;
  fld_next: class_Node__opt;
}
and class_Node__opt = B.box class_Node__raw
and class_Node = b: class_Node__opt { not (B.is_null b) }
```

**R10.2.** `C?` is `B.box C__raw`, and `C` is its **non-null refinement**. A Pulse `box` is
already a nullable pointer (F76): the library gives `B.null`, `B.is_null` with
`b <==> r == null`, and `B.pts_to_not_null`. C#'s `C` and `C?` are likewise one runtime type
plus an annotation. So the honest image of the pair is one type plus a refinement, and the
subtyping `class_C <: class_C__opt` is F*'s ordinary refinement subtyping.

The null test is then `B.is_null x`, whose boolean is *definitionally* the equation
`x == B.null`, so the base case of the induction stays reachable by the prover: `pure (x ==
B.null)` on one side, `[]` on the other, and `class_C__cases` (R10.4) bridging them — the
same shape as before, with the constructor replaced by a decidable equality.

> *Why not `option class_C`? Because `Box` already has a null, and wrapping it gives two
> nullability layers rather than one. The fact a field access then has in hand is `Some? x`
> — a fact about the *encoding*. Under the refinement it is `not (B.is_null x)`, which is
> exactly the annotation the C# programmer wrote. The whole content of the `option` layer
> was the two coercions R10.2b/R10.2c now describe, and those are the identity.*

**R10.2a.** A nullable reference is *owned through the nullable type*: the resource for a
slot of type `C?` is `class_C__inv_opt x #p m`, not `class_C__inv`. R10.3a defines the
non-null invariant in terms of the nullable one, so every §3, §4 and §5 rule that mentions
`class_C__inv` keeps working with no case for recursion.

**R10.2b.** A non-null `C` used where a `C?` is expected — an argument, a `return`, the
right-hand side of a field write — is **the identity**. C# calls it an identity conversion
because nullability is an annotation rather than a type, and R10.2 makes the encoding agree:
`class_C` is a refinement of `class_C__opt`, so the term is already at the wider type. No
coercion is emitted and no lemma is needed to move the invariant, because
`class_C__inv this p m` *is* `class_C__inv_opt this p m` (R10.3a).

**R10.2c.** The converse is also the identity *text*, but not a free step: a `C?` used where
a `C` is expected obliges the solver to discharge `not (B.is_null e)`. In C# that position is
spelled with the null-forgiving operator, `f(x!)`, or is reached by flow narrowing inside an
`if (x != null)` branch. Both work, and for the same reason: the branch condition C#'s own
flow analysis used is the hypothesis F* discharges the refinement from. So `f(x)` and `f(x!)`
translate identically (R10.5 makes `!` transparent), and neither needs the emitter to read
flow analysis — the SMT context already has what the branch put there.

R10.2b and R10.2c therefore have **no emitter component at all**, in code or in
specification position: no coercion wrappers, no widening at an equality, no non-null/
nullable distinction to carry through the IR. This also disposes of a standing wrinkle.
Specification strings are bound by a shim compiled with `#nullable disable` (§4), so a type
recovered from the shim's symbols cannot distinguish `C` from `C?` — which is harmless,
because there is nothing to distinguish them *for*.

**R10.2d.** Allocation is where the refinement is *established*. `B.alloc` returns
`class_C__opt`; a constructor returns `class_C`. The bridging step is `B.pts_to_not_null`,
applied to the `pts_to` the allocation just produced, and it is emitted immediately after
every `B.alloc` (R10.6a, R12.4). This is not the emitter inventing a proof: `new` is
non-null in C#, the surface type already says so, and the step that discharges it is a Pulse
library lemma applied uniformly.

### 10.3 The invariant

**R10.3.** The invariant of a recursive class is a `let rec` over the *nullable* reference,
by cases on the **model**, with `decreases` on the model (F36):

```fstar
let rec class_Node__inv_opt ([@@@mkey] x: class_Node__opt) (p: perm) (m: class_Node__model)
  : Tot slprop (decreases m)
  = match m with
    | [] -> pure (x == B.null)
    | hd :: tl ->
      exists* (r: class_Node__raw).
        B.pts_to x #p r **
        pure (hd == I32.v r.fld_value) **
        class_Node__inv_opt r.fld_next p tl
```

Note what the cons case does *not* have. Under the option encoding it bound a second
existential `v` for the node, reachable only through `pure (x == Some v)` — precisely the
shape R16.3 identifies as one Pulse's matcher cannot solve for. R10.2 removes it at the
source, and with it the commonest instance of that problem.

Three things are load-bearing and none is a choice.

* **The recursion is on the model.** By cases on `x` there is no measure (F36).
* **`[@@@mkey]` is on the reference.** It is the key Pulse matches resources on; without it
  a goal at one model is not found in a context holding the predicate at another.
* **The permission is an explicit parameter, not meta-defaulted.** F21's `#[T.exact …]`
  default cannot be written on a `let rec` binder that the recursive call must instantiate.
  R10.3a restores the defaulted form at the top.

**R10.3a.** The non-null invariant every other rule already talks about is *derived*:

```fstar
let class_Node__inv (this: class_Node) (#[T.exact (`1.0R)] p: perm) (m: class_Node__model)
  : slprop
  = class_Node__inv_opt this p m
```

The argument is `this` and not an injection of it, because R10.2 makes the two types one.
That is what makes R10.2b free, and it is why the derived `class_C__as_opt` and
`class_C__intro` lemmas are now one `rewrite` each rather than a re-fold.

so a recursive class is an ordinary class whose invariant happens to be defined by
recursion, and R4.5's contracts, R4.10's fold/unfold window and R3.10b's nesting need no new
case.

### 10.4 Where the induction comes from — the notation

**R10.5.** The user writes no predicate. They write the `[Model]` member R3.9 already
requires, as a **structural function of the fields**:

```csharp
public sealed class Node
{
    private int value;
    private Node? next;

    [Model] private SpecList<SpecInt> Items => SpecList.Cons(value, next!.Items);
}
```

and the emitter reads it as an induction, by inverting the equation.

The `!` is required — the core invariant says annotated C# compiles unmodified, and a stock
compiler with `<Nullable>enable</Nullable>` will not accept `next.Items` — and it is also
the right reading. It is not a claim that `next` is non-null; it says the member is
**total**: a null reference denotes the empty structure, so `next!.Items` is `[]` when
`next` is null and the equation holds in both cases. That totality is exactly what lets the
equation be read backwards as an induction *with a base case*, and nothing here is ever
executed. The rule is exactly
this and nothing wider:

> The `[Model]` body of a recursive class must be a single application of a **model
> constructor** to arguments, each of which is either
>   (a) a pure expression over the class's non-recursive fields, or
>   (b) `f.M`, where `f` is a field of the class's own nullable type and `M` is the same
>       `[Model]` member.
>
> The constructor's inductive type must have exactly one other constructor, taking no
> recursive argument. That one is what a **null** reference denotes.

Two model types ship with the language, and a third is not needed to make the rule general —
the rule is stated over the constructor's arity, not over the type:

| C# spec type | Pulse | "nil" constructor | recursive constructor |
|---|---|---|---|
| `SpecList<T>` | `list ⟦T⟧` | `SpecList.Empty` | `SpecList.Cons(head, tail)` |
| `SpecTree<T>` | `Pulse.Lib.CSharp.Tree.tree ⟦T⟧` | `SpecTree.Leaf` | `SpecTree.Branch(left, value, right)` |

The derivation is then mechanical. For a model constructor `K a₁ … aₙ` where the recursive
arguments are `aᵢ = fᵢ.M` and the pure ones are `aⱼ = eⱼ`:

```
⟦class C⟧ᵢₙᵥ =
  let rec class_C__inv_opt ([@@@mkey] x) (p: perm) (m) : Tot slprop (decreases m) =
    match m with
    | <Nil>          -> pure (x == None)
    | K b₁ … bₙ      -> exists* (v: class_C) (r: class_C__raw).
                          pure (x == Some v) **
                          B.pts_to v #p r **
                          pure (⋀ⱼ bⱼ == ⟦eⱼ⟧[fields := r.fld_…]) **
                          (**ᵢ class_C__inv_opt r.fld_fᵢ p bᵢ)
```

`SpecTree.Branch(left.Contents, value, right.Contents)` gives the binary-tree predicate by
the same rule, with two recursive conjuncts instead of one (F42).

**R10.5a (refusals).** Anything the derivation does not cover is refused with a diagnostic,
never approximated:

| Diagnostic | Refused |
|---|---|
| PALCS0560 | A recursive class whose `[Model]` type is not one of the inductive spec types. |
| PALCS0561 | A `[Model]` body that is not a single constructor application (R10.5). |
| PALCS0562 | A recursive field that the `[Model]` body does not mention, or mentions other than as `f.M`. |
| PALCS0563 | A recursive class that also has an array field or a non-recursive object field — the induction and R3.10a/R3.10b's flat conjuncts have not been probed together. |
| PALCS0565 | A recursive class in a hierarchy (§9). The two encodings have not been probed together. |
| PALCS0566 | A `[Backward]` field (R10.10): the Pulse shape is pinned, the surface rule is not. |
| PALCS0567 | A field of a recursive class reached outside a null-test window (R10.7c). |
| PALCS0568 | A self-recursive method with no `[Decreases]` (R10.6). |
| PALCS0569 | A null test that is not the whole condition of an `if` (R10.7). |

This is a narrow language. It is narrow *honestly*: every shape inside it is pinned by
`test/pulse_facts/RecursiveFacts.fst`, and §0 rule 3 forbids widening it by guessing.

### 10.5 The derived lemmas

**R10.4.** Six ghost lemmas are emitted beside the predicate, and they are what a client
uses; no client ever unfolds the predicate. This is what makes R9.17's `.fsti` treatment
apply here unchanged, and it is the whole of the improvement over PAL's `_include_pulse`.

| Lemma | Meaning |
|---|---|
| `class_C__cases x` | preserves the invariant; `not (B.is_null x) <==> <the model is a K>`. The bridge between the C# null test and the induction. |
| `class_C__nil_case x` | preserves; `B.is_null x` implies the model is `<Nil>`. |
| `class_C__elim_nil x` | **consumes**; `B.is_null x` implies the model is `<Nil>`. |
| `class_C__intro_nil x p` | `B.is_null x` gives the invariant at `<Nil>`. |
| `class_C__elim_cons x` | on `x: class_C` — R10.2's refinement type *is* "known non-null", so this needs no extra binder and no `pure` — gives up the head cell and each sub-invariant, with the model equation. |
| `class_C__intro_cons x` | its inverse. |

The forward halves of `cases` and `nil_case` are where the one cost of R10.2 is paid. Under
the option encoding `Some? x` held definitionally; under the box encoding non-nullness must
be recovered from the `pts_to`, by **`B.pts_to_not_null`**. That is a Pulse library lemma
applied at a fixed place, so it is a step, not a special case.

Two more are derived from `intro_cons`, and R10.2 has reduced both to a single `rewrite`:

| Lemma | Meaning |
|---|---|
| `class_C__intro x` | `intro_cons` at the **non-null** form: a constructor's result is a `C`, and its postcondition owes `class_C__inv`. Since R10.3a defines `class_C__inv this` as `class_C__inv_opt this`, this is now `intro_cons` plus one rewrite through that definition. |
| `class_C__as_opt x` | R10.2b used to be an injection; it is now the identity, so this lemma survives only because `class_C__inv` is an ordinary `let` that Pulse's matcher does not see through (F77). It is one `rewrite`. |

`nil_case` and `elim_nil` differ only in whether the invariant survives. Which one the
emitter uses at a null test is read off the *contract* — whether the postcondition still
owes that reference's invariant — exactly as R4.10 already reads it. A method that consumes
its argument (R10.6b's `Append` moves `x` into its result) needs the consuming form; one
that preserves it needs the other.

**R10.4d.** R3.10d's `share` and `gather` become `ghost fn rec`, recursing on the model and
proved from the class's own case lemmas rather than by `unfold` (F40). Nothing else about
R3.10c/d changes, so `[Frac]` and read-only aliasing work over a recursive structure.

### 10.6 Methods

**R10.6.** A method over a recursive class is an ordinary method (§4) with two additions.

*Recursion.* A C# method that calls itself is emitted `fn rec` and **must** carry
`[Decreases]`, whose argument is a model. `decreases` on an erased model binder is accepted,
and the obligation at the recursive call is discharged from the equation `elim_cons` hands
back (F38). A recursive method with no `[Decreases]` is PALCS0568 — inferring one would be
the emitter inventing a proof step (§0 rule 3), and is the same refusal R5.9 already makes
for a `while`. There is not even a counted-`for` case to fall back on: a recursion's measure
is a term over the model, so the only two answers are the user's and a refusal.

**R10.7 (the window).** `if (n == null) … else …` **is** the case analysis, so it is where
the lemmas go — the user invokes nothing:

```
⟦if (n == null) S₁ else S₂⟧ =
  class_C__cases n;
  if (None? var_n) {
    class_C__nil_case var_n;      // or elim_nil, per the contract
    ⟦S₁⟧
  } else {
    class_C__elim_cons var_n;
    ⟦S₂⟧
    class_C__intro_cons var_n;    // at the end of the branch, as R4.10 closes its window
  }
```

`class_C__cases` comes first and unconditionally: it is what tells the prover that the two
case analyses — on the reference, which the program does, and on the model, which the
predicate does — agree. Inside the `else` branch every field of `n` is accessible by R3.11's
ordinary rules, reached through `var_n` itself, and every field *write* by R3.12's (F39).

The tests `n == null`, `n != null`, `null == n` and `null != n` all lower to the same
`B.is_null var_n`, with the branches exchanged where C# exchanges them. A null test that is not
the condition of an `if` — inside a `&&`, or assigned to a `bool` — is PALCS0569: the window
it would open has no branch to be the extent of.

**R10.7a.** Inside the window the slot's binder stays `var_n` and `elim_cons` adds a
`B.pts_to var_n`; the non-nullness the branch established is a hypothesis, so R10.2's
refinement is discharged wherever a `C` is expected. That is why `return n` and
`Append(n.next, y)` inside the branch still produce the reference unchanged, with no
re-binding, no projection and no injection.

**R10.7b.** Branch-local mutation has to be written in **tail position**. Two arms that
leave the object in *different* states — one subtree replaced, the other not — cannot be
joined by a statement-position `if`, which has to leave a single state; and each arm has its
own window to close at the state it actually reached. `else if (…) { …; return t; }` is the
ordinary C# for that, and it is a fact about Pulse's `if`, not a restriction §10 adds.

**R10.6a (allocation).** `new Node(v, n)` is R4.12's constructor, unchanged: the argument's
invariant transfers into the field by R3.10b, and R10.4's `intro_cons` is R3.10b's closing
`fold`.

**R10.6b (destructive traversal).** `x.next = Append(x.next, y)` is an ordinary R3.12 field
write inside R10.6's window. This is the case a flat invariant cannot express and the reason
§10 exists.

**R10.7c.** A recursive class's fields are reachable **from outside the class**, which
R3.11 does not otherwise allow (PALCS0523). The licence is exactly R10.7's window: the
client's own null test is what runs `elim_cons`, and `elim_cons` hands back the head cell,
so inside the branch the field is as available to a static method as it is to a method of
the class. Outside any window it is not, and that is PALCS0567. This is why a traversal like
`Lists.Length(Node? n)` can be written as a free function over `n.next` at all, and it is
what keeps the recursive class free of a method per traversal.

### 10.7 Handle classes

**R10.8.** A class holding a recursive class as a field is an *ordinary* M2 class. R3.10b
applies verbatim; only the name of the contributed predicate changes, from `class_C__inv`
to `class_C__inv_opt` (F41). So

```csharp
public sealed class LinkedList
{
    private Node? head;
    [Model] private SpecList<SpecInt> Items => head!.Elements;

    [Ensures("@this.Elements == SpecList.Cons(v, Old(@this.Elements))")]
    public void Push(int v) { head = new Node(v, head); }
}
```

needs no rule of its own, and §10 stays confined to the recursive class itself. `Push` is
three rules already written: the field read hands the sub-invariant to the constructor,
R4.12b transfers it, and R10.2b injects the result back into the nullable field.

**R10.8a.** A `preserves` method of a handle class holds only a *share* of its receiver
(R4.11 makes the receiver's permission a parameter), so the sub-invariant it can hand to a
traversal is at that permission too. A traversal such a method calls must therefore be
`[Frac]` — R4.9's ordinary annotation, discharged over a recursive invariant by R10.7's
recursive `share`/`gather`. Nothing is special-cased: a full-permission traversal is simply
a function the owner cannot call, and the message says which permission was wanted.

### 10.8 Back pointers

**R10.10.** A `prev` field breaks the rule §10 rests on. `next` is *owned* — the cell it
points at belongs to this list and to nothing else — but `prev` points at a cell that
already belongs to the list, so owning it would be owning it twice. The predicate cannot be
a function of the fields alone.

The surface answer is one attribute:

```csharp
public sealed class DNode
{
    private int value;
    [Backward] private DNode? prev;
    private DNode? next;

    [Model] private SpecList<SpecInt> Items => SpecList.Cons(value, next.Items);
}
```

`[Backward]` means: **this field is not owned.** It contributes one *index* to the class's
invariant and one pure equation to each node (F43):

```fstar
let rec class_DNode__inv_opt (left: class_DNode__opt) ([@@@mkey] x: class_DNode__opt)
    (p: perm) (m: class_DNode__model)
  : Tot slprop (decreases m)
  = match m with
    | [] -> pure (x == None)
    | hd :: tl ->
      exists* (v: class_DNode) (r: class_DNode__raw).
        pure (x == Some v) **
        B.pts_to v #p r **
        pure (hd == I32.v r.fld_value /\ r.fld_prev == left) **
        class_DNode__inv_opt x r.fld_next p tl
```

Note the recursive call: the current reference becomes the successor's index. Three
consequences, all mechanical:

* Every method over the class gains one **erased implicit** for the index. It is solved by
  unification at every call site including the recursive one, so the user writes nothing.
* `intro_cons` reads the index **off the field** rather than taking it as an argument. That
  is what makes `head.prev = n` a legal proof step: after the write, re-introducing the node
  yields the invariant at the new predecessor with no extra obligation.
* The `[Model]` member does not mention the `[Backward]` field, and R10.5's derivation does
  not look for it. `[Backward]` is what excuses it from PALCS0562.

**`[Backward]` is refused (PALCS0566).** The Pulse shape above is pinned — `RecursiveFacts.fst`
§8 verifies a doubly linked list with `Length` and a `PushFront` that writes the old head's
back pointer — but the *surface* rule is not. A freshly allocated node's predecessor index
has to come from somewhere, and no rule over C# yet says where; §0 rule 3 forbids the
emitter from inventing one, and it forbids inventing a refusal just as firmly, so the
refusal is written down as a rule with its reason rather than left as an approximation.

`[Backward]` is also one more knob, and knobs run out: it makes a *whole* doubly linked
list expressible and a list *segment* no more expressible than before. §12 is the answer to
the general case, and a doubly linked list is delivered there — with the predicate written
by the user rather than derived, which is what a back pointer needed all along.

### 10.9 Status

Pinned end to end by `test/pulse_facts/RecursiveFacts.fst`, in the emitter's own idiom and
before any rule above was written: the singly linked list with `Length`, `Cons` and a
destructive `Append`; recursive `share`/`gather`; the `LinkedList` handle class; the binary
tree with `Size` and an in-place BST `Insert`; and the doubly linked list with `Length` and
a `PushFront` that writes the old head's back pointer.

Delivered end to end from C#: `test/linked_list` (`Node`, `Lists.Length`/`Cons`/`Append`,
the `LinkedList` handle class, and §7.2's `ListsVariant` written at the opposite null-test
polarity) and `test/binary_tree` (`TreeNode`, `Trees.Size`, a functionally correct in-place
BST `Insert`, and §7.2's `TreesVariant`). Both variants verify with no emitter change, which
is what says R10.7's window is a rule about a null test rather than about how the acceptance
test happens to be phrased.

Not covered by the **derived** invariant, and refused rather than approximated: back
pointers (PALCS0566), recursion crossing a hierarchy (PALCS0565), a recursive class that
also owns an array (PALCS0563), *iterative* traversal, and mutual recursion between two
classes.

Two of those refusals are about §10's derivation, not about the language. §12 answers the
back-pointer one by handing the predicate to the user, and §16 answers the iterative one: a
segment predicate **is** the magic wand a traversal needs to give the tail back, and a
traversal written against one needs no rule §5 does not already have. What still has only
R10.7's window is the invariant §10 derives for you.

---

## 11. User-defined specification types

### 11.1 The problem

§10 reads a recursive class's ownership predicate off its `[Model]` member. To do that it
has to know two things about the model's type: what its **empty** constructor is, and what
its **non-empty** one is. Up to here it knew them by *name*: an enum with two cases, `List`
and `Tree`, chosen by matching the C# type against `SpecList<T>` or `SpecTree<T>`, both of
which the compiler recognises as primitives.

That is a bound on the language that has nothing to do with the language. A user whose
model is an association list, a rose tree, a finite map, or anything else has no way to say
so except by patching the compiler — and §0 rule 3 says a proof that needs help gets it
from the user's annotations or from the reusable library, never from a special case in the
translator. A *model type* the translator has to be taught about is exactly such a special
case, and it is one the user cannot reach.

The fix is not to add more primitives. It is to notice, per F44 and F45, that the emitter
never needed a model type at all — only a constructor name and an arity, which the user can
declare.

### 11.2 What a user declares

**R11.1.** A **user-defined specification type** is a C# type carrying `[SpecType(t)]`,
where `t` is the F\* type it denotes. Its type parameters become the F\* type's arguments,
in order. It is a specification-only type in the sense of §8: naming one in a program
method's signature is PALCS0500, exactly as for `Seq<T>`.

```csharp
[SpecType("MyPulse.assoc")]
public readonly struct SpecAssoc<K, V> { … }
```

**R11.2.** A member carrying `[SpecOp(f)]` denotes the F\* term `f`, applied to the
receiver — if it has one — followed by its arguments, left to right. That is one rule for
four C# shapes, because all four are applications:

| C# | Emits |
|---|---|
| `[SpecOp("m.f")] public SpecInt P => …` (property) | `(m.f recv)` |
| `[SpecOp("m.f")] public SpecInt M(A a) => …` (instance method) | `(m.f recv a)` |
| `[SpecOp("m.f")] public static X F(A a, B b) => …` | `(m.f a b)` |
| `[SpecOp("m.C?")] public bool IsC => …` | `(m.C? recv)` |

A discriminator needs no rule of its own: `Cons?` is a prefix function of one argument
(F44), so it is a `[SpecOp]` like any other.

**R11.3.** A static method carrying `[SpecCtor(c)]` denotes the **constructor** `c` of the
type it returns. Constructors are `[SpecOp]`s that are also *declarations*: they are what
§10 inverts, so they are marked separately and carry the extra bit that says which one is
empty.

```csharp
[SpecCtor("MyPulse.Empty", Empty = true)]
public static SpecAssoc<K, V> Nil<K, V>() => throw …;

[SpecCtor("MyPulse.Entry")]
public static SpecAssoc<K, V> Entry<K, V>(K key, V value, SpecAssoc<K, V> rest) => throw …;
```

**R11.1a.** A *specification-type declaration* — a type carrying `[SpecType]`, **or** a
type declaring any `[SpecOp]` or `[SpecCtor]` member — is skipped wholesale by the
frontend, along with every member of it.

This is not an optimisation, it is what lets a user write a specification type in an
ordinary source file beside the code that uses it. Such a declaration is not a program and
cannot survive being read as one: its members have no bodies (each says what it means in
F\* and throws), their signatures mention specification-only types in executable position,
and they carry open type parameters that no translated method may have. Without R11.1a the
first thing a user sees on declaring a spec type is a storm of PALCS0001 and PALCS0500
about code they never asked to have translated.

**R11.1b.** The placement of the three attributes is checked in its own pass, *before*
R11.1a makes the declaration invisible. The pass has to be separate for exactly that
reason: nothing downstream ever sees a spec-type declaration, so an attribute in the wrong
place would otherwise be silently ignored, and the first symptom would be PALCS0573 at some
distant *use* — a message pointing away from the mistake. It reports:

* PALCS0570 — `[SpecType]` on a type that also carries `[Model]` or `[Invariant]`;
* PALCS0571 — `[SpecCtor]` that is not a static method returning a `[SpecType]`, or
  `[SpecOp]` on a member of a type that is neither a `[SpecType]` nor the class declaring
  that type's constructors.

**R11.4.** The F\* side is the user's. It reaches the generated modules by
`[assembly: IncludePulse]` (§7), or by already being on the include path — the translator
emits the name it was given and does not check that it exists, because that is F\*'s job
and F\* does it better. A misspelling is a type error in the generated module with the C#
attribute's text in it, which is where it can be read.

### 11.3 What the compiler stops knowing

**R11.5.** `RecursiveShape` is deleted. In its place a recursive class carries a
**model shape** — three strings and an arity, all of them read off `[SpecCtor]`:

| Field | Meaning | For `SpecList<T>` | For `SpecAssoc<K,V>` |
|---|---|---|---|
| `Empty` | the empty constructor, as a term and as a pattern | `Nil` | `MyPulse.Empty` |
| `Cons` | the non-empty constructor | `Cons` | `MyPulse.Entry` |
| `ConsTest` | its discriminator | `Cons?` | `MyPulse.Entry?` |

`ConsTest` is derived, not declared: it is `Cons` with `?` appended, which is F\*'s rule and
not ours. Everything §10 emits — `NilPattern`, `NilTerm`, `ConsPattern`, `ConsTerm`,
`ConsTest` — becomes a function of this record, and the emitter's two-way branch on an enum
disappears.

F44 is what makes the `SpecList` column say `Nil` and `Cons` rather than `[]` and `::`.
Writing the *prefix* form everywhere is what lets one template serve both, and it costs
nothing: F\* prints either.

**R11.6.** A model shape's `Cons` may have **any** arity ≥ 1, with any mixture of pure and
recursive arguments, subject to R10.5's existing rule that each recursive field appears
exactly once. F45 pins the case that neither built-in shape can express — two pure
arguments and one recursive one — and it needs no new proof step: the non-empty case of the
invariant gets one `pure` equation per pure argument and one recursive conjunct per
recursive argument, which is what the template already said.

**R11.7.** `SpecTree<T>` stops being a primitive and is **re-declared in the annotation
library** using R11.1–R11.3, pointing at `Pulse.Lib.CSharp.Tree`. It keeps its name, its
members and its behaviour; what changes is that nothing in the compiler mentions it. This
is the test of the mechanism: if a type the compiler used to special-case can be expressed
without the special case, and `test/binary_tree` verifies unchanged, then the mechanism is
at least as expressive as what it replaces.

`SpecList<T>` **stays built-in**, and deliberately. It is F\*'s `list`, whose theory is in
`FStar.List.Tot` and whose operations the translator already maps; a user's first model
type should not require them to write an F\* module. The point of R11.5 is that this is now
a *convenience* rather than a *limit* — the built-in path and the attribute path produce the
same `IrModelShape`, and there is exactly one downstream mechanism.

### 11.4 Rejections

| Id | Refused |
|---|---|
| PALCS0570 | `[SpecType]` on a type that also has a `[Model]`, or is otherwise a translated class. A specification type has no representation. |
| PALCS0571 | A `[SpecCtor]` on a method whose return type is not a `[SpecType]`, or a `[SpecOp]` on a member of a type that is not one. |
| PALCS0572 | A `[SpecType]` used as a recursive class's model with no `[SpecCtor(Empty = true)]`, or with more than one. A null reference has to denote exactly one thing. |
| PALCS0573 | A member of a `[SpecType]` used in a specification without `[SpecOp]` or `[SpecCtor]`. The translator will not guess an F\* name from a C# one — that is the mistake §0 rule 3 is about, and a silently wrong name is worse than a refusal. |

PALCS0573 is the load-bearing one. It is what makes the mechanism *total*: every member of
a user's specification type either declares what it means in F\*, or is refused. There is no
path by which a member is translated to something the user did not write down.

### 11.5 Status

Pinned by `test/pulse_facts/UserSpecFacts.fst` before any of the above was written: the
prefix-constructor facts, a user-declared inductive with a two-pure/one-recursive
constructor, its inductive invariant, its eight lemmas, a recursive traversal and a
destructive traversal that writes a field inside the window.

Delivered end to end from C#: `test/user_spec_type`, whose model type is declared entirely
in the user's own file — an F\* inductive supplied through `[assembly: IncludePulse]` and a
C# surface over it carrying `[SpecType]`, `[SpecCtor]` and `[SpecOp]` — and consumed by a
recursive class the compiler translates with no knowledge of either. `SpecTree<T>` is
re-declared through the same mechanism, and `test/binary_tree` verifies unchanged.

The §7.2 detectors both apply. `test/user_spec_type/AssocsVariant.cs` is an equivalent
program written with every null test at the opposite polarity, the empty case in the
`else`, the model operations reached as instance members where the original reached them
as statics and the reverse, results bound to locals before being returned, and the key
comparison written the other way round; it verifies with no emitter change. Four
diagnostics cases cover PALCS0570–0573.

What is *not* delivered: a user cannot yet declare a spec type whose recursive constructor
has more than one recursive argument in a *class* (§10's window opens one sub-object), and
the iterative traversal of §10.7 is still refused. Neither is a limit of §11 — both are
§10's, and §11 does not make them worse. §16 discharges the second for a §12 predicate,
using a §11 spec type (`SpecFrame<T>`) to name the spine it walks.

---

## 12. User-defined ownership predicates

### 12.1 The problem

§10 derives a class's ownership predicate from its `[Model]`: one downward fold over one
recursive field. §11 lets the *model type* be the user's. Neither lets the **predicate** be
the user's, and there are structures for which no derivation can produce it.

The driving example is a **doubly linked list segment**. A segment breaks §10 three ways,
and the three are independent:

1. It is bounded at **both** ends. It carries boundary parameters — where the segment stops,
   and which node is its last — that no fold over the class's fields could produce, because
   they are not properties of the data at all: they are chosen by whoever states the
   specification.
2. Its empty case is `from == to`, a **relation between two parameters**, not `x == None`, a
   property of one. So a C# `if (x == null)` means something strictly weaker than §10
   assumes as soon as segments are in play — R10.7's case lemma is sound only when the right
   boundary is `null`, that is only for a whole list.
3. Its central lemma — that two adjacent segments compose — is a statement about **two
   instances of the predicate at once**, proved by induction. No amount of reading a
   `[Model]` backwards produces it.

And the `prev` field breaks the ownership discipline outright, for the reason R10.10 gives:
`next` is owned, `prev` points at a cell the node before it already owns. The standard
answer is that a back pointer is **constrained, not owned** — a `pure` equation the
predicate carries — and a predicate the compiler derives can only own what it folds over.

So §12 is the third and last link in a chain: §7 brings your own *module*, §11 brings your
own *model type*, §12 brings your own *ownership predicate*. It is the direct analogue of
PAL's `_plain` + `_include_pulse` + `_refine_value` + `_ghost_stmt`
(`pal/test/recursive_struct/recursive_struct.c`), and it exists for the same reason: the
general case has to be reachable without patching the compiler.

### 12.2 `[Plain]`: a class the translator derives nothing about

**R12.1.** A class carrying `[Plain]` is translated to its **representation and nothing
else**:

```fstar
noeq type class_DNode__raw = {
  fld_value: I32.t;
  fld_prev: class_DNode__opt;
  fld_next: class_DNode__opt;
}
and class_DNode = B.box class_DNode__raw
and class_DNode__opt = option class_DNode
```

That is the whole module. No `[Model]`, no `__inv`, no `intro_nil`/`elim_cons`/`cases`, no
`__as_opt`, no constructor. Everything §10 would have derived becomes the user's
obligation, which is the trade: the compiler gives up saying anything, and in exchange the
user may say anything.

Consequently, and mechanically:

* A `[Plain]` parameter contributes a **binder and no resource** to a contract. Nothing is
  owned by virtue of a reference's type; ownership is only ever what a clause says.
* `null` on a plain class is `B.null`, with **no `intro_nil`** — there is no derived
  predicate for a lemma to be about (R12.2).
* A non-null reference used where a nullable one is expected is the reference itself, by
  R10.2's subtyping, with **no `__as_opt`** — there is no invariant to re-read.
* A method returning a plain class returns a **bare reference**: no existentially quantified
  result model, no `__inv` conjunct. `Result` denotes the reference itself.

Two refusals, both about combining `[Plain]` with something that presupposes a derivation:

* **PALCS0574** — `[Plain]` together with `[Model]`. They are two answers to one question.
* **PALCS0575** — a `[Plain]` class in a hierarchy. A bare record behind a box has no vtable
  and no invariant, so there is nothing for a base class's encoding to compose with.

### 12.3 `SlProp` clauses, plain windows, plain fields

**R12.2.** A `[SpecOp]` whose C# return type is `SlProp` is an **ownership** clause. Where
it appears in a `[Requires]`, `[Ensures]` or `[Preserves]` it joins the separating
conjunction rather than the `pure`:

```csharp
[SpecOp("DllSeg.seg")]
public static SlProp Seg(DNode? from, DNode? prev, DNode? to, DNode? last,
                         SpecList<SpecInt> values) => throw new InvalidOperationException();
```

```csharp
[Requires("Dll.Seg(from, prev, null, last, xs)")]
[Ensures("Dll.Seg(from, prev, null, last, xs)")]
```

becomes `requires (DllSeg.seg var_from var_prev None var_last (reveal var_xs)) ** …`. The
decision is made purely by the C# return type, and it is the only new thing a contract can
say. Note the idiom on the Pulse side: the named wrapper is `unfold`, so slprop matching —
which is syntactic — still sees the underlying `dll_seg` and every lemma written about it
applies to a contract written in terms of the wrapper.

**R12.3.** Inside a method body, three rules, each the corresponding §10 rule with the
proof steps deleted:

| C# | Pulse |
|---|---|
| `x == null` / `x != null` in value position | `None? x` / `Some? x` |
| `if (x == null) A else B` | `if (None? x) { A } else { B }` — **no `cases`, no `elim_cons`, no `intro_cons`**; the `else` branch knows only that `x` is `Some`, which is what makes `x.f` mean something there |
| `x.f`, `x.f = e` | the same box read and box write as R3.8, reached through a value slot |

Whether a field read or write inside the window is *owned* is the user's predicate's
business, and a missing `pts_to` is a failure in their annotations. That is §0 rule 3 read
in the intended direction: the emitter neither invents the proof step nor invents the
refusal.

The `prev` write is where this pays off. Because the user's predicate only ever
**constrained** `prev` with a `pure` equation, overwriting it costs nothing: re-closing the
segment simply reports what the field now holds. A derived predicate could not have offered
this, because it would have had to own the field it folded over.

**R12.3b (a plain reference the body assigns is a cell).** R5.2 gives every assigned local a
`let mut`, and a local that happens to hold a class reference is not an exception. Its slot
is a cell and its resource is an ordinary `R.pts_to`; a field read through it reads the cell
first and projects the box out of what was read. This is what a *cursor* is — a reference
the loop moves — and it needs no rule of its own, only the ordinary one not being skipped
because the local holds a reference.

**R12.3c (a plain class's null test is an ordinary comparison).** R10.7 confines a null test
to the whole condition of an `if` because that `if` is the *extent of a window* — the region
in which §10's case lemmas have been applied. A `[Plain]` class has no derived invariant and
so no window: §12 gave the ownership of the record to the user's predicate, and whether it
is held at a given point is that predicate's business. So PALCS0569 and PALCS0567 both step
aside for a plain class, the projection is emitted, and Pulse checks the `Some?` refinement
against whatever the user's annotations establish — a loop guard, a `[Lemma]` call, an `if`.

Keeping the restriction would have been the emitter inventing a **refusal** (§0 rule 3, read
in its second direction). A cursor's null test is a *loop condition*; no window can be the
extent of a loop condition, so the rule would have ruled out every iterative traversal on
the strength of a constraint whose reason does not apply.

**R12.4.** `new C { f = e, … }` on a plain class allocates: the record is built exactly as
R3.5 builds a struct's, then boxed with `B.alloc`. **Object-initializer syntax only** — a
constructor call is refused with a diagnostic, because a constructor has a *body*, and
reading a body to learn which parameter lands in which field is precisely the deriving §12
does not do. The initializer says it outright.

The allocation is emitted **at the local's own binder**, not at a fresh one it is then
copied from: Pulse matches resources by name, so a copy would leave the context holding
`pts_to t0 _` while every later mention asked for `pts_to var_node _`. This is the same
reason R3.8's alias case shares a slot rather than rebinding one.

### 12.4 What the user supplies

Everything §10 would have derived, written in Pulse through `[assembly: IncludePulseFile]`
(R12.6) and named from C# through `[SpecOp]`, and applied in bodies through `[Lemma]` calls
(R12.7). For the doubly linked list that is the predicate

```fstar
let rec dll_seg (p: perm) ([@@@mkey] from) (prev) (to_) (last) (l: list int)
  : Tot slprop (decreases l)
  = match l with
    | [] -> pure (from == to_ /\ prev == last)
    | hd :: tl ->
      exists* v r.
        pure (from == Some v) ** B.pts_to v #p r **
        pure (hd == I32.v r.fld_value /\ r.fld_prev == prev) **
        dll_seg p r.fld_next from to_ last tl
```

and eight lemmas: `intro_nil`, `elim_nil`, `some`, `elim_cons`, `intro_cons`, `append`,
`snoc` and `cases`. Three of them are worth naming:

* **`append`** — two adjacent segments make one, by induction on the first. This is the
  lemma no `[Model]` could produce.
* **`snoc`** — extending a segment on the right, which is the step an *iterative* traversal
  takes when it advances its cursor. It is what §10.7's refused iterative traversal was
  missing, and §12 is where it can be written.
* **`cases`** — the `if (x == null)` connection, valid *only* when the right boundary is
  `None`. §12 refuses to derive it and makes the user state and prove it, which is the whole
  of point 2 above made concrete.

Three shapes recur in the lemma statements and are worth pinning, because getting them
wrong produces failures that look like unrelated problems:

* An `ensures` cannot mention `L.hd l` — `Cons? l` is not in scope there. Existentially
  quantify the tail and state `pure (l == I32.v r.fld_value :: tl)`, which is the idiom the
  emitter already uses.
* A binder introduced by `with r.` is **ghost** and cannot feed a stateful call or a box
  write. The node has to be *read* (`let node = B.op_Bang from`), which is exactly what the
  emitter does anyway (R3.8).
* `elim_cons` should state its `pts_to` **at the cursor the caller passed**, so that the C#
  body can read a field of a *program* pointer. Under R10.2 that is automatic: the cursor is
  the pointer. (Before R10.2 it needed a refined binder `(from: …__opt { Some? from })` and
  a `rewrite each v as (Some?.v from)`, plus a separate preserving lemma to establish
  `Some? from` in the first place — all three are gone.)

### 12.5 The C# face of a user predicate

§12.4 as first delivered had two blemishes. The predicate and its lemmas were a ~190-line
string literal inside an attribute argument, so no editor gave them syntax highlighting,
type checking, or a jump-to-definition; and every proof step in a body was a raw
`Pal.GhostStmt("…")`, so the caller repeated the callee's binder names, `rewrite`s and
`with`s in a language the C# compiler cannot see. Both are fixed by giving the predicate a
C# *face*, and the fix is a style rule as much as it is two translation rules.

**R12.6.** `[assembly: IncludePulseFile("path")]` is `[assembly: IncludePulse]` (§2) with
the text read from a file beside the annotated source rather than written inline. The path is
resolved relative to the file carrying the attribute; the module name is the file's base
name, and a `module` header inside the file that disagrees with it is an error (PALCS0584),
as is a file that cannot be read (PALCS0583). The emitted module is byte-for-byte the file's
contents, exactly as `IncludePulse` emits the literal's. Nothing else changes: a `.fst` in the source
tree is an ordinary F* file, so `fstar.fst.config.json`, IDE mode and `--cache_checked_modules`
all work on it with no special arrangement.

**R12.7.** A `[Lemma]` whose contract mentions **any** `SlProp` clause is emitted as a Pulse
`ghost fn` rather than an F* `Lemma`: the `SlProp` clauses become the resource conjuncts,
joined with `**`, and the remaining pure clauses are collected into a single trailing
`pure (…)`. A `[Lemma]` with no `SlProp` clause is emitted exactly as before, byte for byte.
The call site needs nothing new — R5.11 already emits a lemma application as `Module.name
args;`, which is also how a Pulse `ghost fn` is called. Ghost parameters are declared
`Ghost<T>` and erase to the underlying type, as everywhere else.

Together these turn a proof step into a C# call:

```csharp
DllProof.Open(from, from!, prev, null, last, xs);
int rest = Length(from.next, from, last);
DllProof.Close(from, from!, prev, null, last, xs);
```

**R12.7b (a `ghost fn` lemma's postcondition is read under its precondition).** R4.8 already
says this of a method: a Pulse `ensures` is type-checked with the `requires` *not* in scope,
so a postcondition that mentions `l[i]` is ill-typed until `i < l.Length` is restated as a
hypothesis. A `ghost fn` is a Pulse function, so it needs the same treatment, and a
`[Lemma]` that owns anything is a `ghost fn`. The pure-`Lemma` form is untouched: there the
`requires` *is* in scope, and restating it would only slow the SMT query down.

**The style rule.** *A user predicate publishes one ghost lemma per step a C# body takes,
whose signature mentions only what C# can name — parameters, locals, `null`, spec lists — and
keeps every `with` and every `rewrite` inside the `.fst` file.* The obstacle this navigates
is real and is worth recording, because it is what R12.4's advice about refined binders runs
into. A predicate's cons case is stated over the *nullable* cursor, and a C# body has to read
a field through the very same pointer:

```fstar
unfold
let opened (from: class_DNode__opt)
           (prev to_ last: class_DNode__opt) (l: list int) : slprop
  = exists* (r: class_DNode__raw) (tl: list int).
      B.pts_to from r **
      dll_seg 1.0R r.fld_next from to_ last tl **
      pure (l == I32.v r.fld_value :: tl /\ r.fld_prev == prev)
```

Under R10.2 this is straightforward: `DNode` and `DNode?` are one Pulse type, so the cursor
the contract talks about *is* the reference the field access reads through. The C# call is
`Open(from, …)` and the resulting `B.pts_to` is syntactically at `var_from`, which is what
the emitter's field reads (R10.4) ask for. Note that the tail segment's `prev` is `from`,
which is what lets the recursive call `Length(from.next, from, last)` match with no
`rewrite` at the call site.

> *A cursor is named **once**, which is worth saying because it was not always possible.
> While `C?` was `option class_C`, a non-null cursor needed a binder
> `(from: class_DNode__opt { Some? from })` — a refinement C# cannot declare — so predicates
> named the head twice and every call site read `Open(from, from!, …)`. R10.2 removed the
> two types and with them the two names. The doubling that remains is a different thing and
> is not removable: a value the body learns by **reading the heap** — a `next` field, a
> payload — must be named explicitly if a later step is to take it back as an ordinary
> argument (F73).*

One convention has to be observed on the F* side. R4.13 sends a C# `int` into a
specification as its mathematical value, so a predicate parameter a C# `[SpecOp]` passes an
`int` to must be declared `int`, not `I32.t`, with the machine value existentially bound:

```fstar
unfold
let cell (v: class_DNode) (value: int) (prev next: class_DNode__opt) : slprop
  = exists* (x: I32.t).
      B.pts_to v ({ fld_value = x; fld_prev = prev; fld_next = next }) **
      pure (I32.v x == value)
```

Declaring the C# parameter `SpecInt` rather than `int` says the same thing on the C# side and
is the clearer of the two.

### 12.6 Status

Pinned first, and independently of the compiler, by `test/pulse_facts/SegmentFacts.fst`:
§§1–5 give the representation exactly as the emitter produces it, `dll_seg`, the whole-list
wrapper, all eight lemmas, a forward traversal and a `push_front` that writes the old head's
back pointer; §6 pins R12.7's C# face — `opened`, `cell`, `seg_open`, `seg_close`, `seg_cons`
— and redoes both worked programs with **no `with` and no `rewrite` in the caller**. That
§6 verified on the first attempt is the fact the whole of M10 rests on: Pulse's matcher does
cope with the read-then-recurse pattern, so the only thing the lemmas must absorb is the
nullable-cursor-to-boxed-node conversion.

Delivered end to end from C#: `test/dll_segment`. `DllSeg.fst` is the predicate and its
lemmas as a real F* file, pulled in by `[assembly: IncludePulseFile("DllSeg.fst")]`. `Dll.cs`
declares `[Plain] DNode`, gives the predicate a C# face as four `SlProp`-valued `[SpecOp]`s,
and publishes four `[Lemma]`s — `Cases`, `Open`, `Close`, `Cons` — one per step a body takes.
`DllOps.cs` has a recursive `Length` over a segment and a `PushFront` that allocates a node
and **writes the old head's back pointer** — the operation a doubly linked list exists for,
and the one §10 could not reach at all. Between them the two bodies contain exactly one raw
`Pal.GhostStmt`, `unreachable ()`, in a branch the user's own `Cases` lemma has just shown to
be dead.

The §7.2 detector applies: `DllOpsVariant.cs` is the same two operations written with the
null tests inverted and their branches swapped, the cursor read into a local before the
recursive call, the allocation moved past the case split, the locals renamed and the addition
written the other way round — and with the null test spelled the other way about, which
R10.2c makes the same translation. It verifies with no emitter change. Two
diagnostics cases cover PALCS0574 and PALCS0575.

What §12 does *not* do is make the proofs disappear. A segment operation still costs the user
four or five explicit proof steps. What R12.7 changes is *where they live and what they look
like*: they are now typed C# calls to lemmas the predicate's author published once, rather
than `rewrite`s the caller has to rediscover. That is §0 rule 3 working as intended — the
difficulty is in the user's annotations and in a reusable library, visible and editable,
rather than in a special case in the emitter. The cheap path remains §10, and §11 widens what
§10 can be cheap about; §12 is what you reach for when neither will do.

---

## 13. Conversions, side effects, and a production case study

§§1–12 were exercised on programs written to be verified. §13 is the first section driven
by code that was not: SharpZipLib's `Adler32` (MIT), verified in `examples/adler32`.

That directory is the reason `examples/` exists. An example and a test run through the
same harness (`test/verify.mk`), carry the same two obligations, and are gated by the same
`make test`; what separates them is provenance. A test is written to exercise a numbered
rule and may be shaped to do so. An example is code that was written for some other
purpose, ported with its adaptations documented and its upstream licence carried alongside
it (`examples/adler32/LICENSE`), and it may not be reshaped to suit the tool. Gating them
identically is the point: an example that is allowed to rot is a claim about pal-csharp
that stopped being true without anyone noticing.

The target was chosen for one reason. Most C# checksums — MurmurHash3, the two common
CRC32s, FNV-1a — rely on **intentional wrapping**, so the obligation pal-csharp discharges
(absence of overflow) is the wrong one for them, and their specification ("it matches the
reference definition") is close to circular. Adler-32 is designed to *avoid* overflow, and
the production source carries a hand-written safety argument in a comment. There is
therefore something specific to check rather than merely a definition to restate.

### 13.1 What the case study found

The comment reads:

```
// We can defer the modulo operation:
// s1 maximally grows from 65521 to 65521 + 255 * 3800
// s2 maximally grows by 3800 * median(s1) = 2090079800 < 2^31
```

Its conclusion is right and its figure is wrong (F54). The true supremum of `s2` is
**2 090 626 020**, larger than the stated 2 090 079 800 by **546 220**, because
"median(s1)" approximates a triangular sum. The comment *understates* the maximum — the
direction that would have mattered had the margin been thinner. The real headroom against
2^31 is 2.65%, not 2.68%. The `s1` claim (max 1 034 520) is correct.

The arithmetic was pinned in `test/pulse_facts/ConversionFacts.fst` **before** any emitter
code was written, per §0. That is the order the discipline requires and it paid: the
case study's headline finding is machine-checked and independent of everything below it.

### 13.2 Rules

| Rule | Construct | Translation |
|---|---|---|
| **R13.1** | explicit numeric cast `(T)e` | `Cast.<src>_to_<tgt> ⟦e⟧`, from `FStar.Int.Cast`. **Modular, with no precondition** (F46). An explicit cast is the programmer *asking* for truncation, and C#'s default `unchecked` context defines it to truncate; demanding `0 <= v < 256` at a `(byte)` cast would be the emitter inventing a refusal for an operation the source language defines (§0 rule 3). A user who wants exactness proves the range and F49 hands it back. |
| **R13.2** | a conversion in *specification* position | the identity on the mathematical value iff every value of the source type is a value of the target (F47) — **not** merely "the target is wider". Otherwise `% pow2 n` (unsigned target) or `FStar.Int.op_At_Percent` (signed) (F48). `Types.RangeFits` decides. |
| **R13.3** | `x++`, `++x`, `x--`, `--x` in expression position | an `IrStmtExpr(prelude, value)`: the write is emitted **at the operator's own position in the tree**, not hoisted to a statement before the enclosing one. The node therefore inherits the emitter's left-to-right operand order and R6.3's short-circuit capture for free, and is faithful by construction with no side condition. Hoisting would have been wrong for `p && a[i++] > 0`. In specification position the construct is refused (PALCS0576): a specification denotes a state and never changes one. |
| **R13.4** | implicit numeric promotion | recorded as an `IrConvert` at the same place reference conversions are. C# evaluates `byte & int` at `int` width — both operands promoted, `int`'s operator applied — and the promotion must be translated or the emitted term is ill-typed. **Literals are re-typed, not converted**: `byte b = 5;` converts at compile time, and emitting a cast would name a runtime operation the program does not perform. |
| **R13.5** | shift | `FStar.UIntN.shift_left` takes a `UInt32.t` amount whatever the operand's width (F51), so the *amount* — and only the amount — carries a conversion. |
| **R13.6** | argument to a `[Spec]` function or `[Lemma]` | a machine argument crosses into the mathematical world exactly when the binder it is passed to lives there. R4.6 makes every `[Spec]` parameter mathematical whatever its C# type; R4.7 leaves a `[Lemma]`'s binders as declared (F55). `IrCall.ParamTypes` carries the declared types so the decision is made per parameter, in one place, for calls from specifications and from code alike. |

R13.6 replaced a blanket rule that coerced every machine argument. That was sound for
`[Spec]` calls, which are the only kind a specification could make before M7, and silently
wrong for a `[Lemma]` with a machine parameter — a combination `examples/adler32` is the first
program to write.

### 13.3 What Adler-32 needed, and where each piece landed

Every gap was closed at the layer §0 rule 3 names, and none in the emitter:

| Gap | Fixed in |
|---|---|
| `Seq.length` unbounded, so `offset + 1` might overflow | `Pulse.Lib.CSharp.Array.arr_length_bound` — **library** |
| nothing tied `A.length buf` to `Seq.length` | `Pal.GhostStmt("Pulse.Lib.Array.pts_to_len $&(buf)")` — **user annotation** (and it forced `$&(…)`, documented in `doc/surface_syntax.md` since M1, to actually be implemented) |
| `(uint)(b & 0xff) <= 255` | `Pulse.Lib.CSharp.Casts.byte_mask_ff_bound`, with an SMTPat **on the idiom** (F53) — **library**, and so free of annotation |
| `(s2 << 16) | s1` denotes `s2 * 65536 + s1` | `Pulse.Lib.CSharp.Casts.logor_shift_disjoint`, likewise patterned on the idiom — **library** |
| the loop maintains congruence, not equality | `ModAdd`/`ModIdem`/`Step` as `[Lemma]`s in the user's own file — **user annotation** |

The last row is the substance of the proof, and it is worth stating plainly, because it is
what makes a deferred-modulo checksum verifiable at all:

> The loop reduces `s1` and `s2` at every chunk boundary; the specification reduces only
> at the end. So what the loop maintains is not equality with the specification but
> **congruence mod BASE** — and congruence is exactly the relation that survives both
> operations the loop performs, adding a byte and reducing.

A corollary caught a real error in a first attempt. `s2 += s1` adds a value that is only
*congruent* to the specification's accumulator, never equal to it, so the step needs
congruence on **both** summands:

```csharp
[Requires("a % BASE == b % BASE")]
[Requires("c % BASE == d % BASE")]
[Ensures("(a + c) % BASE == (b + d) % BASE")]
```

The four-argument form is the honest one; the three-argument form (`c` added to both
sides) is only enough for `s1`.

### 13.4 What was proved

`Func_Adler32_Update` verifies, in two tiers:

* **Tier A — safety.** No array access out of bounds, no arithmetic overflow anywhere,
  including across the deferred modulo. The invariants that carry it are linear in the
  work remaining, which is what lets each survive a single iteration:

  ```csharp
  Pal.Invariant(s1 <= BASE - 1 + 255 * (NMAX - n));
  Pal.Invariant(s2 <= BASE - 1 + (NMAX - n) * S1MAX);
  ```

  The coarse `s2` bound is 3 931 241 520 < 2^32, which is what the `uint` the code
  actually uses requires. The *tight* 2^31 analysis the comment attempts lives in the
  probe, where F54 records that the comment gets it wrong.

* **Tier B — functional correctness.**
  `Result == Adler(Old(Contents(buf)), Old(offset), Old(count))`, where `Adler` is RFC 1950
  §8.2 stated inductively in C# as two `[Spec]` functions. This is the postcondition
  §specreview asks for: it relates the output to the *input*, not merely to a type.

### 13.5 The §7.2 detector

`examples/adler32/Adler32Variant.cs` is the same checksum with the inner loop written as a
`for`, the chunk size chosen by a conditional expression rather than an `if` statement, the
accumulators updated by compound assignment, the outer guard written `!= 0`, and every
local renamed. **It translated with no emitter change** — which is the claim §7.2 exists to
test. It needed five `Pal.Assert`s the original does not, splitting the invariant's
re-establishment into its conjuncts, because the conditional chunk size reaches the solver
as a `match` term it must case-split. That cost is charged in the annotations, where §0
rule 3 says it belongs.

### 13.6 One place fidelity was traded, and why

SharpZipLib writes the inner loop as `while (--n >= 0)`. pal-csharp **translates** that
faithfully after R13.3, but the result is hard to *specify*: Pulse requires the stateful
guard to preserve the invariant, and the natural progress invariant is not stable under the
guard's own decrement. Only inequalities in the weakening direction survive it, and the
body cannot re-establish a tight bound because `n` is stale by one inside the body — the
decrement happened in the guard, not the body. The textbook resolution is to move the
decrement out of the guard, and that is what `examples/adler32/Adler32.cs` does:
`while (n > 0) { …; n--; }`.

This is the one adaptation to the loop, and it is a genuine, reportable limitation rather
than a translation gap. `offset++` inside the array subscript **is** retained, so R13.3 is
still exercised by the real idiom. Two further adaptations are mechanical and touch only
the signature: `ArraySegment<byte>` is spelled out as `(buf, offset, count)`, and the
instance field is passed and returned rather than mutated.

---

## 14. Unconstrained generics

F62–F64 measured the cost of a C# type parameter before this section was written, and the
measurement is what fixes its shape: `Pulse.Lib.CSharp.Array` is already `(#t: Type0)`, a
generic struct is an ordinary parameterised record, and instantiation composes. So generics
add binders and applications to the existing scheme and change no rule that is already here.

### 14.1 What is in scope

**R14.1 — A type parameter is translated exactly when it is unconstrained.** A `where`
clause is a typeclass obligation: `where T : IComparable<T>` says a call to `CompareTo`
must resolve through a dictionary that the caller supplies, and neither the dictionary nor
its coherence has been probed. A constrained type parameter is refused (PALCS0580) rather
than translated with the constraint dropped, because dropping it would silently admit a
program whose body cannot be written.

This is a smaller subset than it sounds, and a well-defined one. C# permits almost nothing
on an unconstrained `T` — no comparison, no arithmetic, no member access, not even `==`.
What is left is the *element-agnostic* part of the language: moving values into and out of
arrays, holding them in a container, counting them, copying them. That is precisely the
part `Span<T>`, `ReadOnlySpan<T>` and `ArraySegment<T>` inhabit, and `examples/adler32`
had to spell its segment out by hand for want of it.

**R14.1b — `Ghost<T>.Value` is transparent.** `Ghost<T>` erases to `T` in a type (R14.1) and
a spec string is bound against parameters that are *already* unwrapped, so a spec string
never writes `.Value` at all. But a specification written in **statement position** —
`Pal.Invariant(…)`, `Pal.Decreases(…)`, a `[Lemma]` argument — is an ordinary C# expression,
where `Ghost<T>` is a real type and C# demands the projection. Nothing about the *meaning*
changes when it is written, so nothing in the translation does either: `g.Value` lowers to
whatever `g` lowers to.

### 14.2 Type parameters are binders

**R14.2 — A method's type parameters become explicit `Type0` binders, ahead of every value
parameter, in declaration order.** `static void Swap<T>(T[] a, int i, int j)` emits

```
fn func_Swap (ty_T: Type0) (var_a: array ty_T) (var_i: I32.t) (var_j: I32.t)
```

A type binder is also bound **in the specification scope**, so R4.9's `$(T)` resolves to
`ty_T` exactly as `$(x)` resolves a value parameter. Without it a generic `[Lemma]` whose
value arguments do not mention `T` — an introduction rule for the empty case of a predicate,
say — has no way to say which type it is about, and the implicit is left as an unresolved
uvar (*"Unexpected unresolved uvars"*). A type parameter is a C# name in scope; `$(…)`
resolves C# names in scope; the rule is the absence of an exception.

They are *explicit*, not implicit `#`-binders, and that is a deliberate choice against the
F* idiom. Roslyn has already resolved the type argument at every call site — for an
inferred call as much as for `Swap<int>(…)`, since C# type inference runs at compile time —
so the translation has the answer in hand and emitting it is structure-preserving. Relying
on F*'s inference instead would make the emitted program's well-typedness depend on a
second inference algorithm agreeing with C#'s, which is a thing to be avoided rather than a
thing to be hoped for. It also keeps a type parameter that appears in no parameter type
translatable rather than being a special case.

Both forms were probed (`test/pulse_facts/GenericFacts.fst` uses implicit binders;
`BinderProbe` confirmed the explicit form, its application at a concrete type, and a generic
caller passing its own type variable along).

**R14.2b — A specification's shim is generic in the same parameters.** R4.x binds an
attribute's spec string by generating a shim method whose parameters are the annotated
method's, and compiling it. A spec on a generic method mentions its type parameters —
`[Ensures("Contents(a) == …")]` on `T[] a` cannot be *typed* without `T` — so the shim
carries the same type parameters, by name. It carries no constraints, and needs none:
R14.1 admits only unconstrained parameters, so a spec that would require one is already
refused at the declaration. This is the only place in the pipeline where generics are not
simply "a type like any other", and it is a consequence of specs being bound as real C#
rather than parsed.

**R14.3 — A type parameter `T` is named `ty_T` in Pulse.** F* reserves an initial capital
for constructors and modules, so `T` cannot be a binder name. The prefix follows the
existing conventions (`var_`, `spec_`, `class_`, `struct_`), and the C# name is preserved
after it so that a message about `ty_T` is legible to someone reading `T`.

**R14.4 — A type parameter in type position renders as its binder name.** `T` is `ty_T`,
`T[]` is `array ty_T`, `Seq<T>` is `Seq.seq ty_T`. Nothing else in §3 changes: the type
parameter is a type like any other, and every rule that maps over a type maps over it.

### 14.3 Call sites

**R14.5 — A call to a generic method applies its type arguments first, positionally, in
declaration order.** `Swap(a, i, j)` inside a method with its own `T` emits
`func_Swap ty_T var_a var_i var_j`; `Swap<int>(b, 0, 1)` emits `func_Swap I32.t var_b 0l 1l`.
The arguments come from Roslyn's resolved symbol, so an inferred call and an explicit one
are translated identically — as they should be, being the same call.

This is the rule that keeps R2.x's module-per-method structure intact. F64 pins that
instantiation composes, so nothing needs specialising: one `Func_` module per generic
method, called at every instantiation, exactly as a non-generic method is.

It applies to all three kinds of callee, because all three are the same IR node: a method
(`func_`), a `[Spec]` function (`spec_`) and a `[Lemma]` (`lemma_`). Each therefore takes
its type binders ahead of its value binders by R14.2, and each is applied to its type
arguments here. A generic `[Spec]` function is worth calling out: it is what lets the
*specification* of a generic method be written once — `Interchanged<T>(s, i, j)` is a
sequence-valued function of `T`, and without R14.2 on spec functions every postcondition
would have to be inlined at each use.

### 14.4 What is refused

Each of these is a refusal to *translate* — a construct with no image under the rules above
— and not a prediction that a proof will fail (§0 rule 3):

* **A constraint (PALCS0580).** R14.1. Includes `where T : class`, `struct`, `new()`, a base
  type and an interface: each says something about `T` that the translation would have to
  carry, and none has been probed.
* **A generic type declaration (PALCS0581).** A generic `class` or `struct` needs a
  parameterised record *and* a parameterised invariant, and §3.4's class encoding fixes the
  representation type at the reference type. F63 shows the record is available; the
  invariant is not yet designed, so the declaration is refused rather than half-translated.
  A generic *method* on a non-generic type is unaffected, which is where the value is.
* **A generic local function or lambda.** Neither exists in the supported subset already.

A type parameter used as the receiver of anything, or compared with `==`, needs no rule
here: C# itself rejects it, so it cannot reach the translation.

---

## 15. Generic types

M8 refused a generic class or struct declaration (PALCS0581) on a stated ground: the record
is representable (F63), but "the invariant and the ownership predicate of a type
parameterised by a type have not been designed". F66–F70 design them. The refusal was
honest and is now discharged, which is the only way a refusal in this document is ever
meant to be removed.

The whole of §15 is one observation. A class's F\* image is a *family* of definitions — a
record, two abbreviations, a model type, an invariant, six case lemmas, two permission
lemmas — and every one of them either mentions the class's representation type or is a
predicate over it. So parameterising the class parameterises all of them uniformly, and the
question is only where the argument has to be written down.

### 15.1 Where the parameter is written

**R15.1 — A class's or struct's type parameters become binders on every definition its
module emits, in declaration order.** The record, the `box` abbreviation, the `option`
abbreviation, the model type, the invariant, the case lemmas and the share/gather lemmas
all take them. R14.1 applies unchanged: a constrained parameter is refused (PALCS0580).

**R15.2 — On a *type* definition the binders are explicit; on everything else they are
implicit.** This is the one rule of §15 with a choice in it, and F68 is why it goes this
way.

A type has no value argument to infer from, so `class_Node__opt` must be applied: a method
binder reads `(var_n: class_Node__opt ty_T)`. Everything else — the invariant, and all
eight lemmas — has a value argument whose type already mentions the parameter, so the
argument is determined by unification with something the emitter is writing down anyway.
Making it explicit would be writing the same information twice.

That is not a stylistic preference. §10's client rules emit lemma calls by the hundred
(`class_Node__cases var_n;`, `class_Node__elim_cons var_n;`, `class_Node__intro_cons
var_n;`), each in a context where the emitter has a *C#* type in hand and would have to
render its F\* image to supply an argument. Under R15.2 not one of those call sites
changes. The client half of §15 is therefore almost empty, and that is the rule's whole
justification.

Contrast R14.2, which made a *method*'s type parameter explicit. The two rules disagree
because the two situations do: Roslyn resolved a method's type argument and the emitter has
it, whereas a generated lemma's type argument is a function of an argument already present.
Neither rule is asking F\* to guess.

**R15.3 — A class type is named with its type arguments applied.** `Node<T>` inside a
generic method is `class_Node__opt ty_T`; `Node<int>` in a non-generic one is
`class_Node__opt I32.t`. The arguments come from Roslyn's constructed type symbol, so — as
in R14.5 — an inferred instantiation and a written one are indistinguishable by the time
the translator sees them.

**R15.4 — The recursion is at the same type argument.** A recursive field of `Node<T>` has
type `Node<T>?`, never `Node<U>?`, because that is what C# writes: a field's type is a type
in the class's own scope. So the mutually recursive group is parameterised uniformly and
F66's well-foundedness argument is the monomorphic one.

This is worth stating because the alternative — *non-uniform* (polymorphic) recursion, as
in `Nest<T> { Nest<(T,T)>? next; }` — is expressible in C# and has no `type … and …` image
at all. It is refused (PALCS0582): a field whose type instantiates the enclosing class at
anything but its own parameters.

### 15.2 What the model is

**R15.5 — A generic class's model type is parameterised by the same parameters.** R10.5
reads the `[Model]` member backwards to obtain the induction, and the constructor
application it reads is now at the element type: `SpecList.Cons(value, next!.Items)` where
`value` is a `T` gives `list ty_T`, and the pure conjunct relating the head to the field is
`m0 == r.fld_value` rather than R6's `I32.v r.fld_value`, because there is no conversion to
apply at an abstract type.

That last clause is not a special case. §6 puts `I32.v` on an integer field because a C#
`int` field and its `SpecInt` model are different types; a `T` field and its `T` model are
the *same* type, so the identity is what §6 already prescribes.

### 15.3 Saying things about an abstract value

**R15.6 — Equality on a type parameter is `Pal.Same(a, b)`.** C# refuses `a == b` on an
unconstrained `T`, so a specification that needs it has nothing to write; `Pal.Same` is a
`[Spec]`-level intrinsic that lowers to `BinOp.Eq` and is otherwise a `==`. It exists for
exactly the reason the rest of §15 does: the C# surface is missing an operator that the F\*
image has, and the annotation layer is where that gap is filled.

`test/generic_tree`'s `GetOr` is the case: it returns a `T`, and
`Pal.Same(Result, SpecTree.Get(t.Elements, k, fallback))` is its whole postcondition.

**R15.7 — The list vocabulary lives in `Pulse.Lib.CSharp.List`.** `SpecList.Take`, `Drop`,
`InsertAt`, `RemoveAt` and `Reverse` denote `CL.take`, `CL.drop`, `CL.insert_at`,
`CL.remove_at` and `CL.rev`. Every one is **total and takes an `int`, never a refined
`nat`**, and that is a rule rather than an omission: R3.9b puts a method's precondition in a
*later* conjunct than the postcondition that mentions these terms, so `CL.take m (I32.v
var_i)` has to be well typed where a bound on `var_i` is not yet available. Clamping a
negative or oversized index is therefore part of the specification, and the library says
what the clamp does.

**R15.8 — `null` at a generic class is named before it is introduced.** `None` says nothing
about what it is empty *of*, so R15.2's implicit type argument to `class_C__intro_nil` has
nothing to resolve against. The emitter binds it first, at its type
(`let t : class_C__opt ty_T = None;`), and introduces the invariant at the binder. A
monomorphic class has no ambiguity and keeps the shorter form, so every pre-M9 emission is
byte-identical.

**R15.9 — A type in argument position is bracketed.** `tree (kv ty_T)`, not `tree kv ty_T`.
This is R15.3 applied one level down, and it is what makes a *nested* generic specification
type — a map is `SpecTree<SpecKv<T>>` — render correctly.

### 15.4 What stays refused

* **A constrained type parameter (PALCS0580).** R14.1, unchanged. This is what keeps an
  ordered container generic in its *value* and concrete in its *key*: a `TreeNode<T>` with
  an `int key` and a `T value` is a map, is fully general in what it stores, and needs no
  comparison on `T` at all. A `TreeNode<T>` ordered *by* `T` needs `IComparable<T>` and is
  refused.
* **Non-uniform recursion (PALCS0582).** R15.4.
* **A generic `struct` (PALCS0581).** A struct is a *value* here: copied at every
  assignment, stored inline in whatever holds it, and represented by R3.4's record rather
  than by a reference with an invariant. Parameterising a record is a different problem
  from parameterising a class and has not been designed.
* **A generic class in a hierarchy (PALCS0581).** §9's vtable is a record whose field types
  mention the class, so parameterising the class parameterises the vtable, and the cast
  lemmas relating a derived record to its base have to be parameterised alongside it.
  Neither is designed. The refusal fires at the derived class too, so that no hierarchy
  anywhere contains a parameterised class.

§11's user-defined specification types are *not* on this list: `[SpecType]` has always been
generic where the F\* type behind it is, and R15.9 is what makes the nested case
(`SpecTree<SpecKv<T>>`) come out right.

### 15.5 What §15 does not reach

Three shapes are expressible in C#, are not about generics at all, and are refused or fail
for reasons §10 and §4 own. They are recorded here because they are what a "complete"
container library runs into, and because the honest response to each is a rule, not an
emitter patch.

* **A field read through a non-null recursive reference.** R10.7 opens a window at a *null
  test*, so a receiver of type `Cell<T>` (not `Cell<T>?`) has no window to be read in.
  This is why `test/generic_list` has no `First`. The rule that would fix it — open a
  non-null receiver directly with `as_opt`, `cases` and `elim_cons` — is designable and is
  not designed.
* **A windowed reference passed as an argument.** R10.7 closes the window at the end of the
  branch, so a reference handed to a call *while open* is handed over open. This is what
  makes an in-place `Reverse` (which passes `x` to its own recursive call after rewriting
  `x.next`) fail, and why `test/generic_list`'s `Reverse` is the persistent one.
* **A `[Consumes]` parameter given away on two different paths.** R4.9c is a statement about
  the *method*: the first consuming use moves the argument, and a second use is PALCS0550
  even when the two are in disjoint branches. Splitting the branches into two methods says
  one thing each, and is what `test/generic_list` does.

The persistent style these push a library towards is not a consolation prize. An operation
that allocates what it returns leaves its argument `[Frac]`-observed, so the caller keeps
the list it passed in — which is the ordinary contract of a container operation in a garbage
collected language, and the one C# programmers expect.

---

## 16. Cursors: iterative traversal

§10.7 refused iterative traversal and gave a reason — *"needs a magic wand to give the tail
back, and has not been probed"*. §12 then answered the first half without noticing: a
**segment** predicate is what a magic wand was wanted for, and `test/dll_segment` already
had one. §16 probes the rest. The refusal is discharged, and it is discharged the way §0
asks — a probe first, then rules, then two acceptance directories and their variants.

The section's one observation is this:

> **The part of a structure a loop has walked is a function of the loop counter, not a
> history.** So it can be *named* in the invariant by a total function of the counter, and
> the loop needs no ghost accumulator, no wand, and no rule beyond R5.8c.

### 16.1 The linear case

`test/list_cursor` walks a singly linked list. The user's Pulse file `CellSeg.fst` declares
one predicate, `seg p from to_ l` — the cells from `from` up to (not including) `to_`, and
the values in them — plus `whole = seg from None`. The loop invariant then owns two halves:

```csharp
Pal.Invariant(Cells.Seg(head, at, SpecList.Take(xs.Value, i)));   // walked
Pal.Invariant(Cells.Held(at, SpecList.Drop(xs.Value, i)));        // remaining
```

`Take` and `Drop` are the two total functions of the counter. Advancing is `seg_snoc` —
moving one cell from the right half to the left — and finishing is `seg_close`, which is the
"magic wand" §10.7 wanted, except that it is an ordinary lemma about an ordinary predicate
and needed no wand at all.

### 16.2 The branching case

`test/tree_cursor` walks a binary search tree. Nothing about the shape of §16.1 changes; the
walked part is just a **one-hole context** rather than a prefix. `KnotPath.fst` declares

| linear | branching |
|---|---|
| `SpecList.Take(xs, i)` | `Descent.Ctx(t, key, n)` — the spine, outermost-first |
| `SpecList.Drop(xs, i)` | `Descent.Sub(t, key, n)` — the subtree still to search |
| `Append` | `plug c sub` |
| `seg_snoc` | `path_append` — one frame appended to the spine |
| `seg_close` | `path_close` |

The frame carries the node's key, its value, and **the off-path child**, so a step down owns
the sibling subtree it did not take. A descent's path is in general path-dependent, but a
*search* path is determined by the tree and the key, both of which are fixed for the loop —
so `Ctx` and `Sub` really are functions of `n`, and a branching cursor needs no more loop
machinery than a linear one.

Two details are worth pinning because they were not obvious:

* **`Sub` and `Ctx` recurse on the tree, not the counter** (`decreases t`), so `n` stays an
  unrefined `int` and no `n <= depth` refinement has to be threaded. They stop early at a
  hit, which is what makes `Sub`'s relationship to `kfind` hold unconditionally.
* **No ordering hypothesis is needed.** `kfind` on a `Branch` is *defined* by comparing the
  key with the entry, so following the comparison is following the definition. An
  out-of-order tree makes lookup useless, not unsound — and a precondition demanding
  sortedness would have been a proof obligation invented for the emitter's convenience.

### 16.3 Rules the cursor needs

**R16.1 — Two exits, no `break`.** `break` is R5.10, which allocates a flag; a loop with a
data-structure invariant does not need it. The device the probe pinned instead: an `int`
local `live` is the loop condition, and the measure is `size(Sub(t, key, n)) + live`. A
descent shrinks the subtree; a stop clears the flag; either strictly decreases the sum. This
is general to any pal-csharp loop with an early exit, and it is written by the user, not by
the emitter.

The measure **must** use the walked structure's size, not the counter: R5.9's case-2
measure bounds a counter by its own type, and a tree has no length by which to bound `n`.
`Pal.Decreases` (R5.9 case 1) is how a user says so.

**R16.2 — Every conjunct of an invariant must be distinguishable by its resource.** Pulse
matches by resource, so two conjuncts of the *same* predicate whose only difference is an
argument the body just read from the heap cannot be told apart. The fix is not a lemma but a
definition: make each conjunct's model half a **total projection** of a model the invariant
already names — `subl t` and `subr t` rather than two existentials. Then the two conjuncts
differ syntactically and the matcher never has to guess.

**R16.3 — An existential reachable only through `pure` can never be solved.** Pulse's
matcher recovers an `exists*` binder from the `pts_to`s it unifies. A binder that appears
*only* inside a `pure (…)` has nothing to be recovered from, and folding such a predicate
fails with *"Cannot check relation with uvars"*. This decides where a machine value may be
hidden:

* a predicate that is **folded** by a body — one that describes an open node — keeps its
  machine field explicit, because the record literal determines it; a wrapper with
  `exists* (k: I32.t)` then hides it for the invariant's benefit, and the matcher recovers
  `k` from the `pts_to`;
* a predicate only ever **matched as a precondition** may take a mathematical `int` with the
  machine value existentially bound, because the caller's context supplies it. `DllSeg.cell`
  is this shape.

R10.2 removed the commonest instance of this rule. Under the option encoding *every*
recursive invariant's cons case bound a node existential reachable only through
`pure (x == Some v)`, so every user predicate imitating one inherited the problem and every
lemma over it needed the cursor twice. The box encoding puts the `pts_to` at the cursor
itself, so nothing has to be recovered. What survives is the case the rule was really about:
a value the body learns by *reading the heap* and a later step takes back as an argument.

**R16.4 — A model-level guard is stated over the model.** R4.13 sends a C# `int` in
specification position into F\* as its `.v`, by *position* and not by declared type, so a
predicate parameter of type `I32.t` is unwritable from a C# contract. The consequence is a
style rule, not a limitation: publish a total projection of the model (`Descent.NodeKey`)
and let the contract compare against **that**. The body's own `key < nk` on machine ints
implies it, because the open-node predicate ties the field to the model. The signatures get
shorter, and the contract stops mentioning machine words.

**R16.5 — A pure lemma call goes first.** A pure `Lemma` placed *last* in a `ghost fn` body
has its postcondition dropped. Call it before the step it justifies.

### 16.4 What is delivered

`test/list_cursor` — `CellSeg.fst`, `Cell.cs` (the `[Plain] Cell<T>`, five `[SpecOp]`s and
six `[Lemma]` steps), `Walks.cs` with an iterative `Count`, and §7.2's `WalksVariant`.

`test/tree_cursor` — `KnotPath.fst`, `Knot.cs` (the `[Plain] Knot<T>`, the `SpecFrame<T>`
spec type with its two `[SpecCtor]`s, and ten `[Lemma]` steps), `Search.cs` with an
iterative BST `Find` proved to return `SpecTree.Get(t, key, fallback)`, and §7.2's
`SearchVariant` — which builds its tree by nesting constructor calls, tests membership
rather than lookup, spells the comparison the other way round, checks equality last, and
names its flag differently. It verifies with no emitter change.

The emitter changes §16 required are R5.8c, R5.8d, R12.3b, R12.3c and R14.2's scope
extension. Every one of them is a rule about a C# construct — an invariant clause, a tail
position, an assigned local, a null test, a name in scope — and none mentions a cursor.
Everything that *is* about cursors is in the user's Pulse file and the user's annotations,
which is what §0 rule 3 asks for and is the whole claim of §16.

### 16.5 What §16 does not reach

* **A cursor that mutates.** Every step here is `[Frac]`-observing or full-permission
  read-only; an iterative in-place insert would have to re-close the spine around a *changed*
  subtree, which is a different `path_close` and is not probed.
* **A cursor over a structure the compiler derives.** §16 is written entirely against §12's
  user-defined predicates. A `[Recursive]` class's derived invariant still has only R10.7's
  window, so §10.7's refusal stands for *derived* structures — narrowed, not removed.
* **`break`.** R16.1's flag is the idiom; making R5.10's flag interact with an owning
  invariant is untried.

## 17. `Span<T>`: a borrowed window

The facts were probed and pinned first (`test/pulse_facts/SliceFacts.fst`, F78–F83), as §0
requires. This section is the scheme they led to.

A `Span<T>` is a **borrowed window** into memory somebody else owns. That is what the C#
type means and it is what `Pulse.Lib.Slice.slice` is, so the two are put together: §17.2
gives the rules, §17.3 the borrow, §17.4 what is refused.

### 17.1 What the probes settled

**A span is a struct that owns memory, so it cannot be a translated struct (F79).** §3.4
rejects a struct field of reference type as `PALCS0511`, because copying the struct would
duplicate ownership of the same memory — and a `Span<T>` is exactly such a struct. Applying
that rule to spans would be correct and useless. A span must therefore be a **slot kind**,
primitive like `T[]`: no field projections, no struct copying, its own row in R4.9's table.
R17.1 makes it one.

**The library is already the right shape (F78).** A `slice t` has a non-ghost `len`, a
`pts_to` over its contents, `split`/`join`, `subslice` with a `subslice_rest` residue,
`share`/`gather`, and an `is_from_array` provenance token. Taking a window and giving it
back are both *derivable* — `SliceFacts` S2 does it — so nothing had to be asked of the
Pulse library. What was missing was only the C# side.

**And the C# side is smaller than it looks.** The question that made this section hard to
write was: C# marks neither the point where a window borrows nor the point where it
returns, and recovering either from flow analysis is a borrow checker, which R10.2b refuses
on principle. Both halves of that turn out to be wrong.

*Borrowing is marked.* `a.AsSpan(1, 3)` is where the author put it, and Roslyn hands it
over as an ordinary expression. No new syntax is needed to take a window because C# already
has the syntax.

*Returning is unmarked because there is nothing to mark.* Ending a borrow has no runtime
content — it is purely a proof step — and a proof step the author writes is a **ghost
statement**, which §12 has supported since M10. So `Pal.Restore(w)` (R17.6), and the borrow
checker never comes up: to choose which restore to emit the translator reads the
*initializer* of the window's local, which is syntax, and reads nothing else.

> ***An earlier draft of this section took a different route,*** and it is recorded because
> the mistake is instructive. Observing that a span which is only passed and indexed *is*
> the array — same address, same length, same contents, same owner — it identified the two,
> translating `Span<T>` to the array slot and refusing every span that was not a whole
> array. That bought three rules which cost nothing to write, and paid for them by refusing
> the operation `Span<T>` exists for: `numbers.AsSpan(1, 3)`, the first thing anyone writes
> with a span, was outside the subset. No further work *inside* the identification could
> have admitted it, because the identification is precisely the assertion that such a span
> does not exist — a boundary correctly drawn around the wrong region. The refusal was
> honest about being a scheme limit rather than a proof failure, which is what §0 rule 3
> asks; what §0 does not ask is that the limit be in a useful place.

**Two mechanical points that survive unchanged.** `s.Length` is an `int` where `Slice.len`
is an `SZ.t`, which is R3.3's bridge again and genuinely free. And Roslyn models `s[i]` as
a call to a `ref T`-returning `get_Item` rather than as an element access, so *recognising*
an element write is frontend work that arrays did not need.

### 17.2 The rules

**R17.1 — `Span<T>` and `ReadOnlySpan<T>` are `Pulse.Lib.Slice.slice`.** `MapType` sends
both, at a mappable element type, to `IrSpanType`, which `Names` renders `S.slice ⟦T⟧`.
`T[]` is unaffected and stays `array ⟦T⟧`. A span is therefore its own slot kind
(`SlotKind.Span`), whose resource is `S.pts_to` rather than `A.pts_to` — which satisfies
F79's requirement that a span be primitive rather than a translated struct by making it
primitive, which is what F79 asked for.

This is what a span *is*: a base, a length and a permission, describing memory somebody
else allocated. A window has a length of its own (R17.3), a base of its own (R17.4) and an
owner who is owed it back (R17.6), and `slice` has all three where `array` has none of
them.

The C#-facing operations live in `Pulse.Lib.CSharp.Span`, an `.fsti` of modeling axioms and
derived operations over the Pulse library, in the style `Pulse.Lib.CSharp.Array`
established — not a new theory. §3.4's struct rules are never reached, because `MapType`
never produces a struct for a span.

**R17.2 — a `ReadOnlySpan<T>` parameter is fractional.** It takes a permission variable and
its post-state model is its pre-state model, which is R4.9's `[Frac]` row. The permission is
the one `[Frac("p")]` names if the parameter carries the attribute, and a generated one
otherwise. Generating it is not a convenience: `ReadOnlySpan<T>` *means* read-only in C#, so
requiring the author to also write `[Frac]` would be the translator asking to be told
something the program already says (§0 rule 3, in the "never invent a refusal" direction).
A `Span<T>` parameter is the full-permission row, and takes `[Frac]` only if written.

**R17.3 — `s.Length` is the span's own length.** `IrLength` again, but emitted as
`Span.length_i32`, which is `Slice.len` composed with R3.3's `SZ.t` → `I32.t` bridge. Like
an array's header field, `Slice.len` is pure and non-ghost, so the guard of a counted `for`
over a span is a pure expression exactly as it is over an array, and R5.9's measure
inference applies unchanged.

The length is the *window's*, not its parent's, which is the point: `a.AsSpan(from, count)`
has length `count`, and a method written over a span never mentions where the window came
from.

**R17.4 — `s[i]` is the slice subscript.** Roslyn models it as a call to a `ref T`-returning
`get_Item` rather than as an element access over an array, so the frontend has to recognise
it; what it lowers to is `IrElement`, emitted as `Span.read` / `Span.write`, with R6.4's two
obligations (`0 <= i` and `i < s.Length`) generated at it unchanged.

`ReadOnlySpan<T>` needs no rule to forbid the write, because C# forbids it: its indexer
returns `ref readonly T` and the C# compiler rejects the assignment. This is the core
invariant paying for itself — the annotated program is an ordinary C# program, so an
ordinary C# rule is available to enforce a separation-logic one.

**R17.6a — a span parameter reaches the specification shim as an array.** §4's shim (the
generated compilation unit that binds spec strings, `SpecBinder`) declares a span parameter
as `T[]` rather than as the span type the method wrote. This is the one place the abandoned
identification survives, and it is forced rather than chosen. `Span<T>` is a
`ref struct`, and C# refuses a `ref struct` inside a lambda — *"cannot use parameter that
has ref-like type inside an anonymous method, lambda expression, query expression, or local
function"*, CS9108 — so a shim that kept the span type would reject every quantified
contract, `Forall((int k) => … Contents(a)[k] …)` being the shape almost every array
contract in `test/` has. With the array type the restriction never arises, and no spec term
changes meaning, because `Pal.Contents` has the same `Seq<T>` for both — the shim binds
names and types for a spec string, and never sees a resource at all, so nothing about
ownership rides on the choice.

The restriction does bite in **statement** position, where there is no shim: a
`Pal.Invariant(Pal.Forall(…))` that mentions a span is a real lambda over a real
`ref struct` and C# rejects it. The idiom is to name the predicate — a `[Spec]` method over
`Seq<T>`, which moves `Pal.Contents(a)` out of the lambda and into an ordinary argument
position — and `test/array_view` uses it for exactly this reason. This is a genuine narrowing of
the surface for spans relative to arrays; it is C#'s and not the scheme's, and §17.5 records
it rather than hiding it.

### 17.3 Creation is a borrow

**R17.5 — every span comes from somewhere, and taking it consumes the source.** There is no
way to make a span out of nothing (R17.7 refuses the one C# offers), so every span
expression in the subset names a source that already owns memory, and taking the window
takes that ownership. Five C# forms, three library operations, one receipt each:

| C# | operation | receipt left in context |
|---|---|---|
| `Span<T> s = a;` and `a.AsSpan()` | `Span.of_array a` | `S.is_from_array a s` |
| `a.AsSpan(i)`, `a.AsSpan(i, n)` | `Span.of_array_range a i n` | `Span.is_range_of a w p i j v` |
| `s.Slice(i)`, `s.Slice(i, n)`, `s[i..j]` | `Span.sub s i n` | `Span.is_sub_of s w p i j v` |

The one-argument forms synthesise the missing length as `source.Length - start`, so
`s.Slice(i)` and `s.Slice(i, s.Length - i)` translate to the same term — two spellings of
one operation, which is what §0's structure-preservation rule requires of them.

The borrow is emitted **at the local's own binder**, not at a fresh temporary the local is
then bound to. This is R12.4's reason verbatim: Pulse matches resources by name (F77), so a
copy would leave the context holding `S.pts_to t0 _` while every later mention of the
window asked for `S.pts_to var_w _`.

Consuming the source is what makes the accounting work, and it is visible in the C# type
system rather than enforced by the translator: while the window is out, the source has no
`pts_to`, so an index of it does not verify. The author gets it back with R17.6.

**R17.6 — `Pal.Restore(w)` ends a borrow.** It is a `[Conditional("PAL")]` ghost statement
(§12), so it is erased by the C# compiler and costs nothing at runtime, and it takes **one**
argument: the window. Which of the three operations R17.5 lists is emitted comes from the
`SpanOrigin` recorded on the local's slot **when the local was declared** — a syntactic
property of its initializer, read once, never a flow analysis. After the restore the slot
leaves scope, so a later use of `w` is "not in scope" rather than an unprovable goal.

One argument suffices because the receipt in context determines everything else. `give_back
w` recovers the parent, the permission, the bounds and both contents by unification
(F80) — so the surface asks the author only for the thing C# cannot tell the translator,
which is *where*.

Getting it wrong fails, and fails locally. Omit the restore and the parent's `pts_to` is
missing where the postcondition needs it. Write it too early and the window's own `pts_to`
is gone at its next use. Both land in the author's annotations, which §0 rule 3 says is
where a proof is fixed. Neither can make a false postcondition provable: the restore is a
library operation with its own precondition, not a translator assumption.

**R17.8 — what the parent holds afterwards is `Pal.Splice`.** After a window over
`[from, to)` is restored, the parent's contents are its old contents with that range
replaced by the window's: `CS.splice (old, from, to, window)` in
`Pulse.Lib.CSharp.Seq`, written `Pal.Splice(Old(Contents(a)), from, to, Contents(a))` in a
contract. `splice` is defined **total**, falling back to the parent when the indices do not
fit, so it can appear in a specification without dragging a refinement along; `splice_index`
and `splice_length` carry `[SMTPat]`, which is what discharges the usual "the window is
zero, everything outside it is untouched" postcondition without a single lemma call.

A read-only window restored unwritten gives the parent back exactly what it had, which is
`splice_same`. So a read-only borrow costs its user nothing beyond the bounds — see
`ReadAt` in `test/array_view`, whose `Contents(a) == Old(Contents(a))` needs no help.

### 17.4 What is refused

**R17.7 — the forms that are not borrows (`PALCS0590`).** The list is short now and every
entry is on it for a reason of its own, not because a rule ran out:

* **`stackalloc`.** An allocation, not a borrow: no `T[]` owns the memory, so there is no
  parent to consume and nothing for `Pal.Restore` to give back. It would need a
  scoped-lifetime allocation rule, interacting with F75's rule about `let mut` and tail
  position.
* **A range on an *array*.** `a[1..3]` where `a` is `int[]` *copies* — C# compiles it to
  `RuntimeHelpers.GetSubArray`, producing a fresh array whose writes are invisible in `a`.
  Translating it as a window would be translating a different program. The refusal is not a
  limitation but a correction, and the diagnostic says so.
* **`^k` in a range.** The from-end index is `s.Length - k`, which is ordinary arithmetic —
  but arithmetic `System.Index`'s conversion performs and the source does not write. §0's
  rule against inventing steps covers arithmetic as much as proofs; supporting it means a
  rule saying what `^k` elaborates to.
* **The implicit `T[]` → `Span<T>` conversion anywhere but a local's initializer.**
  `Wipe(a)` would borrow `a` and hand back a receipt with no name, leaving the array
  unrecoverable and failing far from the cause. The fix is one line the author can see:
  name the borrow, pass the name, restore it. (A Normalize-pass rewrite to
  `Span<T> t = a; Wipe(t); Pal.Restore(t);` would be a legitimate R2-style desugaring and is
  deferred, not rejected.)
* **`Pal.Restore` of a span *parameter*.** A restore returns a window to whoever lent it,
  and R17.6 reads which operation that is off the borrow that created the window. A
  parameter was borrowed in another method, whose receipt this one does not hold.
* **A span local assigned after its declaration.** Not a special case: a span local is bound
  with `let`, not `let mut`, so R7's general assignment rule refuses it. R17.6's origin is a
  property of the initializer, and an assignment would make "which borrow is this" depend on
  the path taken — the borrow checker §17 exists to avoid. A second window gets a second
  name.
* **`CopyTo`, `Fill`, `ToArray`, and `string`'s implicit `ReadOnlySpan<char>`.** Library
  operations with no rule yet; `Span.copy_to` exists in the library for the first of them
  and only the surface is missing.

### 17.5 What §17 does not reach

* **An inline quantified invariant over a span**, per R17.6a: C# forbids a `ref struct`
  inside a lambda (CS9108), so a *statement-position* `Pal.Forall` that mentions a span
  does not compile. Contracts are unaffected (the shim sees an array), and the idiom inside
  a loop is a named `[Spec]` predicate over the `Seq<T>`, which moves `Pal.Contents(s)` out
  of the lambda into ordinary argument position — `test/array_view` uses it in both the
  acceptance file and the variant. Nothing can be done about this from inside the scheme:
  it is a rule of the language the annotated program must keep compiling in.
* **A span-typed return.** A method may take a window and may create one, but may not hand
  one back to its caller: the receipt would have to travel with it, and R17.6 has no way to
  name a borrow the caller did not take. C# itself restricts `ref struct` returns for a
  related reason.
* **A span-typed field**, which C# forbids outright (`Span<T>` is a `ref struct`), so this
  costs nothing.
* **`Memory<T>`, `ArraySegment<T>`, `IEnumerable<T>`.** `ArraySegment<T>` is now expressible
  as a window and is a surface question only; `examples/adler32` still spells its segment out
  as three parameters and no longer has to.
* **The refused forms of R17.7**, each for its own stated reason.

---

## 18. Totality: nothing is dropped, nothing is guessed

Every rule up to here says what some C# construct *becomes*. This section says what
happens to a construct no rule mentions, and it exists because the honest answer, for a
long time, was "nothing, quietly".

The frontend collects by **positive match**. It walks a class's members looking for a
field, an auto-property, a `[Model]`, a `[Spec]` observation, a method; it walks a call
looking for a callee it can name; it walks a binary operator looking for the module that
implements it. Each of those walks ended in a fallthrough — `continue`, or a default — and
a fallthrough is a decision. It decides that a construct the rules do not cover should be
translated as though it were not there.

That is the worst of the three possible answers. A refusal tells the author what the tool
cannot do. A wrong translation is caught by F\*. But a *silent* drop reports
`0 error(s)`, emits a module that looks right, and verifies — proving a theorem about a
program the author did not write. §0 rule 3 forbids inventing a refusal; it does not
license inventing an omission.

A *silent mistranslation* is the same failure one step further along. R9.12b is the
example: a virtual method that both mutates its receiver and returns a value emitted a
dispatching wrapper that declared a return type and dropped the value, so `palcs` reported
`0 error(s)` and wrote Pulse that does not typecheck. It is less dangerous than a silent
drop — F\* rejects it, so no false theorem is proved — but it fails in the wrong place and
in the wrong language. The author asked about C# and is shown an F\* type error inside a
wrapper they did not write and cannot read, at a line number that means nothing to them.

The two have a common cause worth naming, because it is the thing to look for rather than
the thing to fix. Both arise where the emitter *branches*, and both were introduced by
adding code inside a branch that had no business being there. A `moves ? … : …` split
exists to decide how the receiver's invariant is threaded; whether a call produces a value
is an independent question, and R9.12b's defect is that the value-binding was written into
one arm of that split at three separate sites, by three separate people-shaped events, none
of which noticed. **When the same two-armed test recurs, whatever is common to the arms
should be lifted out of it rather than duplicated into it** — not for tidiness, but because
duplicating it is how one copy comes to differ from another.

### 18.1 The two rules

**R18.1 — A construct the frontend does not recognise is refused, not skipped.** Every
positive-match walk is **total**: each case either matches a category the rules name, or
raises a diagnostic that says which construct was not translated and why. There is no
fallthrough that means "ignore this".

This is one rule with five sites, and it is stated once because the five are the same
mistake:

| Walk | The fallthrough that was a decision | Now |
|---|---|---|
| a translated class's members (§3.4, §4.5) | a member matching no category was skipped, so a computed property, an indexer, a `const` field, an operator or an explicit interface implementation vanished | **PALCS0591** names the member and its kind. The computed property has since been *translated* rather than refused — that is R9.20, and it is what R18.1 is for: the report is what turns a silent gap into a named one, and a named one into a feature |
| a call's callee (R4.4) | `KindOf` accepted **any** static ordinary method, including one declared in the BCL, and emitted a call into a module that is never generated | **PALCS0592**: a callee must be declared in this compilation |
| a binary operator's operand type (R6.4) | the module was chosen by the operand's primitive kind, defaulting to `Int32` when the operand was not primitive, so `a == b` on two objects emitted `I32.eq` applied to two boxes | **PALCS0593**: an operator whose operands are not primitive has no module |
| a class's base list (R9.1) | only `BaseType` was inspected, and an interface is not a `BaseType` in Roslyn, so `class C : IFoo` silently forgot `IFoo` | **PALCS0594** until §9 has interfaces |
| a method body's receiver bracket (R4.10) | the `unfold`/`fold` bracket was opened for every instance method, so a body that only called another method on `this` handed it a representation where its contract demands the invariant | **R4.10c**: open it only when a field is named, and **PALCS0597** when a body wants both |
| a class's field declarations (R9.4) | only the declared type and name were read, so an initialiser -- an assignment R4.12 had no statement position for -- was dropped, and the field appeared to be built solely by the constructor | **PALCS0596**, and then R4.12d, which supplied the missing statement position -- the head of every constructor that does not chain -- at which point the diagnostic had nothing left to report and was retired |

**R18.2 — Every name the emitter writes is a name that resolves.** A generated module may
refer to another generated module, to a module of `Pulse.Lib.CSharp.*` or the F\* standard
library, or to a Pulse file the user supplied (§12); to nothing else. This is not a rule
the emitter can be trusted to keep by inspection, so it is **mechanically checked**:
`test/module-refs.sh` reads every qualified reference in every generated file and requires
it to resolve. It is the third detector, beside §7.2's two, and it is the one that catches
a *dangling* emission rather than an invented or an ill-provenanced one.

Two live defects were what earned it. `override int GetHashCode()` on a class with no user
base emitted `Class_Object.class_Object__model`, because the override's base was read off
`BaseType.Name` and every C# class's implicit base is `System.Object`; and
`ReferenceEquals(a, b)` emitted `Func_Object_ReferenceEquals.func_Object_ReferenceEquals`.
Neither module has ever existed. Both programs translated with `0 error(s)`.

**R18.3 — A name is emitted for at most one declaration.** R2.1's qualification by
declaring type keeps method names injective, but a constructor's name is `_ctor`
regardless of its signature, so two constructors of one class collide. Two declarations
competing for one module is not a translation, and until constructors have a
signature-bearing name, a class with more than one constructor is **PALCS0501**, the
existing module-name collision, reported with constructor-specific advice — C# does not
permit "rename one".

R18.3 was already implemented and already firing; the program still crashed with an
unhandled `ArgumentException`, because the emitter runs *despite* errors (§2 poisons the
output through `TranslationErrors.fst`) and diagnostics are printed only after it. The
throw pre-empted every message. So the fix was to make the emitter's dictionaries
collision-proof, not to add a rule: **a diagnostic that a crash outruns is not a
diagnostic**, and any pass that runs after an error must be total in the presence of one.

### 18.2 What is refused, and what each refusal is waiting for

R18.1 turns a silent drop into a diagnostic; it does not by itself translate anything new.
Each of the following is now refused *and* named as a scheme gap, which is the state a
feature has to reach before it can be designed.

* **A property with a `set` accessor, and an indexer** (PALCS0591). The *getter* half of
  this bullet is closed: R9.20 translates a computed property as the method its getter is,
  which was the largest thing R18.1 uncovered and is now the smallest feature in §9,
  because a getter *is* a method of no arguments and needed no new rule beyond finding it.
  A setter is a method of one argument whose name C# chooses, so R9.20b keeps refusing it
  until §4 has a reading of `value` in a specification. An indexer is a property with
  parameters and waits on the same.
* **A `const` field** (PALCS0591). It is a pure value and owns nothing, so it wants no
  invariant; what it wants is to be in scope in a body and in a contract, which is a
  question about §2's module layout rather than about ownership.
* **An explicit interface implementation, an operator, a conversion, an event, a
  finalizer** (PALCS0591). None has a rule, and the first two wait on §9's interfaces.
* **An `override` of a member of `object`** — `GetHashCode`, `Equals`, `ToString`
  (PALCS0591). R9.6 reads an override as the forgetting function of a *translated* base.
  `System.Object` is not translated and has no model, so an override of one of its members
  is not a forgetting function and has no other reading.
* **A call to a method not declared in this compilation** (PALCS0592). This is what makes
  `ReferenceEquals` a diagnostic. It also states, for the first time, the rule the whole
  scheme has assumed: pal-csharp translates a *whole program*, and a method whose body it
  cannot see has no contract it can trust.
* **`==`, `!=` and `ReferenceEquals` on class-typed operands** (PALCS0593, and
  PALCS0592 for `ReferenceEquals`, which is also not declared here).
  Object identity has no story: `Box` has a decidable equality, but nothing relates it to
  the ownership discipline, and two references that are equal are not thereby
  interchangeable in a context that owns one of them.
* **Two members of one program that mangle to one module name** (PALCS0501), per R18.3.
  R2.1a closed the case that motivated this bullet -- a second constructor -- by giving an
  overload set a signature suffix. What is left is a collision R2.1 admits it does not
  resolve: `Alpha.Meter.Read` and `Beta.Meter.Read` are not an overload set, because they
  are not members of one type, and the module name carries no namespace.
* **An `interface` declaration, and an implements clause** (PALCS0594). §8.6 records why
  interfaces are not simply R9.2 plus R9.3: what a C# interface adds is *multiple*
  implementation, and R9.8 pins the obstacle — a `dyn` is made at one witness type and
  `mkdyn` is not injective, so one value cannot be viewed at two unrelated roots.
* **A body that both reads a field of its receiver and calls a method on it** (PALCS0597).
  Not a dropped construct but the same mistake one level down: the bracket was emitted
  unconditionally, so the ill-typed case was emitted too. R4.10c says why the two halves
  cannot be reconciled without the emitter inventing a fold.
* **A `record`** (PALCS0530). A record's primary constructor, its generated `Equals`,
  `GetHashCode`, `ToString` and `Deconstruct`, and its `with` expression are five features
  at once. An *annotated* record now says so; an unannotated one is ignored, like any
  unannotated type — R18.1 governs what the translator was asked to translate, not every
  declaration in the compilation. PALCS0530 previously read "does not translate classes
  yet", a message left over from before §3.4 was built and untrue as stated.

### 18.3 Why this is a section and not a bug list

Everything above could have been fixed one `if` at a time. It is written down as a rule
because the four sites are one mistake made four times, and because the mistake is
*structural*: a compiler assembled from positive matches drops what it does not match, and
will do so again at the fifth site unless the rule is that a walk must be total.

That also fixes what the refusals mean. §0 rule 3 says the frontend refuses what it cannot
*translate*, never what it predicts will not *prove*. Every diagnostic in §18 is the first
kind, and each names a construct with no image under any rule in this document — which is
also why each is listed in §18.2 with the rule that would have to exist for it to be
accepted.
