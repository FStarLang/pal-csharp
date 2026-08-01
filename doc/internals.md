# pal-csharp internals

How the translator is put together, and why. The companion documents are
[`translation.md`](translation.md) — the specification this code implements — and
[`surface_syntax.md`](surface_syntax.md) — what a user writes. This one is for people
changing the translator.

Read `translation.md` §0 first. It is short, and it constrains every decision below.

---

## 1. Pipeline

```
.cs ─► Load ─► Frontend ─► Normalize ─► Check ─► Emit ─► .fst
       Roslyn   attrs +     for→while    well-    Pulse
                spec        escapes      formed   codegen
                binding     liveness     ness
```

| Stage | Code | Job |
|---|---|---|
| Load | `Frontend/Loader.cs` | build a `CSharpCompilation`; refuse to proceed on any C# error |
| Frontend | `Frontend/FrontendPass.cs` + `SpecBinder`, `ExprLowerer`, `StmtLowerer` | walk the syntax with the semantic model, bind spec strings, build the IR |
| Normalize | `Passes/Normalize.cs` | C#→C# rewrites: `for`→`while`, measure inference, loop liveness |
| Check | `Passes/Check.cs` | whole-IR well-formedness; reports, never rewrites |
| Emit | `Emit/PulseEmitter.cs` + `MethodPlan`, `CodeEmitter`, `SpecEmitter` | one module per declaration |

Driven by `Pal.Tool/Program.cs`, which is also where the three output artefacts are
written: the modules, `diagnostics.json`, `source_range_info.json`, and the
`TranslationErrors.fst` sentinel.

The stage boundaries are not cosmetic. Normalize's output is still recognisably the source
program, which is what keeps it inside `translation.md` §0 rule 2; Check is a pure
predicate over the IR, which is what lets it run twice as PAL's does; and Emit sees exactly
what Normalize produced.

---

## 2. Refusing to guess

Two policies account for most of the design.

**Nothing translates if the C# does not compile.** `Loader` collects Roslyn's errors and
returns. Translating a program the C# compiler rejects would report the same mistakes a
second time, in worse terms.

**Nothing verifies if the translation was incomplete.** Every error also writes
`assert False` into `TranslationErrors.fst`, which is part of every test's module set. A
partial translation therefore fails F\* rather than passing quietly on the fragment that
happened to translate. This is PAL's device and it is worth keeping.

---

## 3. Binding specification strings

`Frontend/SpecBinder.cs` is the subtlest part of the front end, so it is worth describing
in full.

A C# attribute argument must be a compile-time constant, so `[Requires("0 <= n")]` carries
its predicate as a string. The string is *not* opaque. `SpecBinder`:

1. collects every spec string in the compilation, together with the member it annotates;
2. synthesises a **shim**: a source file in namespace `__PalSpecShims` containing, for each
   site, a method with the annotated member's signature whose body is
   `return <the string>;`, prefixed with `#line` directives pointing back into the original
   string literal;
3. adds the shim to the compilation and asks Roslyn to bind it;
4. maps every resulting `Diagnostic` back through the `#line` mapping, so an error is
   reported at its position *inside the string literal*;
5. hands the bound `ExpressionSyntax` and its `SemanticModel` to `ExprLowerer`.

Consequences to be aware of when changing it:

* **`Location.GetMappedLineSpan()`**, not `GetLineSpan()`, is what honours `#line`.
* **`SemanticModel`s are not portable across compilations**, so the shim's model may only
  be used on shim syntax, and the original model only on original syntax.
* **Never ask the semantic model about a synthesised node** that was not part of a
  compilation it knows.
* **The shim lives in `__PalSpecShims`**, so a spec string that names a sibling class by a
  qualified name would not bind unless the annotated member's own namespace is imported
  into the shim. `BuildUsings` does that.
* `Loader.ReferenceSet()` must not reference the translator's own assemblies: the
  namespace `Pal.*` would shadow `PalLang.Pal`, and every intrinsic would resolve to the
  wrong thing.

The alternative surface — contracts as leading `Pal.Requires(...)` statements — needs none
of this, and is why it exists. Both lower to the same IR node.

---

## 4. The IR

`Ir/Ir.cs`, about 300 lines. Every node carries an `IrLoc`, which is what makes both the
diagnostics and the provenance lint (R2.2) possible.

The IR is deliberately close to C#: `IrWhile`, `IrIf`, `IrBlock`, `IrAssign`,
`IrElement`, `IrCall`. There is no lower-level intermediate form, no basic-block graph, no
SSA. That is a direct consequence of `translation.md` §0 rule 2 — emitted Pulse must mirror
the C# it came from — and it means the emitter is a syntax-directed walk rather than a
compiler back end.

Nodes that are *not* one-to-one with C# earn their place individually:

| Node | Why it exists |
|---|---|
| `IrTypeBoundMeasure` | R5.9 case 2's inferred measure; a distinct node so the provenance lint can see it is emitter-generated |
| `IrWhile.Counted` | records that a `while` came from a counted `for`, which is what licenses that measure |
| `IrWhile.Unassigned` | R5.8b: locals the loop never writes, framed rather than existentially quantified |
| `IrWhile.Step` | R5.7 + R5.10: a `for` step must survive `continue` but not `break` |
| `IrInlinePulse` | raw Pulse, spliced after antiquotation expansion |

---

## 5. Normalize

`Passes/Normalize.cs`. Three C#→C# rewrites, each a rule over syntax applied uniformly:

* **`for` → `while`** (R5.7). The step is appended to the body — unless the body contains a
  `break` or `continue`, in which case it travels in `IrWhile.Step`, because C# runs the
  step after a `continue` but not after a `break`.
* **Measure inference** (R5.9 case 2), and *only* for a counted `for`. Everything else gets
  a diagnostic demanding `Pal.Decreases`. Guessing would be the emitter inventing a proof
  step.
* **Loop liveness** (R5.8, R5.8b): the free variables and the assigned variables of the
  loop, computed syntactically. Both must include `Step`, or a counter that lives in the
  step looks unassigned and the loop cannot be shown to terminate — which is exactly the
  bug the `break_continue` test caught.

---

## 6. Emit

Three cooperating emitters, split by what they produce rather than by what they consume.

### `MethodPlan` — the signature and the contract

Given an `IrMethod`, produces the binders, the ghost binders, the `requires` and `ensures`
resource lists, the `Slot` for each parameter, and two `SpecScope`s (pre- and post-state).
It is where R4.1's parameter treatment lives, where `[Frac]` weakens ownership (R4.9), and
where R4.8 wraps the postcondition as `PRE ==> POST`.

`Clause(resources, pure, existentials)` assembles a separation-logic clause and is shared
between contracts and loop invariants — the single most useful piece of factoring in the
emitter, because it makes the two agree by construction.

### `CodeEmitter` — executable code

A syntax-directed walk producing Pulse statements. Its recurring devices:

* **`Slot`** — how a C# name is represented right now: an immutable binder, a mutable `ref`
  cell, or a live array. Statements consult slots; specifications consult scopes.
* **`Capture`** — runs a sub-emission and collects the lines it produced plus its result
  term. This is what makes A-normalisation and short-circuit lowering (R6.3) compositional:
  a stateful sub-expression can be lifted wherever it needs to go.
* **`Escape`** — R5.10's break/continue flags for the innermost loop, saved and restored
  around nested loops.
* **`DerefScope`** — the scope in which a termination measure is emitted. An array denotes
  the *live array* here, not its contents, because F3 forbids a measure from mentioning the
  invariant's existentials. This is why `a.Length` has two readings (F7').

### `SpecEmitter` — propositions and pure terms

Emits a `Term`: text plus what it denotes (`Math`, `Machine`, `Bool`, `Prop`, `Seq`,
`Array`). The kind is what drives coercion — `I32.v` inserted exactly where a machine
integer is used mathematically, and nowhere else — and, as above, what selects between
`Seq.length` and `arr_length`. Getting a `TermKind` wrong is the most common way to produce
Pulse that is ill-typed rather than merely unprovable.

`Antiquotation.Expand` implements `$(…)` and friends, and runs on every raw-Pulse string
including those in specification position.

---

## 7. Output

One module per declaration, following PAL's conventions:

| Declaration | Module |
|---|---|
| method | `Func_<Type>_<Name>.fst` |
| `[Spec]` | `Let_<Type>_<Name>.fst` |
| `[Lemma]` | `Let_<Type>_<Name>.fst` |
| `[IncludePulse("M", …)]` | `M.fst` |
| — | `TranslationErrors.fst` |

Names are qualified by the declaring type (R2.1) *always*, not on collision, so adding an
unrelated class never renames an existing module.

Files are written only when their contents change, which keeps F\*'s checked-file cache
warm across runs — the single largest factor in test wall-clock time.

---

## 8. The Pulse support library

`pulse/Pulse.Lib.CSharp.*`, seeded from PAL's `Pulse.Lib.C.*`:

| Module | Contents |
|---|---|
| `Array` | `arr_length`, `read`, `write`, `alloc`, and the array-length modelling axiom |
| `Seq` | `FStar.Seq` / `FStar.Seq.Permutation` wrappers and the general lemmas about them |
| `Int32`, `Casts`, `Inhabited` | the machine-integer model and the `int`↔`SizeT` bridge |

This is the *other* place proof help may live (`translation.md` §0 rule 3). A lemma belongs
here if it is a general fact — about sequences, about arrays, about integers — usable by
any program. A lemma that mentions a particular example does not belong here or anywhere
else in the translator; it belongs in that example's `.cs` file.

---

## 9. Tests

```
test/
  <name>/Makefile               `include ../verify.mk`
  <name>/<Name>.cs              the annotated program
  <name>/<Name>Variant.cs       the same contract, written differently
  <name>/<name>.fst.config.json IDE configuration, generated
  verify.mk                     the shared harness
  diagnostics/                  negative tests: what must be *rejected*
  pulse_facts/                  regression pins for the facts in translation.md §1
                                (PulseFacts F1-F12, StructFacts F10-F12, ObjectFacts F13-F16)
  probe_insertion_sort/         scheme-adequacy probe for §2-§6, hand-derived
  objects_probe/                scheme-adequacy probe for §3.4/§4.5, hand-derived
  no-example-names.sh           no test-suite identifier may appear in Pal.Compiler
  provenance-lint.sh            every generated construct must trace to a C# span
  fst-configs.sh                writes (and `--check`s) the .fst.config.json files
```

`verify.mk` is two-phase, and the reason is worth recording: F\*'s dependency graph is not
known until `palcs` has run, so phase 1 translates and phase 2 re-enters `make` with
`PHASE=verify`, at which point `$(wildcard out/*.fst)` sees the generated files and
`.depend` can be included.

**`make -C test` runs the two lints as well as the proofs.** They are not optional extras:
`translation.md` §7.2 names variant tests and the provenance lint as the two mechanical
detectors of the failure mode this project is most at risk of — a translator quietly
reverse-engineered from its own test suite.

If a test's results look stale after a compiler change, `rm -rf out _cache` in its
directory.

### Checking generated modules interactively

The F\* IDE looks for a file whose name ends in `.fst.config.json`, searching from the
directory of the file being edited up to the workspace root and taking the **nearest**
one. A config in `test/swap/` therefore serves `test/swap/out/Func_Swapping_Swap.fst`
too, which is the whole reason one config per test directory is enough.

`test/fst-configs.sh` writes them, deriving each directory's include paths from what it
holds — `.` when there are hand-written `.fst` files, `out` when `palcs` generates
modules, always `_cache` and the support library — so there is no per-test special case.
`make -C test` runs it with `--check`: a config that has drifted from the build fails the
suite, because an IDE that disagrees with `make` about `--include` or `--already_cached`
produces errors that exist nowhere but the editor.

`test/diagnostics` is the one directory with a config *per case* rather than one for the
directory, and the reason is instructive: every rejected case emits a module named
`TranslationErrors`, so a single config listing all the case directories would make that
name ambiguous and F\* would silently resolve it to a different case's file. `run.sh`
writes one config into each case's output directory instead, and the nearest-config rule
does the rest.

### Adding a test

1. `mkdir test/<name> && echo 'include ../verify.mk' > test/<name>/Makefile`
2. write `<Name>.cs`, with a contract that says something — see `surface_syntax.md` and, for
   what counts as a strong specification, the sortedness *and* permutation postcondition of
   `test/insertion_sort_sorted`;
3. write `<Name>Variant.cs`: the same contract, genuinely differently written — loop form
   swapped, locals renamed and reordered, guard restructured, a helper extracted. It must
   verify with **no translator change**. If it does not, that is the signal §7.2 exists to
   produce;
4. `make -C test configs`, so the new directory gets its `.fst.config.json`.

### When a proof fails

In order of likelihood:

1. The loop body needs a fact from the enclosing `requires`. Restate it as an invariant.
2. The measure does not decrease on the path that ends the loop.
3. A `[Spec]` predicate used in an invariant carries a `[Requires]`, whose refinement
   cannot be discharged at invariant establishment. Make the predicate total.
4. Two `[Ensures]` are in the wrong order — one indexes an array the other bounds.
5. A recursive spec function needs unfolding inside a loop invariant; supply a `[Lemma]`.

None of those is fixed in the translator. That is the point.
