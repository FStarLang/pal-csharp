# pal-csharp

[![CI](https://github.com/FStarLang/pal-csharp/actions/workflows/ci.yml/badge.svg)](https://github.com/FStarLang/pal-csharp/actions/workflows/ci.yml)

### Proof Annotation Language for C#

Write ordinary C#, annotate it with separation-logic specifications, and have those
specifications translated to [Pulse](https://github.com/FStarLang/FStar/tree/master/pulse)
— an F\*-based separation-logic verification language — where the proofs are discharged by
the type checker.

`pal-csharp` is the C# analogue of [PAL](https://github.com/FStarLang/pal), which does the
same for C.

```csharp
[Ensures("y == Old(x) && x == Old(y)")]
public static void Swap(ref int x, ref int y)
{
    int tmp = y; y = x; x = tmp;
}
```

**Annotated C# always compiles and runs as ordinary C#, at zero runtime cost.** Attributes
are inert metadata, and the `Pal.*` proof intrinsics are `[Conditional("PAL")]`, so their
call sites — arguments included — are erased from a normal build. No preprocessor, no
source rewriting.

## Status

**Milestone 1 is complete.** The translator works end to end — annotated C# in, verified
Pulse out — and the whole M1 acceptance suite passes.

- [x] Pinned F\*/Pulse toolchain (`make tools`)
- [x] Test harness, negative tests, and the two anti-contortion lints
- [x] [`doc/translation.md`](doc/translation.md) — the compositional translation scheme
- [x] `Pal.Annotations` — the annotation surface
- [x] `Pulse.Lib.CSharp.*` — the Pulse support library
- [x] `Pal.Compiler` / `palcs` — the Roslyn-based translator
- [x] Scalars, `ref`/`out`/`in`, arrays, loops, `break`/`continue`, fractional
      permissions, `[Spec]` functions, `[Lemma]` calls, `Ghost<T>` arguments, raw-Pulse
      interop
- [x] `struct`s with `[Refine]` type refinements
- [x] **Insertion sort proved sorted *and* a permutation of its input**
- [x] Classes and objects — abstract invariants over a pure model, a class owning its
      array, and a class owning other objects three levels deep
- [x] Thirty-eight acceptance directories verify, each with an independently written variant
      that must verify with no translator change
- [x] **A production checksum verified as it ships** — SharpZipLib's `Adler32`
      ([`examples/adler32`](examples/adler32)), proved free of overflow *and* equal to
      RFC 1950 §8.2, which turned up an arithmetic error in its own safety comment
- [x] `Pal.Analyzers` — in-IDE squiggles, running the translator's own passes so the
      editor and `palcs` cannot disagree
- [x] **Unconstrained generics** — a generic method over `T[]` verifies, calls another
      generic method, and is instantiated at a concrete type, with no monomorphising pass
      ([`doc/translation.md`](doc/translation.md) §14)
- [x] **Generic classes** — `Cell<T>` and `TreeNode<T>` with parameterised invariants, and
      a full library over each proved against `Pulse.Lib.CSharp.List` /
      `Pulse.Lib.CSharp.Tree` ([`test/generic_list`](test/generic_list),
      [`test/generic_tree`](test/generic_tree),
      [`doc/translation.md`](doc/translation.md) §15)
- [x] **Bring your own ownership predicate** — a `[Plain]` class about which the translator
      derives nothing, its separation-logic predicate written in an ordinary `.fst` file
      beside the C# and pulled in with `[assembly: IncludePulseFile]`, and every proof step
      in a body an ordinary typed C# call to a `[Lemma]` the predicate publishes. Reaches a
      doubly linked list — including a `PushFront` that *writes the old head's back pointer*
      ([`test/dll_segment`](test/dll_segment),
      [`doc/translation.md`](doc/translation.md) §12)
- [x] **Cursors — iterative traversal of a linked structure**, which §10.7 had refused as
      needing "a magic wand". It does not: the part a loop has walked is a *function of the
      loop counter*, so the invariant can name it with `Take`/`Drop` (a list) or a one-hole
      context (a tree) and close it at the end with an ordinary lemma. An iterative BST
      lookup is proved to return the value the map holds
      ([`test/list_cursor`](test/list_cursor), [`test/tree_cursor`](test/tree_cursor),
      [`doc/translation.md`](doc/translation.md) §16)
- [x] **`null` is a pointer, not a wrapper.** A Pulse `box` is already nullable, so `C?` is
      that box and `C` is its non-null refinement — one type and a refinement, exactly as C#
      has one runtime type and an annotation. Passing a `C` where a `C?` is wanted is the
      identity; `x!` is a refinement the surrounding `if` already proves. Every recursive
      invariant loses an existential, and every hand-written cursor lemma takes its cursor
      once instead of twice ([`doc/translation.md`](doc/translation.md) R10.2,
      [`test/pulse_facts/NullFacts.fst`](test/pulse_facts/NullFacts.fst))
- [ ] `Span<T>`, interfaces, constrained generics, `IEnumerable<T>` iterators — see
      [`doc/translation.md`](doc/translation.md) §8, §15.5 and §16.5

## Quick start

```bash
make tools        # install the pinned F*/Pulse toolchain into tools/fstar
make              # build the translator
make test         # the regression gate: every test and every example, then the lints
```

`make test` is the gate. It covers two trees. `test/` holds programs written to exercise a
numbered rule of [`doc/translation.md`](doc/translation.md). `examples/` holds code that was
written for some other purpose and then verified — real code, ported with its adaptations
documented and its upstream licence carried beside it. Both run through the same harness,
carry the same two obligations, and are held to the same lints; only their provenance
differs. `make -C examples` runs the examples alone.

To translate and verify one program:

```bash
palcs -o out MyProgram.cs        # C# ─► Pulse
```

The F\* version is pinned in [`tools/fstar-version.txt`](tools/fstar-version.txt) and used
by both local builds and CI, so the two cannot drift. The F\* binary release bundles Pulse,
so no separate Pulse install is needed.

### Reading the generated Pulse interactively

Every directory that holds or produces F\* carries an `.fst.config.json`, so opening a
generated `out/*.fst` in an editor with the
[F\* VS Code assistant](https://marketplace.visualstudio.com/items?itemName=FStarLang.fstar-vscode-assistant)
(or `fstar-mode.el`) checks it with exactly the flags `make` uses — hover for types,
`Ctrl+.` to check to a point, jump to definitions in `Pulse.Lib.CSharp.*`. Open the
repository root as the workspace; the editor takes the config nearest the file.

The configs are generated by [`test/fst-configs.sh`](test/fst-configs.sh) from what each
directory actually contains, and `make -C test` fails if any is stale, so an editor and a
build can never disagree about include paths.

### Seeing pal-csharp's own diagnostics as you type

Install the [C# extension](https://marketplace.visualstudio.com/items?itemName=ms-dotnettools.csharp),
open the repository root, and run `make` once so the analyzer exists to be loaded. The
workspace is already configured to load [`Pal.Tests.sln`](Pal.Tests.sln), which is the
product plus one project per test directory, each of which loads `Pal.Analyzers`. From
then on every `PALCS` diagnostic appears in the editor as you type — including the ones
whose span is *inside* a specification string — in the same words and at the same place
`palcs` would put them, because the analyzer runs the translator's own passes rather than
restating its rules.

`test/diagnostics/cases` will be solidly red, and that is the point: every file in it is a
program pal-csharp is meant to refuse, and its `// EXPECT:` header names the refusal.

**Failed proofs show up there too.** An analyzer cannot run a prover — it has to answer
between keystrokes — but it can read the last answer. `make` pipes F\*'s output through
`palcs report`, which maps each message back to the C# line that produced the Pulse it is
about and writes `out/verification.txt`; the projects list that file as an `AdditionalFile`,
which Roslyn tracks for changes. So run `make`, and what Pulse could not prove appears as
`PALCS0600` on the statement or the contract clause responsible, in F\*'s own words. Nothing
rewrites the prover's explanation — only its location changes.

The projects and the solution are generated by
[`test/cs-projects.sh`](test/cs-projects.sh); `Pal.slnx` stays the product-only solution
that `make` and CI build. As with the F\* configs, `make -C test` fails if any is stale.
After adding or removing a test directory:

```bash
make -C test configs
```

The gate builds these projects too, via [`test/ide-build.sh`](test/ide-build.sh), and
requires them to build clean. The acceptance harness compiles each directory with a
synthesised *stock* project — deliberately without the analyzer, since its obligation is
that annotated C# is ordinary C# — which leaves the converse unchecked: that the analyzer
says *nothing* about a program pal-csharp accepts. A spurious diagnostic is invisible to a
proof and is the first thing a contributor sees, so it is gated. The diagnostics cases are
excluded, for the reason they are red above.

### Continuous integration

[`.github/workflows/ci.yml`](.github/workflows/ci.yml) runs `make test` — the same gate,
not a reimplementation of it, so CI and a working copy cannot disagree about what passing
means. The pinned toolchain is cached on `tools/fstar-version.txt` and CI asserts that the
F\* it ended up with is the one the pin names, so neither a stale cache nor a silent
upgrade can go unnoticed. The analyzer check runs again as its own job, where it needs no
F\* and so reports a regression in minutes rather than after a verification run.

## Documentation

| Document | Covers |
|----------|--------|
| [`doc/surface_syntax.md`](doc/surface_syntax.md) | What you write: contracts, loops, ownership, `[Spec]`, `[Lemma]`, `Ghost<T>`, raw Pulse — start here |
| [`doc/translation.md`](doc/translation.md) | The translation scheme, rule by rule — the specification of the emitter, and the anti-contortion discipline that keeps it compositional |
| [`doc/internals.md`](doc/internals.md) | How the translator is built: the pipeline, spec-string binding, the IR, the emitters, the test harness |

## Design in one paragraph

The translator is a standalone .NET tool: a [Roslyn](https://github.com/dotnet/roslyn)
front end, its own IR, and its own Pulse emitter. Declaration-level contracts are carried
by attributes whose string payloads are parsed and **bound by Roslyn in the method's
scope**, so specifications are genuinely type-checked; statement-level constructs that
attributes cannot reach — loop invariants, asserts, ghost statements — are
`[Conditional]` `Pal.*` calls taking real C# expressions. Ownership is read off the C# type
system (`ref`, `out`, `in`, `Span<T>`, `T[]`), lemmas are ordinary C# method calls that
vanish at runtime, and pure specification functions are ordinary expression-bodied methods.

## License

[Apache 2.0](LICENSE)
