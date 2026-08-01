# pal-csharp

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

Milestone 1. The translator works end to end: annotated C# in, verified Pulse out.

- [x] Pinned F\*/Pulse toolchain (`make tools`)
- [x] Test harness, negative tests, and the two anti-contortion lints
- [x] [`doc/translation.md`](doc/translation.md) — the compositional translation scheme
- [x] `Pal.Annotations` — the annotation surface
- [x] `Pulse.Lib.CSharp.*` — the Pulse support library
- [x] `Pal.Compiler` / `palcs` — the Roslyn-based translator
- [x] Scalars, `ref`/`out`/`in`, arrays, loops, `break`/`continue`, fractional
      permissions, `[Spec]` functions, `[Lemma]` calls, `Ghost<T>` arguments, raw-Pulse
      interop
- [x] **Insertion sort proved sorted *and* a permutation of its input**
- [ ] `struct` support (`point_struct`, `circular_buffer`) — see
      [`doc/translation.md`](doc/translation.md) §8
- [ ] `Pal.Analyzers` — in-IDE squiggles on specifications

## Quick start

```bash
make tools        # install the pinned F*/Pulse toolchain into tools/fstar
make              # build the translator
make -C test      # translate and verify every test, then run the lints
```

To translate and verify one program:

```bash
palcs -o out MyProgram.cs        # C# ─► Pulse
```

The F\* version is pinned in [`tools/fstar-version.txt`](tools/fstar-version.txt) and used
by both local builds and CI, so the two cannot drift. The F\* binary release bundles Pulse,
so no separate Pulse install is needed.

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
