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

Early bootstrap. The toolchain and the translation scheme are in place; the translator
itself is not yet implemented.

- [x] Pinned F\*/Pulse toolchain (`make tools`)
- [x] Test harness and toolchain regression tests
- [x] [`doc/translation.md`](doc/translation.md) — the compositional translation scheme
- [ ] `Pal.Annotations` — the annotation surface
- [ ] `Pulse.Lib.CSharp.*` — the Pulse support library
- [ ] `Pal.Compiler` — the Roslyn-based translator

## Quick start

```bash
make tools        # install the pinned F*/Pulse toolchain into tools/fstar
make -C test      # verify the toolchain regression tests
```

The F\* version is pinned in [`tools/fstar-version.txt`](tools/fstar-version.txt) and used
by both local builds and CI, so the two cannot drift. The F\* binary release bundles Pulse,
so no separate Pulse install is needed.

## Documentation

| Document | Covers |
|----------|--------|
| [`doc/translation.md`](doc/translation.md) | The translation scheme, rule by rule — the specification of the emitter, and the anti-contortion discipline that keeps it compositional |

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
