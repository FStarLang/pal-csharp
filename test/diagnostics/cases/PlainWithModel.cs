// EXPECT: PALCS0574
// R12.1. `[Plain]` and `[Model]` are the two answers to the same question — what owning a
// reference to this class means — and a class may only give one of them. `[Model]` has the
// translator derive the predicate; `[Plain]` says the translator derives nothing and the
// user's own predicate says everything.
using PalLang;

[Spec]
public struct PlainCellModel
{
    public SpecInt V;
}

[Plain]
public sealed class PlainCell
{
    internal int v;

    [Model]
    private PlainCellModel Model => new PlainCellModel { V = v };
}
