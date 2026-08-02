using PalLang;

namespace PalCSharp.Tests;

[Spec]
public struct CellModel
{
    public SpecInt V;
}

/// <summary>
/// The bottom of a three-level hierarchy. Like every leaf it knows nothing about being
/// owned, and — per F17 — the bound a two-levels-removed owner will need is a
/// <c>[Refine]</c> on the model, not a <c>pure</c> conjunct of the invariant, because a
/// conjunct sits behind a folded slprop and never reaches the owner at all.
/// </summary>
[Invariant("0 <= v")]
public sealed class Cell
{
    private int v;

    [Refine("0 <= Result.V && Result.V <= 2147483647")]
    [Model]
    private CellModel Model => new CellModel { V = v };

    [Spec]
    public SpecInt V => Model.V;

    [Spec]
    public CellModel State => Model;

    [Requires("0 <= start")]
    [Ensures("@this.V == start")]
    public Cell(int start)
    {
        v = start;
    }

    [Requires("@this.V < 2147483647")]
    [Ensures("@this.V == Old(@this.V) + 1")]
    public void Bump()
    {
        v = v + 1;
    }

    [Ensures("Result == @this.V")]
    public int Value()
    {
        return v;
    }
}
