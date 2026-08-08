using PalLang;

namespace PalCSharp.Tests;

/// <summary>
/// A leaf whose model <em>is</em> its base's (R9.15e). A tile is given directly by its
/// area, so the forgetting function (R9.6) is the identity and the two models are the same
/// bare <c>SpecInt</c>.
///
/// <para>That degenerate case is the one R9.15e exists for. Every class has its own
/// <c>__model</c> refinement type (R9.5), so <c>Tile</c>'s model and <c>Shape</c>'s are
/// distinct types even when the function between them is <c>fun m -> m</c>. A base
/// reference whose model was left as an application of <c>forget</c> is one whose model is
/// only known at <em>Tile</em>'s refinement, and the base's own observations cannot be
/// unfolded on it — so a client's precondition written at <c>Shape</c> becomes
/// unprovable. Where the forgetting does arithmetic, as <c>Square</c>'s and
/// <c>Circle</c>'s do, the result is at the base's type by construction and the question
/// never arises; here it is the whole content of the cast.</para>
/// </summary>
[Invariant("extent >= 0")]
public sealed class Tile : Shape
{
    private int extent;

    /// <summary>Tile's own model — which happens to be exactly what a Shape knows.</summary>
    [Refine("Result >= 0")]
    [Model]
    private SpecInt Extent => extent;

    /// <summary>The forgetting function (R9.6), here the identity.</summary>
    protected override SpecInt Area => Extent;

    /// <summary>An observation of Tile's own model.</summary>
    [Spec]
    public SpecInt TheExtent => Extent;

    [Requires("n >= 0")]
    [Ensures("@this.TheExtent == n")]
    public Tile(int n)
    {
        extent = n;
    }

    public override int GetArea()
    {
        return extent;
    }

    public override void Double()
    {
        extent = 4 * extent;
    }
}
