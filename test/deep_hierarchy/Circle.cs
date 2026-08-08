using PalLang;

namespace PalCSharp.Tests;

/// <summary>
/// A second leaf, so that the hierarchy has something to dispatch <em>between</em>. It
/// shares nothing with <c>Square</c> but the model its parent declares: a different
/// representation, a different refinement, a different forgetting function.
/// </summary>
[Invariant("radius >= 1")]
public sealed class Circle : Shape
{
    private int radius;

    [Refine("Result >= 1")]
    [Model]
    private SpecInt Radius => radius;

    /// <summary>
    /// R9.6. Areas are integers here, so this is a circle of the taxicab plane rather than
    /// the Euclidean one — which is beside the point. What matters is that a subclass may
    /// forget its model however it likes, and its parent's contract still holds of it.
    /// </summary>
    protected override SpecInt Area => 3 * Radius * Radius;

    [Requires("r >= 1")]
    [Requires("3 * r * r <= 2147483647")]
    [Ensures("@this.TheRadius == r")]
    public Circle(int r)
    {
        radius = r;
    }

    [Spec]
    public SpecInt TheRadius => Radius;

    public override int GetArea()
    {
        return 3 * radius * radius;
    }

    public override void Double()
    {
        radius = 2 * radius;
    }

    public override int Scaled(int k)
    {
        return k * (3 * radius * radius);
    }

    public override int DoubleAndReport()
    {
        int was = 3 * radius * radius;
        radius = 2 * radius;
        return was;
    }
}
