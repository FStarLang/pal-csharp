using PalLang;

namespace PalCSharp.Tests;

/// <summary>
/// A leaf of the <em>intermediate</em> class. It forgets through two levels: its own model
/// has one number, the quadrilateral model has two, the shape model has one again. Only
/// the first hop is written here — the second is <c>Quadrilateral</c>'s own <c>override</c>.
/// </summary>
[Invariant("side >= 1")]
[Invariant("side * side <= 2147483647")]
public sealed class Square : Quadrilateral
{
    private int side;

    [Refine("Result >= 1")]
    [Model]
    private SpecInt Side => side;

    /// <summary>R9.6: the forgetting function, to the <em>immediate</em> base's model.</summary>
    protected override Box Bounds => new Box { Width = Side, Height = Side };

    [Requires("n >= 1")]
    [Requires("n * n <= 2147483647")]
    [Ensures("@this.SideLength == n")]
    public Square(int n)
    {
        side = n;
    }

    [Spec]
    public SpecInt SideLength => Side;

    public override int GetArea()
    {
        return side * side;
    }

    public override void Double()
    {
        side = 2 * side;
    }

    public override int Scaled(int k)
    {
        return k * (side * side);
    }

    public override int Weighted(int a, int b)
    {
        return a * side + b * side;
    }

    public override int DoubleAndReport()
    {
        int was = side * side;
        side = 2 * side;
        return was;
    }

    public override int Perimeter()
    {
        return 4 * side;
    }

    /// <summary>A <c>Square</c>-only member: what a downcast through two levels is for.</summary>
    [Ensures("Result == @this.SideLength")]
    public int GetSide()
    {
        return side;
    }
}
