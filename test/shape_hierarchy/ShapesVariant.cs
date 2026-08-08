using PalLang;

namespace PalCSharp.Tests;

/// <summary>
/// §7.2's variant: the same client written differently — a <c>for</c> loop instead of a
/// <c>while</c>, the accumulation reassociated, the temporaries removed, the shape created
/// through a differently spelled conversion. It must verify with no emitter change.
/// </summary>
public static class ShapesVariant
{
    [Requires("first.TheArea + second.TheArea <= 2147483647")]
    [Ensures("Result == first.TheArea + second.TheArea")]
    public static int SumAreas(Shape first, Shape second)
    {
        return first.GetArea() + second.GetArea();
    }

    [Requires("4 * shape.TheArea <= 2147483647")]
    [Ensures("shape.TheArea == 4 * Old(shape.TheArea)")]
    public static void Grow(Shape shape)
    {
        shape.Double();
    }

    [Requires("count >= 0 && count <= 1000")]
    [Requires("shape.TheArea <= 100")]
    [Ensures("Result == count * shape.TheArea")]
    public static int RepeatArea(Shape shape, int count)
    {
        int acc = 0;
        for (int k = 0; k < count; k++)
        {
            Pal.Invariant(0 <= k && k <= count);
            Pal.Invariant(shape.TheArea <= 100);
            Pal.Invariant(acc == k * shape.TheArea);
            Pal.Decreases(count - k);
            acc = acc + shape.GetArea();
        }
        return acc;
    }

    [Ensures("Result == 27")]
    public static int MakeAndMeasure()
    {
        Shape s = new Circle(3);
        int a = s.GetArea();
        return a;
    }

    [Ensures("Result == 31")]
    public static int MakeAndSum()
    {
        Shape one = new Square(2);
        Shape two = new Circle(3);
        int total = SumAreas(two, one);
        return total;
    }

    /// <summary>§7.2's variant of <c>Shapes.SumFresh</c>: the conversions are at the other
    /// argument and at the other class, and one of them is a named local.</summary>
    [Ensures("Result == 31")]
    public static int SumFresh()
    {
        Circle c = new Circle(3);
        int total = SumAreas(c, new Square(2));
        return total;
    }

    /// <summary>§7.2's variant of <c>Shapes.MakeShape</c>: the conversion happens at the
    /// declaration and the <c>return</c> hands back a name, not a fresh object.</summary>
    [Ensures("Result.TheArea == 48")]
    public static Shape MakeShape()
    {
        Shape r = new Circle(4);
        return r;
    }

    [Ensures("Result * Result == 400")]
    public static int GrowAndMeasureSide()
    {
        Shape s = new Square(10);
        Square sq = (Square)s;
        int side = sq.GetSide();
        return 2 * side;
    }

    /// <summary>
    /// R9.15e, written differently: the conversions happen at the argument rather than
    /// through named base-typed locals, and one operand is a leaf whose forgetting is
    /// arithmetic while the other's is the identity.
    /// </summary>
    [Ensures("Result == 13")]
    public static int SumTiles()
    {
        Tile t = new Tile(4);
        return SumAreas(new Square(3), t);
    }

    /// <summary>R9.15e, with the mutation done through a directly created base local.</summary>
    [Ensures("Result == 24")]
    public static int GrowTile()
    {
        Shape s = new Tile(6);
        s.Double();
        int a = s.GetArea();
        return a;
    }

    /// <summary>
    /// R9.15e's bracket, written differently: the two calls are made on separate
    /// receivers, so each opens and closes its own view, and the observation is read
    /// before the mutation rather than after.
    /// </summary>
    [Ensures("Result == 21")]
    public static int DirectTile()
    {
        Tile t = new Tile(5);
        int before = t.GetArea();
        Tile u = new Tile(4);
        u.Double();
        return before + u.GetArea();
    }
}
