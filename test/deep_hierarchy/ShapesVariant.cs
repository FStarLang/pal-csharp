using PalLang;

namespace PalCSharp.Tests;

/// <summary>
/// §7.2's variant for the three-level hierarchy: the same programs written differently —
/// a <c>for</c> loop instead of a <c>while</c>, conversions at argument and return
/// position instead of at a local declaration, temporaries removed or added, parameters
/// renamed and reordered. It must verify with no emitter change.
/// </summary>
public static class ShapesVariant
{
    [Requires("3 * (quad.TheWidth + quad.TheHeight) <= 2147483647")]
    [Ensures("Result == 3 * (quad.TheWidth + quad.TheHeight)")]
    public static int PerimeterAndHalf(Quadrilateral quad)
    {
        return quad.Perimeter() + quad.SemiPerimeter();
    }

    [Requires("quad.TheWidth * quad.TheHeight <= 2147483647")]
    [Ensures("Result == quad.TheWidth * quad.TheHeight")]
    public static int AreaOfQuad(Quadrilateral quad)
    {
        int a = quad.GetArea();
        return a;
    }

    /// <summary>The loop as a <c>for</c>, accumulating in the other order.</summary>
    [Requires("count >= 0 && count <= 1000")]
    [Requires("quad.TheWidth + quad.TheHeight <= 100")]
    [Ensures("Result == count * (2 * (quad.TheWidth + quad.TheHeight))")]
    public static int RepeatPerimeter(Quadrilateral quad, int count)
    {
        int acc = 0;
        for (int k = 0; k < count; k++)
        {
            Pal.Invariant(0 <= k && k <= count);
            Pal.Invariant(quad.TheWidth + quad.TheHeight <= 100);
            Pal.Invariant(acc == k * (2 * (quad.TheWidth + quad.TheHeight)));
            Pal.Decreases(count - k);
            acc = quad.Perimeter() + acc;
        }
        return acc;
    }

    /// <summary>The lower conversion written at the receiver of the call, not at a local.</summary>
    [Ensures("Result == 20")]
    public static int MakeAndMeasure()
    {
        return ((Quadrilateral)new Square(5)).Perimeter();
    }

    /// <summary>Both conversions at an argument, so neither is written as a declaration.</summary>
    [Ensures("Result == 25")]
    public static int UpTwoLevels()
    {
        return Measure(new Square(5));
    }

    [Requires("shape.TheArea <= 2147483647")]
    [Ensures("Result == shape.TheArea")]
    private static int Measure(Shape shape)
    {
        return shape.GetArea();
    }

    /// <summary>The leaves the other way round, and the sum taken by this class's own helper.</summary>
    [Ensures("Result == 31")]
    public static int MixedLeaves()
    {
        Quadrilateral small = new Square(4);
        Quadrilateral wide = new Rectangle(3, 5);
        return Shapes.SumAreas(wide, small);
    }

    /// <summary>
    /// The conversion up written in one step across both levels, and the way back down in
    /// one step too — R9.16 needs a local to bind the model equation to, and one is enough.
    ///
    /// <para>The growth stays a call on <c>s</c> rather than a call to <c>Shapes.Grow(s)</c>,
    /// and that is not a stylistic choice: handing the reference to a <c>Shape</c>-typed
    /// parameter drops what it is known to stand for (R9.16), and nothing gets it back. A
    /// variant that passed it would be a different program, not the same one written
    /// differently.</para>
    /// </summary>
    [Ensures("Result * Result == 100")]
    public static int GrowAndMeasureSide()
    {
        Shape s = new Square(5);
        s.Double();
        Square sq = (Square)s;
        return sq.GetSide();
    }

    [Ensures("Result * Result == 1600")]
    public static int GrowAndMeasurePerimeter()
    {
        Shape s = new Square(5);
        s.Double();
        Square sq = (Square)s;
        int p = sq.Perimeter();
        return p;
    }

    /// <summary>The §7.2 variant of <c>ReportThenGrow</c>: the receiver is a
    /// <c>Rectangle</c> reached at the root type, the result goes through a local, and the
    /// growth is observed afterwards rather than being taken on trust.</summary>
    [Ensures("Result == 6")]
    public static int ReportThenGrow()
    {
        Rectangle r = new Rectangle(2, 3);
        Shape s = r;
        int was = s.DoubleAndReport();
        return was;
    }

    [Ensures("Result == 24")]
    public static int ReportThenMeasure()
    {
        Shape s = new Rectangle(2, 3);
        int was = s.DoubleAndReport();
        int now = s.GetArea();
        return now;
    }

    /// <summary>The §7.2 variants: a different leaf, arguments that are not equal to each
    /// other, and the result taken through a local.</summary>
    [Ensures("Result == 24")]
    public static int ScaleAtRoot()
    {
        Circle c = new Circle(2);
        Shape s = c;
        int r = s.Scaled(2);
        return r;
    }

    [Ensures("Result == 45")]
    public static int WeighAtMiddle()
    {
        Square sq = new Square(5);
        Quadrilateral q = sq;
        int r = q.Weighted(4, 5);
        return r;
    }

    /// <summary>R9.18f, at an explicit receiver rather than through an intermediate local.</summary>
    [Frac("p")]
    [Requires("shape.TheWidth * shape.TheHeight <= 2147483647")]
    [Ensures("Result == shape.TheWidth * shape.TheHeight")]
    public static int AreaAtMiddle(Quadrilateral shape)
    {
        int r = shape.GetArea();
        return r;
    }

    /// <summary>R9.18f, reaching the intermediate class's own inherited-method body.</summary>
    [Ensures("Result == 32")]
    public static int TwiceAreaOfSquare()
    {
        Square sq = new Square(4);
        Quadrilateral q = sq;
        return q.TwiceArea();
    }
}
