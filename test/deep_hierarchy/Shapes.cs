using PalLang;

namespace PalCSharp.Tests;

/// <summary>
/// A client of the three-level hierarchy (R9.18). Every method here is written at some
/// static type in the chain and calls what that type declares — which is the whole claim
/// depth makes: <c>Quadrilateral</c> is a real abstraction, not a staging post.
/// </summary>
public static class Shapes
{
    /// <summary>
    /// At the root, and unchanged from the two-level suite: dispatch reaches a
    /// <c>Square</c> through two vtables now, and nothing here says so.
    /// </summary>
    [Requires("a.TheArea + b.TheArea <= 2147483647")]
    [Ensures("Result == a.TheArea + b.TheArea")]
    public static int SumAreas(Shape a, Shape b)
    {
        int x = a.GetArea();
        int y = b.GetArea();
        return x + y;
    }

    /// <summary>A mutating dispatch at the root, over an object two levels below it.</summary>
    [Requires("4 * s.TheArea <= 2147483647")]
    [Ensures("s.TheArea == 4 * Old(s.TheArea)")]
    public static void Grow(Shape s)
    {
        s.Double();
    }

    /// <summary>
    /// At the <em>middle</em> of the chain. <c>Perimeter</c> is the intermediate class's
    /// own virtual method and <c>SemiPerimeter</c> is its non-virtual one, so this method
    /// is exactly what a class in the middle is for: it can say more than a <c>Shape</c>
    /// client and less than a <c>Square</c> one.
    /// </summary>
    [Requires("3 * (q.TheWidth + q.TheHeight) <= 2147483647")]
    [Ensures("Result == 3 * (q.TheWidth + q.TheHeight)")]
    public static int PerimeterAndHalf(Quadrilateral q)
    {
        int p = q.Perimeter();
        int h = q.SemiPerimeter();
        return p + h;
    }

    /// <summary>
    /// An <em>inherited</em> virtual called at the intermediate class: the slot is
    /// <c>Shape</c>'s, the model is <c>Quadrilateral</c>'s, and the caller sees the
    /// contract R9.6's forgetting function re-reads at the model it is holding.
    /// </summary>
    [Requires("q.TheWidth * q.TheHeight <= 2147483647")]
    [Ensures("Result == q.TheWidth * q.TheHeight")]
    public static int AreaOfQuad(Quadrilateral q)
    {
        return q.GetArea();
    }

    /// <summary>
    /// Dispatch under a loop, at the intermediate class. R5.12's re-quantification is
    /// indifferent to depth.
    /// </summary>
    [Requires("n >= 0 && n <= 1000")]
    [Requires("q.TheWidth + q.TheHeight <= 100")]
    [Ensures("Result == n * (2 * (q.TheWidth + q.TheHeight))")]
    public static int RepeatPerimeter(Quadrilateral q, int n)
    {
        int total = 0;
        int i = 0;
        while (i < n)
        {
            Pal.Invariant(0 <= i && i <= n);
            Pal.Invariant(q.TheWidth + q.TheHeight <= 100);
            Pal.Invariant(total == i * (2 * (q.TheWidth + q.TheHeight)));
            Pal.Decreases(n - i);
            total = total + q.Perimeter();
            i = i + 1;
        }
        return total;
    }

    /// <summary>
    /// R9.15 across the lower edge: a leaf converted to the class in the middle. From the
    /// next line on the square is a quadrilateral — two numbers, not one.
    /// </summary>
    [Ensures("Result == 20")]
    public static int MakeAndMeasure()
    {
        Quadrilateral q = new Square(5);
        return q.Perimeter();
    }

    /// <summary>
    /// R9.18 across the upper edge, and the point of the whole exercise: the conversion of
    /// an intermediate reference to the root's. C# writes two implicit conversions here,
    /// and so does the translation — one rule per edge, applied twice.
    /// </summary>
    [Ensures("Result == 25")]
    public static int UpTwoLevels()
    {
        Quadrilateral q = new Square(5);
        Shape s = q;
        return s.GetArea();
    }

    /// <summary>Two different leaves of the middle class, seen at the root.</summary>
    [Ensures("Result == 31")]
    public static int MixedLeaves()
    {
        Quadrilateral a = new Rectangle(3, 5);
        Quadrilateral b = new Square(4);
        Shape x = a;
        Shape y = b;
        return SumAreas(x, y);
    }

    /// <summary>
    /// R9.16 twice. The reference is grown at the root — a virtual call — and then cast
    /// back down through <em>both</em> levels to reach a <c>Square</c>-only member.
    ///
    /// <para>The postcondition is stated as a square rather than as <c>Result == 10</c>,
    /// and that is the meaning of the upcast, not a weakness of the proof: from the moment
    /// the reference is a <c>Shape</c>, the side is known only through the area. Each cast
    /// recovers a type and never the knowledge that was given up.</para>
    /// </summary>
    [Ensures("Result * Result == 100")]
    public static int GrowAndMeasureSide()
    {
        Quadrilateral q = new Square(5);
        Shape s = q;
        s.Double();
        Quadrilateral back = (Quadrilateral)s;
        Square sq = (Square)back;
        return sq.GetSide();
    }

    /// <summary>
    /// A downcast through both levels again, ending on an <em>inherited</em> virtual:
    /// <c>Perimeter</c> is declared by the class in the middle and dispatched here at a
    /// leaf's static type.
    ///
    /// <para>Stopping in the middle would not do. A <c>Quadrilateral</c> recovered from a
    /// <c>Shape</c> has some width and height whose product is the area, and that is all —
    /// forgetting is not injective, so a perimeter of 40 is no more provable than one of
    /// 202. Only the second cast, which recovers the model with one number in it, says
    /// which quadrilateral this is. The postcondition is squared for the same reason
    /// <c>GrowAndMeasureSide</c>'s is: the side is known through the area.</para>
    /// </summary>
    [Ensures("Result * Result == 1600")]
    public static int GrowAndMeasurePerimeter()
    {
        Quadrilateral q = new Square(5);
        Shape s = q;
        s.Double();
        Quadrilateral back = (Quadrilateral)s;
        Square sq = (Square)back;
        return sq.Perimeter();
    }
}
