using PalLang;

namespace PalCSharp.Tests;

/// <summary>
/// A client of the hierarchy (§9). Nothing here mentions <c>Square</c> or <c>Circle</c>:
/// these methods are written against <c>Shape</c>, and every call to <c>GetArea</c> or
/// <c>Double</c> is dispatched (R9.12) through the receiver's vtable.
/// </summary>
public static class Shapes
{
    /// <summary>
    /// Two shapes, observed. Both calls are virtual, and neither method knows or cares
    /// which implementation answers.
    /// </summary>
    [Requires("a.TheArea + b.TheArea <= 2147483647")]
    [Ensures("Result == a.TheArea + b.TheArea")]
    public static int SumAreas(Shape a, Shape b)
    {
        int x = a.GetArea();
        int y = b.GetArea();
        return x + y;
    }

    /// <summary>
    /// A mutating dispatch. The precondition is the base class's, restated at the client's
    /// binders — which is the whole content of programming to an abstraction: the client
    /// discharges what <c>Shape.Double</c> demands and learns what it promises, with no
    /// access to how either is established.
    /// </summary>
    [Requires("4 * s.TheArea <= 2147483647")]
    [Ensures("s.TheArea == 4 * Old(s.TheArea)")]
    public static void Grow(Shape s)
    {
        s.Double();
    }

    /// <summary>
    /// Dispatch under a loop (R5.12). The invariant is written at the model, so the
    /// shape's implementation is as invisible inside the loop as outside it.
    /// </summary>
    [Requires("n >= 0 && n <= 1000")]
    [Requires("s.TheArea <= 100")]
    [Ensures("Result == n * s.TheArea")]
    public static int RepeatArea(Shape s, int n)
    {
        int total = 0;
        int i = 0;
        while (i < n)
        {
            Pal.Invariant(0 <= i && i <= n);
            // The loop re-quantifies the shape's model on every turn, so a bound the
            // precondition gave has to be carried round explicitly (R5.12) — exactly as it
            // would be for an `int`.
            Pal.Invariant(s.TheArea <= 100);
            Pal.Invariant(total == i * s.TheArea);
            Pal.Decreases(n - i);
            total = total + s.GetArea();
            i = i + 1;
        }
        return total;
    }

    /// <summary>
    /// R9.15. Creating a <c>Shape</c>. The C# is an ordinary implicit reference
    /// conversion; the translation is the leaf's view of its own invariant at the base's
    /// model, followed by the upcast — and from the next line on, nothing about a
    /// <c>Square</c> is visible.
    /// </summary>
    [Ensures("Result == 25")]
    public static int MakeAndMeasure()
    {
        Shape s = new Square(5);
        return s.GetArea();
    }
}
