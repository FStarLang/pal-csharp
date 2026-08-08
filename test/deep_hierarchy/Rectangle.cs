using PalLang;

namespace PalCSharp.Tests;

/// <summary>
/// A second leaf of the intermediate class, and the reason the intermediate class has to be
/// open-world (R9.18): <c>Quadrilateral</c> is compiled against no subclass in particular,
/// and both leaves fill the one vtable it declares.
/// </summary>
/// <remarks>
/// Its model has two numbers where <c>Square</c>'s has one, so the two forget to the same
/// <c>Box</c> by different functions and to the same <c>SpecInt</c> area by the same second
/// hop — which is what makes the hierarchy a refinement chain rather than three unrelated
/// classes that happen to share method names.
/// </remarks>
/// <remarks>
/// There is deliberately no invariant bounding the perimeter. <c>Double</c> quadruples the
/// area, and <c>Shape.Double</c>'s precondition says exactly that much is representable;
/// it says nothing about <c>2*(w+h)</c> after doubling, and no invariant a subclass writes
/// can make it. So the perimeter bound is where the C# already puts it — a precondition of
/// <c>Perimeter</c> — and that is the concrete form of the rule that a virtual method's
/// contract, written at the base model, must be discharged from the base model alone.
/// </remarks>
[Invariant("w >= 1")]
[Invariant("h >= 1")]
[Invariant("w * h <= 2147483647")]
public sealed class Rectangle : Quadrilateral
{
    private int w;
    private int h;

    [Refine("Result.Width >= 1")]
    [Refine("Result.Height >= 1")]
    [Model]
    private Box Dims => new Box { Width = w, Height = h };

    /// <summary>
    /// R9.6 at the first hop. Here it is the identity, which is worth having in the suite:
    /// a subclass may refine its parent's model by nothing at all and still be a subclass.
    /// </summary>
    protected override Box Bounds => Dims;

    [Requires("width >= 1")]
    [Requires("height >= 1")]
    [Requires("width * height <= 2147483647")]
    [Ensures("@this.TheWidth == width")]
    [Ensures("@this.TheHeight == height")]
    public Rectangle(int width, int height)
    {
        w = width;
        h = height;
    }

    public override int GetArea()
    {
        return w * h;
    }

    public override void Double()
    {
        w = 2 * w;
        h = 2 * h;
    }

    public override int Scaled(int k)
    {
        return k * (w * h);
    }

    public override int Weighted(int a, int b)
    {
        return a * h + b * w;
    }

    public override int DoubleAndReport()
    {
        int was = w * h;
        w = 2 * w;
        h = 2 * h;
        return was;
    }

    public override int Perimeter()
    {
        return 2 * (w + h);
    }
}
