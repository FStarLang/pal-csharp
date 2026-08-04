// EXPECT: PALCS0549
// R9.15's conversion *moves* the invariant onto the base-typed reference, and a parameter's
// invariant is owed back to the caller by this method's own postcondition (R4.10). So
// `Shape s = q;` on a parameter is not a proof the translator is failing to find: it is a
// method whose specification cannot hold, whatever the emitter does. The refusal is written
// against the parameter, where the reader can act on it, rather than left to surface as an
// unprovable epilogue in Pulse the reader never wrote.
//
// The receiver is the same rule and the same message: `this` is a parameter too.
using PalLang;

public abstract class Shape
{
    [Refine("Result >= 0")]
    [Model]
    protected abstract SpecInt Area { get; }

    [Spec]
    public SpecInt TheArea => Area;

    [Frac("p")]
    [Requires("@this.TheArea <= 2147483647")]
    [Ensures("Result == @this.TheArea")]
    public abstract int GetArea();
}

[Invariant("side >= 0")]
[Invariant("side * side <= 2147483647")]
public sealed class Box : Shape
{
    private int side;

    [Model]
    protected override SpecInt Area => side * side;

    [Ensures("@this.TheArea == 0")]
    public Box()
    {
        side = 0;
    }

    public override int GetArea()
    {
        return side * side;
    }
}

public static class Client
{
    [Requires("s.TheArea <= 2147483647")]
    [Ensures("Result == s.TheArea")]
    public static int Measure(Shape s)
    {
        return s.GetArea();
    }

    [Requires("b.TheArea <= 2147483647")]
    [Ensures("Result == b.TheArea")]
    public static int ViaBase(Box b)
    {
        Shape s = b;
        return s.GetArea();
    }
}
