using PalLang;

namespace PalCSharp.Tests;

/// <summary>
/// Clients of the four-level chain, at each of its static types.
/// </summary>
public static class Uses
{
    /// <summary>
    /// At the deepest static type the source has a name for, calling the shared
    /// non-virtual body. Two virtual calls inside it dispatch to the generated leaf.
    /// </summary>
    [Ensures("Result == 50")]
    public static int AtLeaf()
    {
        Rect r = new Rect__impl(5);
        return r.Twice();
    }

    /// <summary>Dispatch at the root.</summary>
    [Frac("p")]
    [Requires("s.TheArea <= 2147483647")]
    [Ensures("Result == s.TheArea")]
    public static int AtRoot(Shape s)
    {
        return s.GetArea();
    }

    /// <summary>Dispatch at the first intermediate class.</summary>
    [Frac("p")]
    [Requires("4 * q.TheSide <= 2147483647")]
    [Ensures("Result == 4 * q.TheSide")]
    public static int AtMiddle(Quad q)
    {
        return q.Perimeter();
    }

    /// <summary>
    /// R9.15e, both halves. The value is created three levels down and handed to a method
    /// whose precondition is written at the root, so the conversion crosses two edges that
    /// forget by the identity — one out of a sealed class, one out of an abstract one.
    /// Without the rule the model arrives at the leaf's own refinement and
    /// <c>AtRoot</c>'s precondition, a statement purely about a <c>Shape</c>, cannot be
    /// discharged.
    /// </summary>
    [Ensures("Result == 49")]
    public static int UpToRoot()
    {
        Rect r = new Rect__impl(7);
        return AtRoot(r);
    }

    /// <summary>R9.15e, stopping at the intermediate class.</summary>
    [Ensures("Result == 24")]
    public static int UpToMiddle()
    {
        Rect r = new Rect__impl(6);
        return AtMiddle(r);
    }
}
