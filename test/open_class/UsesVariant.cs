using PalLang;

namespace PalCSharp.Tests;

/// <summary>
/// §7.2's variant: the same clients written differently — the conversions happening at an
/// argument rather than through a named base-typed local, an intermediate binding where
/// there was none, the virtual calls reached at a different static type. It must verify
/// with no emitter change.
/// </summary>
public static class UsesVariant
{
    [Ensures("Result == 50")]
    public static int AtLeaf()
    {
        Rect__impl leaf = new Rect__impl(5);
        Rect r = leaf;
        int t = r.Twice();
        return t;
    }

    [Ensures("Result == 49")]
    public static int UpToRoot()
    {
        return Uses.AtRoot(new Rect__impl(7));
    }

    [Ensures("Result == 24")]
    public static int UpToMiddle()
    {
        Rect__impl leaf = new Rect__impl(6);
        Quad q = leaf;
        return Uses.AtMiddle(q);
    }

    /// <summary>
    /// The whole chain walked in one conversion rather than in pieces: the leaf is created
    /// and handed straight to a root-typed parameter, so all three edges are crossed by a
    /// single <c>IrConvert</c>.
    /// </summary>
    [Ensures("Result == 36")]
    public static int StraightToRoot()
    {
        Shape s = new Rect__impl(6);
        int a = s.GetArea();
        return a;
    }
}
