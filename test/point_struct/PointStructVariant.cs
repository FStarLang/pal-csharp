using PalLang;
using static PalLang.Pal;

namespace PalCSharp.Tests.Variant;

/// <summary>
/// The same contracts as <c>PointStruct.cs</c>, written differently: auto-properties
/// instead of fields, the refinement written on a field rather than on the type, the
/// contracts written as leading body statements rather than as attributes, fields
/// declared in the opposite order, and construction by object initializer where the
/// original used <c>default</c>. Nothing here may require a translator change.
/// </summary>
public struct Coord
{
    public int Y { get; set; }
    public int X { get; set; }
}

public struct Span2
{
    public int Hi;

    [Refine("Lo <= Hi")]
    public int Lo;
}

public static class GeometryVariant
{
    public static Coord ShiftX(Coord p, int dx)
    {
        Requires(-1000 <= p.X && p.X <= 1000 && -1000 <= p.Y && p.Y <= 1000);
        Requires(-1000 <= dx && dx <= 1000);
        Ensures(Result<Coord>().X == Old(p.X) + Old(dx));
        Ensures(Result<Coord>().Y == Old(p.Y));

        return new Coord { X = p.X + dx, Y = p.Y };
    }

    [Requires("-1000 <= p.X && p.X <= 1000 && -1000 <= p.Y && p.Y <= 1000")]
    [Ensures("p.X == Old(p.Y)")]
    [Ensures("p.Y == Old(p.X)")]
    public static void Transpose(ref Point p)
    {
        Point original = p;
        p.X = original.Y;
        p.Y = original.X;
    }

    [Requires("hi >= iv.Hi")]
    [Ensures("Result.Lo == iv.Lo")]
    [Ensures("Result.Hi == hi")]
    public static Span2 Widen(Span2 iv, int hi)
    {
        return new Span2 { Lo = iv.Lo, Hi = hi };
    }

    [Requires("-1000 <= iv.Lo")]
    [Requires("iv.Hi <= 1000")]
    [Ensures("Result >= 0")]
    public static int Width(Span2 iv)
    {
        int hi = iv.Hi;
        int lo = iv.Lo;
        return hi - lo;
    }

    [Requires("-1000 <= y && y <= 1000")]
    [Ensures("Result.X == 0")]
    [Ensures("Result.Y == y")]
    public static Coord OnAxis(int y)
    {
        Coord c = default;
        c.Y = y;
        return c;
    }

    [Ensures("Result.X == 0 && Result.Y == 0")]
    public static Coord Origin()
    {
        return new Coord { X = 0, Y = 0 };
    }

    [Requires("-1000 <= p.X && p.X <= 1000 && -1000 <= p.Y && p.Y <= 1000")]
    [Ensures("Result == p.X")]
    public static int CopiesAreIndependent(Coord p)
    {
        Coord q = p;
        q.X = 0;
        q.Y = 0;
        return p.X;
    }
}
