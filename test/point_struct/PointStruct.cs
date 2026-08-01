using PalLang;

namespace PalCSharp.Tests;

/// <summary>An unrefined value struct: two independent coordinates.</summary>
public struct Point
{
    public int X;
    public int Y;
}

/// <summary>
/// A refined value struct. The refinement is written with the fields in scope as
/// simple names, exactly as it would read inside an instance method, and it holds of
/// every value of the type: producing an <c>Interval</c> proves it, consuming one may
/// assume it.
/// </summary>
[Refine("Lo <= Hi")]
public struct Interval
{
    public int Lo;
    public int Hi;
}

public static class Geometry
{
    [Requires("-1000 <= p.X && p.X <= 1000 && -1000 <= p.Y && p.Y <= 1000")]
    [Requires("-1000 <= dx && dx <= 1000")]
    [Ensures("Result.X == p.X + dx")]
    [Ensures("Result.Y == p.Y")]
    public static Point ShiftX(Point p, int dx)
    {
        Point q = p;
        q.X = p.X + dx;
        return q;
    }

    /// <summary>
    /// The struct is passed by reference, so the postcondition talks about the value
    /// the cell holds afterwards rather than about a returned value.
    /// </summary>
    [Requires("-1000 <= p.X && p.X <= 1000 && -1000 <= p.Y && p.Y <= 1000")]
    [Ensures("p.X == Old(p.Y) && p.Y == Old(p.X)")]
    public static void Transpose(ref Point p)
    {
        int t = p.X;
        p.X = p.Y;
        p.Y = t;
    }

    /// <summary>
    /// Widening an interval must re-establish <c>Lo &lt;= Hi</c>. The precondition is
    /// what discharges it; drop it and the proof fails, which is the whole point of
    /// writing the refinement on the type rather than on each method.
    /// </summary>
    [Requires("hi >= iv.Hi")]
    [Ensures("Result.Lo == iv.Lo && Result.Hi == hi")]
    public static Interval Widen(Interval iv, int hi)
    {
        Interval w = iv;
        w.Hi = hi;
        return w;
    }

    /// <summary>
    /// The refinement is available to a caller without being restated: it is what makes
    /// the result non-negative. It does not, however, bound the subtraction — two values
    /// a billion apart still satisfy <c>Lo &lt;= Hi</c> — so freedom from overflow is a
    /// separate obligation, and a separate precondition.
    /// </summary>
    [Requires("-1000 <= iv.Lo && iv.Hi <= 1000")]
    [Ensures("Result >= 0")]
    public static int Width(Interval iv)
    {
        return iv.Hi - iv.Lo;
    }

    /// <summary>
    /// Construction, with the unmentioned field taking its zero. `Origin` is `default`,
    /// so the emitted literal is total either way.
    /// </summary>
    [Requires("-1000 <= y && y <= 1000")]
    [Ensures("Result.X == 0 && Result.Y == y")]
    public static Point OnAxis(int y)
    {
        return new Point { Y = y };
    }

    [Ensures("Result.X == 0 && Result.Y == 0")]
    public static Point Origin()
    {
        return default(Point);
    }

    /// <summary>A struct is a value: assigning one copies it.</summary>
    [Requires("-1000 <= p.X && p.X <= 1000 && -1000 <= p.Y && p.Y <= 1000")]
    [Ensures("Result == p.X")]
    public static int CopiesAreIndependent(Point p)
    {
        Point q = p;
        q.X = 0;
        return p.X;
    }
}
