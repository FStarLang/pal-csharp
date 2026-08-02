using PalLang;

namespace PalCSharp.Tests;

/// <summary>
/// The model of an interval: a spec-only struct (R3.9a), so a caller can talk about the
/// two endpoints separately. <c>[Refine]</c> here rather than on the class's <c>[Model]</c>
/// member because well-formedness is intrinsic to the type — every interval is ordered,
/// whoever produced it — which is the composition R3.9d describes.
/// </summary>
[Spec]
[Refine("Lo <= Hi")]
public struct Bounds
{
    public SpecInt Lo;
    public SpecInt Hi;
}

/// <summary>
/// Why a class invariant is a <c>pure</c> conjunct inside the predicate and not a
/// refinement on the representation (R3.10).
///
/// <c>Shift</c> writes <c>lo</c> and then <c>hi</c>. Between the two writes the object is
/// a perfectly good <c>class_Interval__raw</c> whose <c>lo &lt;= hi</c> is <em>false</em>.
/// A refinement type has to hold of every value of the type, so stating the invariant that
/// way would reject this method outright — and R3.6 writes a whole record per field
/// assignment, so there is no way to write both fields at once and dodge it. Stating it
/// inside the predicate instead means it has to hold only where the predicate is folded,
/// and R4.10's bracket is precisely the mark of where that is.
///
/// The intermediate state is visible in the generated Pulse: two `B.op_Colon_Equals` calls
/// with no `fold` between them.
/// </summary>
/// <remarks>
/// The second clause is R6.4 reaching into the invariant. <c>Size</c> computes
/// <c>hi - lo</c> at machine width, and <c>lo &lt;= hi</c> alone does not make that fit:
/// <c>lo = int.MinValue, hi = int.MaxValue</c> satisfies it and overflows. The bound is a
/// fact about the fields, so R3.9d puts it in <c>[Invariant]</c> — and it lands where it
/// belongs, on the class, rather than as a precondition every reader has to repeat.
/// </remarks>
[Invariant("lo <= hi")]
[Invariant("hi - lo <= 2147483647")]
public sealed class Interval
{
    private int lo;
    private int hi;

    [Model]
    private Bounds Model => new Bounds { Lo = lo, Hi = hi };

    [Spec]
    public SpecInt Low => Model.Lo;

    [Spec]
    public SpecInt High => Model.Hi;

    [Spec]
    public SpecInt Width => Model.Hi - Model.Lo;

    [Requires("lo <= hi")]
    [Requires("hi - lo <= 2147483647")]
    [Ensures("@this.Low == lo")]
    [Ensures("@this.High == hi")]
    public Interval(int lo, int hi)
    {
        this.lo = lo;
        this.hi = hi;
    }

    /// <summary>
    /// The invariant is false after the first assignment whenever <c>d</c> is positive and
    /// the interval is degenerate: <c>lo + d &gt; hi</c>. It is restored by the second.
    /// </summary>
    [Requires("-2147483648 - @this.Low <= d && @this.High + d <= 2147483647")]
    [Requires("-2147483648 <= @this.Low + d")]
    [Ensures("@this.Low == Old(@this.Low) + d")]
    [Ensures("@this.High == Old(@this.High) + d")]
    [Ensures("@this.Width == Old(@this.Width)")]
    public void Shift(int d)
    {
        lo = lo + d;
        hi = hi + d;
    }

    [Ensures("Result == @this.Width")]
    public int Size()
    {
        return hi - lo;
    }
}

public static class Intervals
{
    /// <summary>
    /// A client's view. It never unfolds the invariant, so <c>Lo &lt;= Hi</c> reaches it
    /// only because <c>Bounds</c> carries the fact in its <em>type</em> (F17) — move the
    /// refinement into <c>[Invariant]</c> and this stops verifying while everything else
    /// keeps working, which is the precise statement that the fact was unreachable.
    /// </summary>
    [Ensures("Result >= 0")]
    public static int NonNegativeWidth(Interval i)
    {
        return i.Size();
    }
}
