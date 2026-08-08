using PalLang;

namespace PalCSharp.Tests;

/// <summary>
/// The root of a four-level chain. Two of the three forgetting functions below it are the
/// identity, which is what this directory is for: R9.15e and its abstract-class half are
/// about a subclass that adds no information to its base, and every other hierarchy test
/// here forgets by doing arithmetic.
/// </summary>
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

/// <summary>
/// The first intermediate class (R9.18). Its forgetting to <c>Shape</c> is arithmetic, so
/// the edge below it behaves as <c>test/deep_hierarchy</c>'s does.
/// </summary>
public abstract class Quad : Shape
{
    [Refine("Result >= 1")]
    [Model]
    protected abstract SpecInt Side { get; }

    protected override SpecInt Area => Side * Side;

    [Spec]
    public SpecInt TheSide => Side;

    [Frac("p")]
    [Requires("4 * @this.TheSide <= 2147483647")]
    [Ensures("Result == 4 * @this.TheSide")]
    public abstract int Perimeter();
}

/// <summary>
/// The second intermediate class, and the point of the directory.
///
/// <para>This pair — <c>Rect</c> and <c>Rect__impl</c> — is what an <em>open</em> concrete
/// class desugars to. The user would write one class:</para>
/// <code>
///     public class Rect : Quad {                       // no `sealed`
///         private int s;
///         public override int GetArea()   { return s * s; }
///         public override int Perimeter() { return 4 * s; }
///         public int Twice() { return GetArea() + GetArea(); }
///         public Rect(int n) { s = n; }
///     }
/// </code>
/// <para>and R9.2 refuses it, because a class that may be extended cannot own the
/// representation its subclasses will each have their own of. Splitting it in two — an
/// abstract class holding the model, the forgetting and the shared non-virtual bodies, and
/// a sealed leaf holding the fields and the virtual bodies — is a rewrite of the *source*
/// onto machinery §9 already has, and this directory is that rewrite written out by hand.
/// It is the shape a frontend rule would have to produce, verified before any rule
/// produces it (§0).</para>
///
/// <para>What makes it more than a restatement of <c>test/deep_hierarchy</c>: the split
/// puts <em>two</em> intermediate classes on the chain, and the two edges it introduces —
/// leaf to <c>Rect</c>, <c>Rect</c> to <c>Quad</c> — both forget by the identity, because
/// neither of them was a class boundary in the program the user wrote.</para>
/// </summary>
public abstract class Rect : Quad
{
    [Refine("Result >= 1")]
    [Model]
    protected abstract SpecInt Len { get; }

    /// <summary>R9.6, by the identity: this class knows exactly what a <c>Quad</c> knows.</summary>
    protected override SpecInt Side => Len;

    [Spec]
    public SpecInt TheLen => Len;

    /// <summary>
    /// The open class's non-virtual body. It touches no field — it is written in terms of
    /// virtual methods — so it stays on the abstract half and is shared by every subclass,
    /// present and future, which is what made it non-virtual in the first place.
    /// </summary>
    [Frac("p")]
    [Requires("2 * (@this.TheLen * @this.TheLen) <= 2147483647")]
    [Ensures("Result == 2 * (@this.TheLen * @this.TheLen)")]
    public int Twice()
    {
        int a = GetArea();
        int b = GetArea();
        return a + b;
    }
}

/// <summary>
/// The generated leaf: the open class's own fields and its own virtual bodies. A
/// <c>new Rect(n)</c> in the source becomes a <c>new Rect__impl(n)</c> here.
/// </summary>
[Invariant("s >= 1")]
public sealed class Rect__impl : Rect
{
    private int s;

    [Refine("Result >= 1")]
    [Model]
    private SpecInt L => s;

    /// <summary>R9.6, by the identity again — the leaf and the class it stands for are
    /// the same class in the source.</summary>
    protected override SpecInt Len => L;

    [Requires("n >= 1")]
    [Requires("n * n <= 2147483647")]
    [Ensures("@this.TheLen == n")]
    public Rect__impl(int n)
    {
        s = n;
    }

    public override int GetArea()
    {
        return s * s;
    }

    public override int Perimeter()
    {
        return 4 * s;
    }
}
