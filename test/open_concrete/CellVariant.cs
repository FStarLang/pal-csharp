using PalLang;

/// <summary>
/// §7.2's variant. An open concrete hierarchy written independently of
/// <c>Account</c>/<c>Premium</c>/<c>Gold</c> and differently from it: the root's model is
/// a plain field rather than one behind a <c>[Spec]</c> observation, the constructor takes
/// two arguments so <c>: base(…)</c> has more than one to bind, an argument is an
/// <em>expression</em> rather than a parameter (so R9.21c's renaming has something to
/// carry), the middle class adds a method of its own, and the leaf's constructor chains
/// through two levels at once.
///
/// <para>This file must verify with no change to the translator. If it needs one, R9.21
/// was fitted to <c>open_concrete</c>'s exact shape.</para>
/// </summary>
[Invariant("width >= 1")]
[Invariant("height >= 1")]
public class Cell
{
    protected int width;
    protected int height;

    [Refine("Result >= 1")]
    [Model]
    protected SpecInt Span => width * height;

    [Spec]
    public SpecInt TheSpan => Span;

    [Requires("w >= 1 && h >= 1")]
    [Requires("w * h <= 2147483647")]
    [Ensures("@this.TheSpan == w * h")]
    public Cell(int w, int h) { width = w; height = h; }

    [Frac("p")]
    [Requires("@this.TheSpan <= 2147483647")]
    [Ensures("Result == @this.TheSpan")]
    public int Area() { return width * height; }

    [Frac("p")]
    [Ensures("1 <= Result && Result <= 9")]
    public virtual int Weight() { return 1; }
}

/// <summary>A middle level that adds a method of its own as well as overriding one.</summary>
public class WideCell : Cell
{
    [Requires("h >= 1")]
    [Requires("4 * h <= 2147483647")]
    [Ensures("@this.TheSpan == 4 * h")]
    public WideCell(int h) : base(4, h) { }

    public override int Weight() { return 2; }

    [Frac("p")]
    [Requires("@this.TheSpan <= 1073741823")]
    [Ensures("Result == 2 * @this.TheSpan")]
    public int Twice() { return 2 * (width * height); }
}

/// <summary>The third level, chaining through the middle one.</summary>
public class TallCell : WideCell
{
    [Requires("k >= 0")]
    [Requires("4 * (k + 1) <= 2147483647")]
    [Ensures("@this.TheSpan == 4 * (k + 1)")]
    public TallCell(int k) : base(k + 1) { }

    public override int Weight() { return 3; }
}

public static class Cells
{
    [Ensures("Result == 12")]
    public static int Plain()
    {
        Cell c = new Cell(3, 4);
        return c.Area();
    }

    [Ensures("Result == 20")]
    public static int Wide()
    {
        Cell c = new WideCell(5);
        return c.Area();
    }

    [Ensures("Result == 24")]
    public static int Tall()
    {
        Cell c = new TallCell(5);
        return c.Area();
    }

    [Ensures("Result == 32")]
    public static int TallTwice()
    {
        WideCell c = new TallCell(3);
        return c.Twice();
    }

    /// <summary>
    /// Dispatch over all three levels through the root's slot, so each call learns only
    /// <c>Weight</c>'s abstract contract.
    /// </summary>
    [Ensures("3 <= Result && Result <= 27")]
    public static int Weights()
    {
        Cell a = new Cell(1, 1);
        Cell b = new WideCell(1);
        Cell c = new TallCell(0);
        return a.Weight() + b.Weight() + c.Weight();
    }
}
