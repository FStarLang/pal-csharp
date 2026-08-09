using System;
using PalLang;

/// <summary>
/// §7.2's variant for R9.21d, written independently of <c>Acct</c>/<c>Rewards</c> and
/// differently from it: the extension happens at the <em>second</em> level of a
/// three-level chain rather than the first, the base's model is a computed expression
/// rather than a bare field, the extending class is itself extended by a class that adds
/// no model of its own (so R9.21b's identity case sits directly on top of R9.6's
/// projection), and the forgetting function is a projection out of a two-field record
/// reached through an operation rather than a component accessor.
///
/// <para>This file must verify with no change to the translator. If it needs one, R9.21d
/// was fitted to <c>open_model</c>'s exact shape.</para>
/// </summary>
[assembly: IncludePulse("UserBoxV", """
module UserBoxV

/// A crate model: a volume and a label count.
noeq type crate = { vol: int; tags: int }

let mk (v t: int) : crate = { vol = v; tags = t }
let vol (c: crate) : int = c.vol
let tags (c: crate) : int = c.tags
""")]

[SpecType("UserBoxV.crate")]
public readonly struct SpecCrate
{
    private static Exception Ghost() => new InvalidOperationException(
        "SpecCrate is a specification-only construct and has no runtime meaning.");

    [SpecOp("UserBoxV.vol")]
    public SpecInt Vol => throw Ghost();

    [SpecOp("UserBoxV.tags")]
    public SpecInt Tags => throw Ghost();

    public static bool operator ==(SpecCrate a, SpecCrate b) => throw Ghost();
    public static bool operator !=(SpecCrate a, SpecCrate b) => throw Ghost();
    public override bool Equals(object? obj) => throw Ghost();
    public override int GetHashCode() => throw Ghost();
}

public static class SpecCrateOps
{
    private static Exception Ghost() => new InvalidOperationException(
        "SpecCrateOps is a specification-only construct and has no runtime meaning.");

    [SpecCtor("UserBoxV.mk")]
    public static SpecCrate Mk(SpecInt v, SpecInt t) => throw Ghost();
}

/// <summary>Level one: the model is a product of two fields, not a field.</summary>
[Invariant("wide >= 1")]
[Invariant("tall >= 1")]
[Invariant("wide * tall <= 2147483647")]
public class Box
{
    protected int wide;
    protected int tall;

    [Refine("Result >= 1")]
    [Model]
    protected virtual SpecInt Size => wide * tall;

    [Spec]
    public SpecInt TheSize => Size;

    [Requires("w >= 1")]
    [Requires("h >= 1")]
    [Requires("w * h <= 2147483647")]
    [Ensures("@this.TheSize == w * h")]
    public Box(int w, int h) { wide = w; tall = h; }

    [Frac("p")]
    [Ensures("Result == @this.TheSize")]
    public virtual int Volume() { return wide * tall; }
}

/// <summary>Level two: this is where the model grows.</summary>
[Invariant("tagged >= 0")]
public class Crate : Box
{
    private int tagged;

    [Refine("Result.Vol >= 1 && Result.Tags >= 0")]
    [Model]
    private SpecCrate Whole => SpecCrateOps.Mk(wide * tall, tagged);

    [Spec]
    public SpecInt TheTags => Whole.Tags;

    protected override SpecInt Size => Whole.Vol;

    [Requires("w >= 1")]
    [Requires("h >= 1")]
    [Requires("w * h <= 2147483647")]
    [Ensures("@this.TheSize == w * h")]
    [Ensures("@this.TheTags == 0")]
    public Crate(int w, int h) : base(w, h) { tagged = 0; }

    [Requires("k >= 0")]
    [Requires("@this.TheTags + k <= 2147483647")]
    [Ensures("@this.TheTags == Old(@this.TheTags) + k")]
    [Ensures("@this.TheSize == Old(@this.TheSize)")]
    public void Tag(int k) { tagged = tagged + k; }

    [Frac("p")]
    [Ensures("Result == @this.TheTags")]
    public int Tags() { return tagged; }
}

/// <summary>
/// Level three: adds no model of its own, so R9.21b's identity forgetting sits directly
/// on top of R9.6's projection. It inherits <c>Crate</c>'s model whole, which is the case
/// that must keep working now that the case below it does not.
/// </summary>
public class Pallet : Crate
{
    [Requires("w >= 1")]
    [Requires("h >= 1")]
    [Requires("w * h <= 2147483647")]
    [Ensures("@this.TheSize == w * h")]
    [Ensures("@this.TheTags == 0")]
    public Pallet(int w, int h) : base(w, h) { }
}

public static class Depot
{
    /// <summary>The grown model, exact, two levels below where it was declared.</summary>
    [Ensures("Result == 4")]
    public static int TagsOfPallet()
    {
        Pallet p = new Pallet(2, 3);
        p.Tag(4);
        return p.Tags();
    }

    /// <summary>Forgotten twice over: through <c>Crate</c>'s projection, to <c>Box</c>.</summary>
    [Ensures("Result == 6")]
    public static int SizeOfPallet()
    {
        Pallet p = new Pallet(2, 3);
        p.Tag(4);
        Box b = p;
        return b.Volume();
    }

    /// <summary>The base on its own, with no extension anywhere in sight.</summary>
    [Ensures("Result == 12")]
    public static int PlainBox()
    {
        Box b = new Box(3, 4);
        return b.Volume();
    }
}
