using System;
using PalLang;
namespace PalCSharp.Tests;

public sealed class ReopenOther
{
    private int value;
#if PAL
    [Model] private SpecInt Model => value;
    [Spec] public SpecInt Value => Model;
#endif
    [Ensures("@this.Value == initial")]
    public ReopenOther(int initial) { value = initial; }

    [Frac("p"), Ensures("Result == @this.Value")]
    [Throws(typeof(InvalidOperationException), "@this.Value < 0")]
    public int ReadOrRaise()
    {
        if (value < 0) throw new InvalidOperationException();
        return value;
    }
}

[Invariant("OwnerSpec.Holds(cell, 0, Pal.Permission())")]
[Invariant("value >= 0")]
public sealed class ReopenOwner
{
    private OwnedCell cell;
    private int value;
    private int hidden;
#if PAL
    [Model, Refine("Result >= 0")]
    private SpecInt Model => value;
    [Spec] public SpecInt Value => Model;
#endif

    [Requires("initial >= 0")]
    [Requires("OwnerSpec.Holds(initialCell, 0, Perm.Full)")]
    [Ensures("@this.Value == initial")]
    public ReopenOwner(OwnedCell initialCell, int initial, int hiddenValue)
    {
        value = initial;
        hidden = hiddenValue;
        cell = initialCell;
    }

    [Requires("steps >= 0 && @this.Value < int.MaxValue")]
    [Throws(typeof(InvalidOperationException), "other.Value < 0")]
    [Ensures("Result == steps && @this.Value == Pal.Old(@this.Value) + 1")]
    public int Loop(ReopenOther other, int steps)
    {
        int saved = hidden;
        value++;
        int i = 0;
        while (i < steps)
        {
#if PAL
            Pal.Invariant(OwnerSpec.Holds(cell, 0, Pal.Permission()));
            Pal.Invariant(0 <= i && i <= steps && this.Value == Pal.Old(this.Value) + 1);
#endif
            Pal.Decreases(steps - i);
            other.ReadOrRaise();
            i++;
        }
        return i;
    }

    [Frac("p"), Requires("steps >= 0")]
    [Throws(typeof(InvalidOperationException), "other.Value < 0")]
    [Ensures("Result == steps && @this.Value == Pal.Old(@this.Value)")]
    public int ReadOnlyLoop(ReopenOther other, int steps)
    {
        int saved = hidden;
        int i = 0;
        while (i < steps)
        {
#if PAL
            Pal.Invariant(OwnerSpec.Holds(cell, 0, Pal.Permission()));
            Pal.Invariant(0 <= i && i <= steps && this.Value == Pal.Old(this.Value));
#endif
            Pal.Decreases(steps - i);
            other.ReadOrRaise();
            i++;
        }
        return i;
    }

    [Frac("p"), Requires("steps >= 0")]
    [Ensures("Result == steps && @this.Value == Pal.Old(@this.Value)")]
    public int NoReopenLoop(int steps)
    {
        int saved = hidden;
        int i = 0;
        while (i < steps)
        {
            Pal.Invariant(OwnerSpec.Holds(cell, 0, Pal.Permission()));
            Pal.Invariant(0 <= i && i <= steps && hidden == saved);
            Pal.Decreases(steps - i);
            i++;
        }
        Pal.Assert(hidden == saved);
        return i;
    }
}
