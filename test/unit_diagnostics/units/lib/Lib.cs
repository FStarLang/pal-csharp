using System.Collections.Generic;
using PalLang;

[assembly: SpecBinding("T:System.Collections.Generic.IEqualityComparer`1", "Pulse.Lib.CSharp.Equality.comparer")]

namespace PalCSharp.Tests;

/// <summary>A unit the cases reference (doc/translation.md §36).</summary>
public abstract class Shape
{
    [Refine("Result >= 0")]
    [Model]
    protected abstract SpecInt Area { get; }

    [Spec]
    public SpecInt TheArea => Area;
}

public static class Util
{
    [Ensures("Result == x")]
    public static int Id(int x)
    {
        return x;
    }
}
