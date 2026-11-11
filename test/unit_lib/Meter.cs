using PalLang;

namespace PalCSharp.Tests;

/// <summary>
/// A verification unit (doc/translation.md §36) that <c>test/unit_client</c> references: it
/// is translated and verified here, once, and the client uses its modules without
/// translating or checking them again.
/// </summary>
[Invariant("level >= 0")]
public sealed class Meter
{
    private int level;

    [Refine("Result >= 0")]
    [Model]
    private SpecInt Model => level;

    [Spec]
    public SpecInt Value => Model;

    [Ensures("@this.Value == 0")]
    public Meter()
    {
        level = 0;
    }

    [Requires("@this.Value < 2147483647")]
    [Ensures("@this.Value == Old(@this.Value) + 1")]
    public void Tick()
    {
        level = level + 1;
    }

    [Ensures("Result == @this.Value")]
    public int Read()
    {
        return level;
    }
}

/// <summary>
/// Internal to the unit, and still callable from the client: a unit is a fragment of one
/// assembly's sources, so the units it is translated with see its internals (R36.2).
/// </summary>
internal static class Clamp
{
    [Ensures("Result >= 0")]
    [Ensures("Result >= x")]
    internal static int NonNegative(int x)
    {
        if (x < 0) return 0;
        return x;
    }
}
