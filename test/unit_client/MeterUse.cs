using PalLang;

namespace PalCSharp.Tests;

/// <summary>
/// A client of the unit <c>test/unit_lib</c> (doc/translation.md §36). Its Makefile names
/// that directory in <c>REFERENCES</c>, so <c>Meter</c> and <c>Clamp</c> are translated
/// there and only this class is translated here; F* uses the referenced unit's checked
/// modules for the calls.
/// </summary>
public static class MeterUse
{
    [Requires("@m.Value < 2147483646")]
    [Ensures("@m.Value == Old(@m.Value) + 2")]
    public static void TwoTicks(Meter m)
    {
        m.Tick();
        m.Tick();
    }

    /// <summary>An internal member of the referenced unit (R36.2).</summary>
    [Ensures("Result >= 0")]
    public static int Below(Meter m)
    {
        return Clamp.NonNegative(m.Read() - 1);
    }

    [Ensures("Result == 0")]
    public static int Fresh()
    {
        Meter m = new Meter();
        return m.Read();
    }
}
