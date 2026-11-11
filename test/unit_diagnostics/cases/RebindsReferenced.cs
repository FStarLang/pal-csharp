// EXPECT: PALCS0760
// REFERENCES: lib
// R36.6. The referenced unit binds `IEqualityComparer<T>` to another term.
using PalLang;

[assembly: SpecBinding("T:System.Collections.Generic.IEqualityComparer`1", "Pulse.Lib.CSharp.Equality.default_comparer")]

public static class Rebinds
{
    [Ensures("Result == x")]
    public static int Id(int x)
    {
        return x;
    }
}
