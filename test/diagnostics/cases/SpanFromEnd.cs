// EXPECT: PALCS0590
// R17.7. `^k` in a range. The from-end index is `s.Length - k`, which is a perfectly
// ordinary bound — but it is computed by `System.Index`'s conversion rather than written
// in the source, and §0's rule against inventing steps applies to arithmetic as much as to
// proofs. Supporting it means a rule that says what `^k` elaborates to; until that rule
// exists the translator says so rather than guessing.
using System;
using PalLang;

public static class FromEnd
{
    public static void Tail(Span<int> s)
    {
        Span<int> w = s[1..^1];
        w[0] = 0;
    }
}
