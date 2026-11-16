using System;
using PalLang;

namespace PalCSharp.Tests;

public static class ReadOnlySpanLoops
{
    public static int Length([Frac("p")] Span<int> a) => a.Length;

    public static int ReadOnlyLength(ReadOnlySpan<int> a) => a.Length;

    public static void BodyCall([Frac("p")] Span<int> a)
    {
        int i = 0;
        while (i < 2)
        {
            Pal.Invariant(0 <= i && i <= 2);
            Pal.Decreases(2 - i);
            Length(a);
            i++;
        }
    }

    public static void GuardCall(ReadOnlySpan<int> a)
    {
        int i = 0;
        while (i < 2 && ReadOnlyLength(a) > 0)
        {
            Pal.Invariant(0 <= i && i <= 2);
            Pal.Decreases(2 - i);
            i++;
        }
    }
}
