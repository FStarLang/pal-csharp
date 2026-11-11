// EXPECT: PALCS0590
using System;
using PalLang;

public static class SpanBorrowNamedOrder
{
    [Requires("Contents(array).Length >= 3")]
    [Ensures("Result == 2")]
    public static int Count(int[] array)
    {
        var window = array.AsSpan(length: 1, start: 2);
        int length = window.Length;
        Pal.Restore(window);
        return length;
    }
}
