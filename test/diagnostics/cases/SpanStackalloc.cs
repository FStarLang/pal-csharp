// EXPECT: PALCS0590
// R17.7, R17.9. `stackalloc` is admitted only as the whole initializer of a span local,
// with a size and no element list: that form is a fresh span the local owns. With an
// element list it is still refused.
using System;
using PalLang;

public static class Stack
{
    public static int Scratch()
    {
        Span<int> s = stackalloc int[] { 1, 2, 3, 4 };
        s[0] = 1;
        return s[0];
    }
}
