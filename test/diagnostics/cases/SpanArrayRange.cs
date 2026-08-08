// EXPECT: PALCS0590
// R17.7. A range applied to an *array* rather than to a span. `a[1..3]` looks like the
// window `s[1..3]` denotes, but C# compiles it to `RuntimeHelpers.GetSubArray`, which
// *copies*: the result is a fresh `int[]`, writes to it are invisible in `a`, and no
// ownership was borrowed. Translating it as a window would be translating a different
// program. It is refused rather than silently given the borrow's meaning.
using System;
using PalLang;

public static class ArrayRange
{
    public static void Middle(int[] a)
    {
        int[] w = a[1..3];
        w[0] = 0;
    }
}
