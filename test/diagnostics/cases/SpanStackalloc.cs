// EXPECT: PALCS0590
// R17.7. `stackalloc` is an allocation, not a borrow: it produces a window of memory that
// no `T[]` owns, so there is no parent to consume and nothing for `Pal.Restore` to give
// back. Every other span in §17 begins life as somebody else's, which is what makes the
// borrow accounting work; this one would need a scoped-lifetime allocation rule of its
// own. §17.7 records it as deliberately out of scope.
using System;
using PalLang;

public static class Stack
{
    public static int Scratch()
    {
        Span<int> s = stackalloc int[4];
        s[0] = 1;
        return s[0];
    }
}
