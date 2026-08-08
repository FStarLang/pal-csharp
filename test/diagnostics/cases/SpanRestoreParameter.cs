// EXPECT: PALCS0590
// R17.7. `Pal.Restore` of a span *parameter*. A restore gives a window back to whoever lent
// it, and which operation does that is read off the borrow that created the window
// (R17.6). A parameter was borrowed by somebody else, in another method, whose receipt this
// method does not hold — there is nothing here to give back to. A caller that owns the
// array restores it at its own borrow site.
using System;
using PalLang;

public static class RestoreParam
{
    public static void GiveBack(Span<int> s)
    {
        Pal.Restore(s);
    }
}
