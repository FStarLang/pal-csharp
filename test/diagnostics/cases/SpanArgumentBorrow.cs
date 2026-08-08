// EXPECT: PALCS0590
// R17.7. The implicit `T[]` to `Span<T>` conversion, in argument position. Under R17.5 this
// conversion *is* a borrow, so `Wipe(a)` would consume `a`'s ownership and hand back a
// receipt that has no name — leaving the array unrecoverable, and failing far from the
// line that caused it. It is refused where it happens instead, and the fix is one line the
// author can see: name the borrow, pass the name, `Pal.Restore` it.
using System;
using PalLang;

public static class ImplicitArgument
{
    public static void Wipe(Span<int> s) { }

    public static void WipeAll(int[] a)
    {
        Wipe(a);
    }
}
