// EXPECT: PALCS0001
// R17.7. A span local that is assigned after its declaration. R17.6 reads the restore
// operation off the *initializer* — a syntactic property, fixed once, never a flow
// analysis. An assignment would make the question "which borrow is this" depend on the
// path taken to reach the restore, which is the borrow checker §17 exists to avoid. The
// window is immutable; a second window gets a second name. It is not a special case: a
// span local is bound with `let`, not `let mut`, so it simply is not an assignable target,
// and the general assignment rule refuses it.
using System;
using PalLang;

public static class Reassign
{
    public static void Shift(int[] a)
    {
        Span<int> w = a.AsSpan(0, 2);
        w = a.AsSpan(1, 2);
        Pal.Restore(w);
    }
}
