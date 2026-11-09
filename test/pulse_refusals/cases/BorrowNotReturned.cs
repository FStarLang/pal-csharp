// EXPECT-PULSE: Span.is_from_array var_a var_s
// R17.5/R17.6. Creating a span consumes the parent array's ownership, and `Pal.Restore`
// is what gives it back. Nothing infers where a borrow ends -- that is the design, not an
// omission -- so a method that lends its array out and never takes it back cannot state a
// postcondition about the array, because it no longer holds it.
//
// This is the case the borrow rules exist for, and it is worth being precise about what
// fails: not the write through the span, which is fine, but the method's own postcondition,
// which mentions `Contents(a)` at a point where `a`'s permission is still inside the span.
using System;
using PalLang;

public static class BorrowNotReturned
{
    [Ensures("Contents(a).Length > 0 && Contents(a)[0] == 0")]
    [Requires("Contents(a).Length > 0")]
    // MARKER
    public static void ClearFirst(int[] a)
    {
        Span<int> s = a;
        s[0] = 0;
    }
}
