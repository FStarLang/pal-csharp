// EXPECT-PULSE: FStar.Seq.Base.upd
// R4.1. A method that claims to leave its argument alone and does not. This is worth its
// own case because the claim is the one callers lean on hardest: a postcondition that an
// array is unchanged is what lets a caller keep everything it knew about the array across
// the call, so an unsound one would poison the caller rather than this method.
using PalLang;

public static class PreservesViolated
{
    [Requires("Contents(a).Length > 0")]
    [Ensures("Contents(a) == Old(Contents(a))")]
    public static int Peek(int[] a)
    {
        int v = a[0];
        a[0] = 0;
        // MARKER
        return v;
    }
}
