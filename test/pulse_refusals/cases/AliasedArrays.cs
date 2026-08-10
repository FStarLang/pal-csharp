// EXPECT-PULSE: Cannot prove: A.pts_to var_a
// R4.1. Two array parameters are two separating conjuncts, so a caller that passes the same
// array for both is asking to own it twice. Nothing in the frontend says so: the refusal is
// arithmetic on permissions, and it happens where the permissions are.
//
// This is the array-level twin of `AliasedObjects`, and it earns its place because it is
// the aliasing a C# programmer actually writes. `Copy` is perfectly provable on its own --
// the fault is entirely at the call site, which is the property that makes separation logic
// worth the trouble.
using PalLang;

public static class AliasedArrays
{
    [Requires("Contents(dst).Length > 0 && Contents(src).Length > 0")]
    [Ensures("Contents(dst).Length > 0 && Contents(dst)[0] == Old(Contents(src))[0]")]
    public static void Copy(int[] dst, int[] src)
    {
        dst[0] = src[0];
    }

    [Requires("Contents(a).Length > 0")]
    public static void CopyOntoItself(int[] a)
    {
        // MARKER
        Copy(a, a);
    }
}
