// EXPECT: PALCS0580
// R14.1. A type parameter is translated exactly when it is unconstrained. A constraint is
// a typeclass obligation — `where T : IComparable<T>` means every call site must supply a
// dictionary, and dispatching through that dictionary inside the body is a translation
// that has not been designed or probed. Refusing is honest; translating with the
// constraint silently dropped would admit a program whose body cannot be written.
using PalLang;

public static class Constrained
{
    [Requires("0 <= i && i < a.Length")]
    public static void Touch<T>(T[] a, int i) where T : struct
    {
        T v = a[i];
        a[i] = v;
    }
}
