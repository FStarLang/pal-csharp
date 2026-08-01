// EXPECT: PALCS0001
// R3.5. Only object-initializer construction is translated. A user-written constructor
// has a body, and running that body at every construction site is method translation,
// not expression translation; it is deliberately not attempted rather than silently
// approximated.
using PalLang;

public struct Pair
{
    public int A;
    public int B;

    public Pair(int a, int b)
    {
        A = a;
        B = b;
    }
}

public static class Pairs
{
    [Ensures("Result.A == 1")]
    public static Pair Make()
    {
        return new Pair(1, 2);
    }
}
