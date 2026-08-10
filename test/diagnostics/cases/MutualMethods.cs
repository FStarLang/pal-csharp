// EXPECT: PALCS0579
// R2.1 gives every method a module of its own, so a call is a reference to another module
// and a cycle of calls is a cycle among F* modules. F* does not report that as a program
// error: it fails with "Impossible: cycle detected after cycle detection has passed" and
// asks for a bug report. R10.7's `[Decreases]` is no answer either — a measure is checked
// within one definition, and mutual recursion has no one definition to check it in.
//
// It fails closed, so nothing false was ever provable this way; what it broke was the
// sentinel property, which says a program with no image under the scheme stops at the C#
// level with a message about the C#.
using PalLang;

public static class MutualMethods
{
    [Ensures("Result == 0")]
    public static int Ping(int n)
    {
        if (n == 0) { return 0; }
        return MutualMethods.Pong(n);
    }

    [Ensures("Result == 0")]
    public static int Pong(int n) => MutualMethods.Ping(n);
}
