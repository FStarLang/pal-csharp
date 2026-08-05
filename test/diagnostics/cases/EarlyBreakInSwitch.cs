// EXPECT: PALCS0577
// R5.14. Inside a `switch`, `break` means "leave the switch"; inside a loop it means
// "leave the loop"; and here both constructs are in scope, so which one is meant is
// decided by which encloses the statement. The section's *final* `break` is its
// terminator and goes with the section when the `switch` becomes an if/else chain. This
// one does not: after the rewrite there is no switch left to leave, and the nearest
// construct it could bind to is the `while`. Translating it would change the program, so
// it is refused instead.
using PalLang;

public static class EarlyBreak
{
    public static int Scan(int[] a, int stop)
    {
        int seen = 0;
        while (seen < a.Length)
        {
            switch (a[seen])
            {
                case 0:
                    if (stop == 0) break;
                    seen = seen + 1;
                    break;
                default:
                    seen = seen + 1;
                    break;
            }
        }
        return seen;
    }
}
