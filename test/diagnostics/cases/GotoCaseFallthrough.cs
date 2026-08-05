// EXPECT: PALCS0001
// R5.14. C# forbids implicit fallthrough (CS0163), which is what lets a `switch` become a
// plain if/else chain: the sections are disjoint, so nothing has to carry control from one
// arm into the next. PAL, translating C, has no such luck — it threads a `hit` flag through
// the whole desugaring so that a case body can run because an *earlier* case matched.
//
// `goto case` and `goto default` are the exception C# left open, and they ask for exactly
// the thing the chain cannot express: entry into one arm from inside another. So they are
// refused rather than approximated. The two honest rewrites are in the message — stack the
// labels when the other section should run *instead*, and factor out a method when it
// should run *as well*.
using PalLang;

public static class Falling
{
    public static int Classify(int k)
    {
        int r = 0;
        switch (k)
        {
            case 0:
                r = 1;
                goto case 1;
            case 1:
                r = r + 10;
                break;
            default:
                break;
        }
        return r;
    }
}
