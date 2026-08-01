// Loop escapes. Pulse has no `break` and no `continue`, so R5.11 threads an escape flag
// through the loop body: `break` sets a flag allocated before the loop, which its guard
// and its measure both consult; `continue` sets a flag allocated inside the body and
// reset on every iteration. The remainder of a sequence after a statement that may escape
// is emitted under a test of those flags.
//
// The `continue` case is the interesting one to get right, and this file is written so
// that getting it wrong fails: C# runs a `for` step after a `continue`, so if the step
// were swallowed by the escape guard the counter would stall and the loop's measure would
// not decrease. Termination is therefore the test.
using PalLang;

public static class Escapes
{
    /// <summary>Every entry of <c>s</c> in <c>[lo, hi)</c> is non-zero.</summary>
    [Spec]
    public static bool AllNonZero(Seq<int> s, SpecInt lo, SpecInt hi) =>
        Pal.Forall((SpecInt i) =>
            Pal.Implies(lo <= i && i < hi && 0 <= i && i < s.Length, s[i] != 0));

    /// <summary>
    /// The first index holding <paramref name="key"/>, or -1. The postcondition is
    /// functional in the positive case: the answer really is an index, and it really
    /// holds the key.
    /// </summary>
    [Ensures("Result == -1 || (0 <= Result && Result < a.Length && Contents(a)[Result] == key)")]
    public static int Find(int[] a, int key)
    {
        int found = -1;
        for (int i = 0; i < a.Length; i++)
        {
            Pal.Invariant(0 <= i && i <= a.Length);
            Pal.Invariant(found == -1 ||
                (0 <= found && found < a.Length && Pal.Contents(a)[found] == key));
            if (a[i] == key)
            {
                found = i;
                break;
            }
        }
        return found;
    }

    /// <summary>
    /// How many entries of <paramref name="a"/> are non-zero, computed by skipping the
    /// zeroes with <c>continue</c>. The postcondition pins the count exactly in the case
    /// where nothing was skipped.
    /// </summary>
    [Ensures("0 <= Result && Result <= a.Length")]
    [Ensures("Implies(Escapes.AllNonZero(Contents(a), 0, a.Length), Result == a.Length)")]
    public static int CountNonZero(int[] a)
    {
        int c = 0;
        for (int i = 0; i < a.Length; i++)
        {
            Pal.Invariant(0 <= i && i <= a.Length);
            Pal.Invariant(0 <= c && c <= i);
            Pal.Invariant(Pal.Implies(AllNonZero(Pal.Contents(a), 0, i), c == i));
            if (a[i] == 0)
            {
                continue;
            }
            c = c + 1;
        }
        return c;
    }
}
