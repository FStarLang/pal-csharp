// Fractional permissions (R4.9). `[Frac("p")]` says a parameter is *observed*, not owned:
// the callee gets `A.pts_to a #p s` and the caller keeps the rest, so the same array may
// be passed to two parameters at once. Because the permission is exactly the right to
// read, the contents cannot change, and the one binder `pre_a` stands for both the pre-
// and the post-state — a postcondition about an argument's final contents needs no
// existential and no frame reasoning.
//
// The methods here read two arrays and never write either, which is what makes the
// annotation honest rather than decorative: writing through one is rejected (PALCS0305).
using PalLang;

public static class Compare
{
    /// <summary>The two sequences agree on every index below <c>n</c>.</summary>
    [Spec]
    public static bool AgreeBelow(Seq<int> s, Seq<int> t, SpecInt n) =>
        Pal.Forall((SpecInt k) =>
            Pal.Implies(0 <= k && k < n && k < s.Length && k < t.Length, s[k] == t[k]));

    /// <summary>
    /// Whether two equally long arrays are equal. Both directions are proved: a true
    /// answer exhibits agreement everywhere, and a false one exhibits a witness.
    /// </summary>
    [Requires("a.Length == b.Length")]
    [Ensures("Implies(Result, Compare.AgreeBelow(Contents(a), Contents(b), a.Length))")]
    [Ensures("Implies(!Result, Exists((SpecInt k) => " +
             "0 <= k && k < a.Length && Contents(a)[k] != Contents(b)[k]))")]
    public static bool Equal([Frac("pa")] int[] a, [Frac("pb")] int[] b)
    {
        bool same = true;
        // The exit condition is carried by the guard rather than by a `break`, because the
        // postcondition needs to know *why* the loop stopped. R5.10's break flag is
        // internal to the translation and cannot be named in an invariant, so a
        // `break` here would leave "the loop ran to completion" unstatable. The operand
        // whose dereferences the body needs comes first (see R6.3).
        for (int i = 0; i < a.Length && same; i++)
        {
            Pal.Invariant(0 <= i && i <= a.Length);
            Pal.Invariant(Pal.Implies(same, AgreeBelow(Pal.Contents(a), Pal.Contents(b), i)));
            Pal.Invariant(Pal.Implies(!same, Pal.Exists((SpecInt k) =>
                0 <= k && k < a.Length && Pal.Contents(a)[k] != Pal.Contents(b)[k])));
            if (a[i] != b[i])
            {
                same = false;
            }
        }
        return same;
    }

    /// <summary>
    /// How many indices below <c>a.Length</c> the two arrays agree on. Reading the *same*
    /// array through both parameters is legal here and is not expressible without
    /// fractional permissions.
    /// </summary>
    [Requires("a.Length == b.Length")]
    [Ensures("0 <= Result && Result <= a.Length")]
    [Ensures("Implies(Compare.AgreeBelow(Contents(a), Contents(b), a.Length), Result == a.Length)")]
    public static int CountAgreements([Frac("pa")] int[] a, [Frac("pb")] int[] b)
    {
        int n = 0;
        for (int i = 0; i < a.Length; i++)
        {
            Pal.Invariant(0 <= i && i <= a.Length);
            Pal.Invariant(0 <= n && n <= i);
            Pal.Invariant(Pal.Implies(
                AgreeBelow(Pal.Contents(a), Pal.Contents(b), i), n == i));
            if (a[i] == b[i])
            {
                n = n + 1;
            }
        }
        return n;
    }
}
