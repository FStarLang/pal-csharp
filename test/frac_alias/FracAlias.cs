// Read-only aliasing (R3.10c, R3.10d, R4.9a, R4.11b, R5.13).
//
// An object invariant is indexed by a permission, and the permission propagates into
// everything the object owns — its box, its arrays, its sub-objects. So an object can be
// held at a fraction, and two names can hold fractions of the same object at once. That is
// the whole feature, and everything below is a consequence of it.
//
// The two halves of the feature that need saying out loud:
//
//   * Pulse does not split a permission by itself (F25). `Compare(g, g)` fails against a
//     context holding exactly `class_Gauge__inv g m`, because matching consumes the
//     resource for the first parameter and there is nothing left for the second. So the
//     split is written — `Pal.Share` — and it is written by the author, because deciding
//     where to split means recognising aliasing, and a frontend cannot do that (R3.13).
//
//   * `Pal.Gather` proves the two views *agreed* (F23). That is not an extra hypothesis:
//     the model is pinned to the abstraction function of the representation, gathering
//     proves the representations equal, and a function of equal arguments is equal. Two
//     observers of one object necessarily see the same thing — which is the entire reason
//     to allow them.
using PalLang;

namespace PalCSharp.Tests;

/// <summary>
/// A one-field object, so that nothing here is about depth. <c>test/deep_class</c> is where
/// nesting is tested; this file is about the permission.
/// </summary>
[Invariant("n >= 0")]
public sealed class Gauge
{
    private int n;

    [Refine("Result >= 0")]
    [Model]
    private SpecInt Model => n;

    [Spec]
    public SpecInt Reading => Model;

    [Ensures("@this.Reading == 0")]
    public Gauge()
    {
        n = 0;
    }

    /// <summary>
    /// A mutator. It needs full ownership, and nothing says so in C#: R4.11 gives it a
    /// receiver at <c>1.0R</c> because it assigns a field, and a caller holding half is
    /// refused by Pulse rather than by pal-csharp (§0 rule 3, the other direction).
    /// </summary>
    [Requires("@this.Reading < 2147483647")]
    [Ensures("@this.Reading == Old(@this.Reading) + 1")]
    public void Bump()
    {
        n = n + 1;
    }

    /// <summary>
    /// R4.11b. This method assigns nothing, so the same analysis that gives it
    /// <c>preserves</c> gives it a permission binder, and its receiver is held at that
    /// permission rather than at <c>1.0R</c>. No annotation is involved and none is
    /// offered: a caller with full ownership is unaffected — Pulse instantiates the binder
    /// at <c>1.0R</c> and the call site is textually what it was — so unlike
    /// <c>[Frac]</c> on a parameter this weakens nothing and can be given for free.
    /// </summary>
    [Ensures("Result == @this.Reading")]
    public int Read()
    {
        return n;
    }
}

/// <summary>
/// An owner, to check that the fraction really does reach the parts. <c>Total</c> is
/// read-only, so R4.11b holds its receiver at <c>#p</c>; R3.10c then hands it its two
/// <c>Gauge</c>s at <c>#p</c> as well, and it can only call <c>Gauge.Read</c> on them
/// because R4.11b generalised <em>that</em> over the permission too. Fix a part's readers
/// at <c>1.0R</c> and no fractional owner could read its own parts: the two rules do not
/// merely coexist, one is what makes the other compose.
/// </summary>
[Spec]
public struct PairModel
{
    public SpecInt Lo;
    public SpecInt Hi;
}

public sealed class Pair
{
    private Gauge lo;
    private Gauge hi;

    [Refine("0 <= Result.Lo && 0 <= Result.Hi && Result.Lo + Result.Hi <= 2147483647")]
    [Model]
    private PairModel Model => new PairModel { Lo = lo.Reading, Hi = hi.Reading };

    [Spec]
    public PairModel State => Model;

    [Spec]
    public SpecInt Sum => Model.Lo + Model.Hi;

    [Ensures("@this.Sum == 0")]
    public Pair()
    {
        lo = new Gauge();
        hi = new Gauge();
    }

    [Ensures("Result == @this.Sum")]
    public int Total()
    {
        return lo.Read() + hi.Read();
    }
}

public static class Aliasing
{
    /// <summary>
    /// R4.9a. Two object parameters at <em>independent</em> permissions, which is exactly
    /// what makes them allowed to be the same object: one shared binder would forbid it
    /// again by construction. An observed object contributes no existential to the
    /// postcondition, so this contract can talk about both readings with no <c>Old</c> and
    /// no frame reasoning.
    /// </summary>
    [Ensures("Result == (a.Reading == b.Reading)")]
    public static bool SameReading([Frac("pa")] Gauge a, [Frac("pb")] Gauge b)
    {
        return a.Read() == b.Read();
    }

    /// <summary>
    /// The point of the whole exercise: one object passed to both parameters. Without
    /// <c>Pal.Share</c> this is <c>Cannot prove: class_Gauge__inv var_g _</c> against a
    /// context holding precisely that — F25, which is why the rule exists.
    ///
    /// The postcondition needs no re-establishing after the gather, and that is F23 doing
    /// the work: gathering proves the two halves agreed, so the model coming out is the
    /// model that went in, and <c>preserves</c> holds without a word about it.
    /// </summary>
    [Ensures("Result")]
    public static bool AgreesWithItself(Gauge g)
    {
        Pal.Share(g);
        bool same = SameReading(g, g);
        Pal.Gather(g);
        return same;
    }

    /// <summary>
    /// More than two observers, done the way F27 says it has to be: by *nesting*, not by
    /// sharing twice. The permission itself splits without bound — <c>share</c> halves
    /// whatever it is given — but three views of one name are three resources with the
    /// same head, and matching an slprop against the context is a search for a
    /// <em>unique</em> candidate. A second <c>Pal.Share</c> here and the next call is
    /// refused, by Pulse, listing the thing it wanted three times over.
    ///
    /// Nothing in pal-csharp knows about that, which is the point: it is a fact about the
    /// prover's matcher, and R2.3 carries it back to the C# line that caused it.
    /// </summary>
    [Ensures("Result == @g.Reading")]
    public static int ThreeObservers(Gauge g)
    {
        Pal.Share(g);
        bool first = SameReading(g, g);
        Pal.Gather(g);

        Pal.Share(g);
        bool second = SameReading(g, g);
        int seen = g.Read();
        Pal.Gather(g);

        Pal.Assert(first && second);
        return seen;
    }

    /// <summary>
    /// The round trip restores full ownership, so a mutator is callable again afterwards.
    /// This is what R3.10d's third lemma buys: <c>Gather</c> is stated as <c>Share</c>'s
    /// exact inverse, so the permission arithmetic is discharged once inside the lemma
    /// rather than surfacing here as a fact about <c>p /. 2.0R +. p /. 2.0R</c> — which
    /// would be a statement about the encoding and not about the program.
    /// </summary>
    [Requires("@g.Reading < 2147483647")]
    [Ensures("@g.Reading == Old(@g.Reading) + 1")]
    public static void ObserveThenMutate(Gauge g)
    {
        Pal.Share(g);
        bool agreed = SameReading(g, g);
        Pal.Gather(g);
        Pal.Assert(agreed);
        g.Bump();
    }

    /// <summary>
    /// The same closure for arrays. R4.9 has claimed since M1 that "the same array may be
    /// passed to two parameters at once", and until <c>Pal.Share</c> existed that claim was
    /// not actually reachable — <c>test/compare_elements</c> documents the two <c>[Frac]</c>
    /// parameters but has no caller that aliases them. F25 says Pulse does not split for an
    /// array either, so this is the missing half.
    /// </summary>
    [Spec]
    public static bool Agree(Seq<int> s, Seq<int> t, SpecInt n) =>
        Pal.Forall((SpecInt k) =>
            Pal.Implies(0 <= k && k < n && k < s.Length && k < t.Length, s[k] == t[k]));

    [Requires("a.Length == b.Length")]
    [Ensures("Implies(Result, Aliasing.Agree(Contents(a), Contents(b), a.Length))")]
    [Ensures("Implies(!Result, Exists((SpecInt k) => " +
             "0 <= k && k < a.Length && Contents(a)[k] != Contents(b)[k]))")]
    public static bool Equal([Frac("pa")] int[] a, [Frac("pb")] int[] b)
    {
        bool same = true;
        for (int i = 0; i < a.Length && same; i++)
        {
            Pal.Invariant(0 <= i && i <= a.Length);
            Pal.Invariant(Pal.Implies(same, Agree(Pal.Contents(a), Pal.Contents(b), i)));
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
    /// The array halves agree because they are halves of one array — the same content F23
    /// carries for objects, arriving here through <c>Array.gather</c> instead. A false
    /// answer would exhibit an index at which the array differs from itself.
    /// </summary>
    [Ensures("Result")]
    public static bool ArrayEqualsItself(int[] a)
    {
        Pal.Share(a);
        bool same = Equal(a, a);
        Pal.Gather(a);
        return same;
    }

    /// <summary>
    /// An owner observed through a fraction, and its parts with it. Nothing here mentions
    /// a <c>Gauge</c>: the fraction reaches them through <c>Pair</c>'s invariant, which is
    /// R3.10c's claim that an object at <c>p</c> is one every part of which is held at
    /// <c>p</c>.
    /// </summary>
    [Requires("@p.Sum + @q.Sum <= 2147483647")]
    [Ensures("Result == @p.Sum + @q.Sum")]
    public static int Combined([Frac("pp")] Pair p, [Frac("pq")] Pair q)
    {
        return p.Total() + q.Total();
    }

    [Requires("2 * @p.Sum <= 2147483647")]
    [Ensures("Result == 2 * @p.Sum")]
    public static int Doubled(Pair p)
    {
        Pal.Share(p);
        int total = Combined(p, p);
        Pal.Gather(p);
        return total;
    }
}
