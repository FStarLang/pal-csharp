// §7.2's variant detector for the fractional-object rules. The same facts, written every
// other way C# allows: the observations read through `this.` and expression bodies, the
// permission variables renamed and the parameters given in the other order, the two-name
// alias reached through a local rather than through the parameter directly, the array
// scan descending instead of ascending, the owner's parts summed by a local rather than
// in one expression, and the round trip written with the mutation before the observation
// instead of after.
//
// What must not differ is the shape of the emitted Pulse: every read-only member is
// generalised over a permission because R4.11b's write-set analysis says so and not
// because of how it was spelled, every `[Frac]` parameter gets its own binder, and every
// `Pal.Share` becomes the lemma for its argument's type.
using PalLang;

namespace PalCSharp.Tests;

[Invariant("0 <= ticks")]
public sealed class Dial
{
    private int ticks;

    [Refine("0 <= Result")]
    [Model]
    private SpecInt Model => this.ticks;

    [Spec]
    public SpecInt Level => Model;

    [Ensures("@this.Level == 0")]
    public Dial()
    {
        ticks = 0;
    }

    [Ensures("Result == @this.Level")]
    public int Peek() => this.ticks;

    [Requires("@this.Level < 2147483647")]
    [Ensures("@this.Level == Old(@this.Level) + 1")]
    public void Tick()
    {
        int next = this.ticks + 1;
        ticks = next;
    }
}

[Spec]
public struct TwoModel
{
    public SpecInt Second;
    public SpecInt First;
}

public sealed class Two
{
    private Dial b;
    private Dial a;

    [Refine("0 <= Result.First && 0 <= Result.Second && " +
            "Result.First + Result.Second <= 2147483647")]
    [Model]
    private TwoModel Model => new TwoModel { Second = this.b.Level, First = this.a.Level };

    [Spec]
    public TwoModel State => Model;

    [Spec]
    public SpecInt Both => Model.First + Model.Second;

    [Ensures("@this.Both == 0")]
    public Two()
    {
        b = new Dial();
        a = new Dial();
    }

    [Ensures("Result == @this.Both")]
    public int Sum()
    {
        int second = this.b.Peek();
        int first = this.a.Peek();
        return first + second;
    }
}

public static class AliasVariant
{
    /// <summary>
    /// The permissions renamed and the comparison written the other way round. The two
    /// binders stay independent, which is the only thing that matters.
    /// </summary>
    [Ensures("Result == (y.Level == x.Level)")]
    public static bool Matches([Frac("qy")] Dial y, [Frac("qx")] Dial x)
    {
        int ly = y.Peek();
        int lx = x.Peek();
        return lx == ly;
    }

    /// <summary>
    /// The alias reached through a local. <c>d</c> and <c>same</c> are one object as far as
    /// C# is concerned and two names as far as the reader is concerned, which is precisely
    /// the case R3.13 says no frontend can recognise — and does not have to, because the
    /// split is written down.
    /// </summary>
    [Ensures("Result")]
    public static bool SelfMatch(Dial d)
    {
        Dial same = d;
        Pal.Share(same);
        bool r = Matches(same, d);
        Pal.Gather(d);
        return r;
    }

    /// <summary>
    /// The round trip with the mutation first. <c>Tick</c> needs full ownership, so it has
    /// to come before the <c>Share</c> or after the <c>Gather</c>; here it comes before,
    /// and the observation that follows sees the incremented value.
    /// </summary>
    [Requires("@d.Level < 2147483647")]
    [Ensures("@d.Level == Old(@d.Level) + 1")]
    public static void MutateThenObserve(Dial d)
    {
        d.Tick();
        Pal.Share(d);
        bool agreed = Matches(d, d);
        Pal.Gather(d);
        Pal.Assert(agreed);
    }

    [Spec]
    public static bool Differs(Seq<int> s, Seq<int> t, SpecInt n) =>
        Pal.Exists((SpecInt k) => n <= k && 0 <= k && k < s.Length && k < t.Length && s[k] != t[k]);

    /// <summary>A descending scan, with the disagreement stated over a suffix.</summary>
    [Requires("u.Length == w.Length")]
    [Ensures("Implies(!Result, AliasVariant.Differs(Contents(u), Contents(w), 0))")]
    public static bool Alike([Frac("qu")] int[] u, [Frac("qw")] int[] w)
    {
        bool bad = false;
        int j = u.Length;
        while (j > 0 && !bad)
        {
            Pal.Invariant(0 <= j && j <= u.Length);
            Pal.Invariant(Pal.Implies(bad, Differs(Pal.Contents(u), Pal.Contents(w), 0)));
            Pal.Decreases(j);
            j = j - 1;
            if (u[j] != w[j])
            {
                bad = true;
            }
        }
        return !bad;
    }

    [Ensures("Result")]
    public static bool AlikeToItself(int[] u)
    {
        Pal.Share(u);
        bool r = Alike(u, u);
        Pal.Gather(u);
        return r;
    }

    /// <summary>The owner case, summed through a local and shared through one name.</summary>
    [Requires("2 * @t.Both <= 2147483647")]
    [Ensures("Result == @t.Both + @t.Both")]
    public static int Twice(Two t)
    {
        Pal.Share(t);
        int left = t.Sum();
        int right = t.Sum();
        Pal.Gather(t);
        return left + right;
    }
}
