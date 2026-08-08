// The §7.2 variant of `Temperature`: the same object and the same overload sets, written
// differently. The constructors are declared in the opposite order, the chain runs to
// depth two the other way round, the general constructor is the *last* one declared, the
// overloaded method takes its extra argument first, and the fields are read through an
// explicit `this.`.
//
// The variant exists to detect a translator fitted to one example. R2.1a's suffix is a
// function of the signature and not of declaration order, so reordering must change
// nothing; if it did, the module a caller referred to would depend on where in the file
// its callee happened to sit.
using PalLang;

namespace Instruments;

[Spec]
public struct Sample
{
    public SpecInt Unit;
    public SpecInt Level;
    public SpecInt Floor;
}

[Invariant("least <= amount")]
public sealed class Pressure
{
    /// <summary>
    /// The variant puts the initialiser on the *first* field and gives it a value the
    /// general constructor does not overwrite with a constant, so a scheme that quietly
    /// ordered initialisers after the body, or ran them in the chaining constructors too,
    /// would build the wrong representation rather than the same one twice.
    /// </summary>
    private int amount = 0;

    /// <summary>
    /// The initialiser-only field, declared *last* here and with a different value, so a
    /// scheme that had quietly fixed the position or the value in the emitter rather than
    /// reading it from the declaration would show up.
    /// </summary>
    private int least;

    private int unit = 2;

    [Model]
    private Sample Model => new Sample { Unit = this.unit, Level = this.amount, Floor = this.least };

    [Spec]
    public SpecInt Level => Model.Level;

    [Spec]
    public SpecInt Floor => Model.Floor;

    [Spec]
    public SpecInt Unit => Model.Unit;

    /// <summary>Declared first here, and chained to from below.</summary>
    [Ensures("@this.Level == 0")]
    [Ensures("@this.Floor == 0")]
    [Ensures("@this.Unit == 2")]
    public Pressure() : this(0)
    {
    }

    [Requires("0 <= n")]
    [Ensures("@this.Level == n")]
    [Ensures("@this.Floor == 0")]
    [Ensures("@this.Unit == 2")]
    public Pressure(int n) : this(n, 0)
    {
    }

    /// <summary>The general constructor, declared last.</summary>
    [Requires("f <= n")]
    [Ensures("@this.Level == n")]
    [Ensures("@this.Floor == f")]
    [Ensures("@this.Unit == 2")]
    public Pressure(int n, int f)
    {
        this.amount = n;
        this.least = f;
    }

    [Ensures("Result == @this.Level")]
    public int Level_()
    {
        return this.amount;
    }

    /// <summary>
    /// The variant's instance overload set is three deep rather than two, and the
    /// no-argument member is *not* the one written first — a scheme that had let the
    /// declaration order or the arity of the first member reach the suffix would build
    /// different names here than for <c>Temperature.Get</c>.
    /// </summary>
    [Requires("-1000000 <= k && k <= 1000000")]
    [Requires("-1000000 <= @this.Level && @this.Level <= 1000000")]
    [Ensures("Result == @this.Level + k")]
    public int Read(int k)
    {
        return this.amount + k;
    }

    [Ensures("Result == @this.Level")]
    public int Read()
    {
        return this.amount;
    }

    [Requires("-1000000 <= @this.Level && @this.Level <= 1000000")]
    [Ensures("Result == @this.Level")]
    public int Read(Pressure other)
    {
        return this.amount;
    }

    /// <summary>Width-only overloads, with the wider member second here.</summary>
    [Requires("-1000000 <= @this.Level && @this.Level <= 1000000")]
    [Ensures("Result == @this.Level")]
    public long Widened(int factor)
    {
        return (long)this.amount;
    }

    [Requires("-1000000 <= @this.Level && @this.Level <= 1000000")]
    [Ensures("Result == @this.Level")]
    public long Widened(long factor)
    {
        return (long)this.amount;
    }
}

public static class Gauges
{
    /// <summary>The extra argument comes first, so the two suffixes differ in order too.</summary>
    [Requires("-1000000 <= k && k <= 1000000")]
    [Requires("-1000000 <= @p.Level && @p.Level <= 1000000")]
    [Ensures("Result == k + @p.Level")]
    public static int Sense(int k, Pressure p)
    {
        return k + p.Level_();
    }

    [Ensures("Result == @p.Level")]
    public static int Sense(Pressure p)
    {
        return p.Level_();
    }

    [Ensures("Result == 0")]
    public static int Ambient()
    {
        Pressure p = new Pressure();
        return Sense(p);
    }

    [Requires("0 <= n && n <= 1000000")]
    [Ensures("Result == n + 1")]
    public static int Raised(int n)
    {
        Pressure p = new Pressure(n);
        return Sense(1, p);
    }
}
