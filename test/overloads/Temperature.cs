// R2.1a and R4.12c. A class with more than one constructor -- which, before R2.1a, was a
// class pal-csharp could not translate at all, and did not say so: `Naming.Of` mapped both
// to `Func_Temperature__ctor` and the frontend crashed keying a dictionary by it.
//
// C# is why the rule is needed rather than merely nice. A method's author can rename it;
// `.ctor` has no name of its own, so without a signature in the module name a class may
// declare exactly one constructor. Constructors and method overloads take the same suffix,
// because they are the same problem and one rule is better than two.
using PalLang;

namespace Instruments;

/// <summary>
/// A temperature in whole degrees, held as a value and a scale flag.
/// </summary>
[Spec]
public struct Reading
{
    public SpecInt Degrees;
    public SpecInt Origin;
}

[Invariant("origin <= degrees")]
public sealed class Temperature
{
    private int degrees;
    private int origin;

    [Model]
    private Reading Model => new Reading { Degrees = degrees, Origin = origin };

    [Spec]
    public SpecInt Degrees => Model.Degrees;

    [Spec]
    public SpecInt Origin => Model.Origin;

    /// <summary>
    /// The general constructor. Its module is `Func_Temperature__ctor_int_int` -- the
    /// parameter types, `_`-joined, because it is one of an overload set.
    /// </summary>
    [Requires("o <= d")]
    [Ensures("@this.Degrees == d")]
    [Ensures("@this.Origin == o")]
    public Temperature(int d, int o)
    {
        this.degrees = d;
        this.origin = o;
    }

    /// <summary>
    /// R4.12c. A convenience overload: its body is the chained call and nothing else, so
    /// the emitted function is that call and its `[Ensures]` is discharged from the
    /// general constructor's contract rather than re-proved from the fields.
    /// </summary>
    [Requires("0 <= d")]
    [Ensures("@this.Degrees == d")]
    [Ensures("@this.Origin == 0")]
    public Temperature(int d) : this(d, 0)
    {
    }

    /// <summary>
    /// R2.1a again, on a zero-argument member: an empty parameter list renders `_unit`,
    /// so the module is `Func_Temperature__ctor_unit`. Chaining twice is chaining once at
    /// each step -- there is no depth rule, because R4.12c is not recursive.
    /// </summary>
    [Ensures("@this.Degrees == 0")]
    [Ensures("@this.Origin == 0")]
    public Temperature() : this(0)
    {
    }

    [Ensures("Result == @this.Degrees")]
    public int Get()
    {
        return degrees;
    }
}

public static class Scales
{
    /// <summary>
    /// A method overload set. Unlike a constructor these could have been given different
    /// names by their author, and the rule does not care: the collision is the same one.
    /// </summary>
    [Ensures("Result == @t.Degrees")]
    public static int Read(Temperature t)
    {
        return t.Get();
    }

    [Requires("-1000000 <= k && k <= 1000000")]
    [Requires("-1000000 <= @t.Degrees && @t.Degrees <= 1000000")]
    [Ensures("Result == @t.Degrees + k")]
    public static int Read(Temperature t, int k)
    {
        return t.Get() + k;
    }

    /// <summary>
    /// Each `new` resolves to the constructor C# resolved it to, so which module is called
    /// is Roslyn's answer and not a re-implementation of overload resolution.
    /// </summary>
    [Ensures("Result == 0")]
    public static int Freezing()
    {
        Temperature t = new Temperature();
        return Read(t);
    }

    [Requires("0 <= d && d <= 1000000")]
    [Ensures("Result == d + 1")]
    public static int Warmer(int d)
    {
        Temperature t = new Temperature(d);
        return Read(t, 1);
    }
}
