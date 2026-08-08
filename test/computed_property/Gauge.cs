// R9.20. A computed property is the method its getter is: one module `Func_C_P`, the
// contract read from the property declaration -- C# does not permit an attribute on an
// accessor, so the property is the only place it can go -- and the body lowered by the
// ordinary rules. Both accessor forms appear here, `=> e` and `get { ... }`, because they
// are the same declaration written differently and must produce the same Pulse.
//
// The point of the rule is that nothing else in §9 changes. A getter is a nullary instance
// method, so R9.7's frame opens the representation exactly as it does for `Width()` below,
// and R9.20a makes a read `g.Span` the call `g.Span()` -- which is why `Width()` can
// return `Span` and `Reader.Read` can read it from outside the class.
using PalLang;

namespace Instruments;

/// <summary>
/// The model: a spec-only struct (R3.9a), so a caller can name the endpoints separately.
/// </summary>
[Spec]
public struct Bounds
{
    public SpecInt Lo;
    public SpecInt Hi;
}

[Invariant("low <= high")]
[Invariant("high - low <= 2147483647")]
public sealed class Gauge
{
    private int low;
    private int high;

    [Model]
    private Bounds Model => new Bounds { Lo = low, Hi = high };

    [Spec]
    public SpecInt Lo => Model.Lo;

    [Spec]
    public SpecInt Hi => Model.Hi;

    [Requires("lo <= hi")]
    [Requires("hi - lo <= 2147483647")]
    [Ensures("@this.Lo == lo")]
    [Ensures("@this.Hi == hi")]
    public Gauge(int lo, int hi)
    {
        this.low = lo;
        this.high = hi;
    }

    /// <summary>The expression-bodied form.</summary>
    [Ensures("Result == @this.Hi - @this.Lo")]
    public int Span => high - low;

    /// <summary>The block-bodied form. Same declaration, same output.</summary>
    [Ensures("Result == @this.Lo + @this.Hi")]
    [Requires("-2147483648 <= @this.Lo + @this.Hi && @this.Lo + @this.Hi <= 2147483647")]
    public int Total { get { return low + high; } }

    /// <summary>
    /// R9.20a inside the class: `Span` here is the call `Span()`, and the receiver is the
    /// `this` the frontend synthesised for `Width` itself.
    /// </summary>
    [Ensures("Result == @this.Hi - @this.Lo")]
    public int Width()
    {
        return Span;
    }

    /// <summary>
    /// A property read in a condition is a call in a condition; R6.3 is unchanged, and
    /// R4.10c keeps the invariant folded because this body names no field either.
    /// </summary>
    [Ensures("k < 0 || Result == 1")]
    [Ensures("k >= 0 || Result == 0")]
    public int AtLeast(int k)
    {
        if (k >= 0)
        {
            int unused = Span;
            return 1;
        }
        return 0;
    }
}

public static class Reader
{
    /// <summary>
    /// R9.20a from outside the class: a client reads the property exactly as it would call
    /// the method, and gets the same Pulse.
    /// </summary>
    [Ensures("Result == @g.Hi - @g.Lo")]
    public static int Read(Gauge g)
    {
        return g.Span;
    }

    /// <summary>
    /// Two reads of a read-only property leave the model where it was, so the second read
    /// still satisfies the first's postcondition: R4.11 classifies a getter like any other
    /// method, from its body.
    ///
    /// Both bounds are preconditions because a *client* cannot see the class invariant:
    /// `[Invariant("low <= high")]` is stated over the representation, and a caller holds
    /// the model. That is R3.9d read from outside — a fact a client needs is a fact the
    /// model must carry — and §0 rule 3 says the fix goes here, in the annotation.
    /// </summary>
    [Requires("@g.Lo <= @g.Hi")]
    [Requires("2 * (@g.Hi - @g.Lo) <= 2147483647")]
    [Ensures("Result == 2 * (@g.Hi - @g.Lo)")]
    public static int Twice(Gauge g)
    {
        int a = g.Span;
        int b = g.Span;
        return a + b;
    }
}
