using PalLang;

namespace PalCSharp.Tests;

/// <summary>
/// The §7.2 variant of <c>Counter</c>: the same object, written differently. The field is
/// renamed and read through an explicit <c>this.</c>, the mutator uses <c>++</c> instead
/// of <c>x = x + 1</c>, the reader is expression-bodied instead of using a
/// <c>return</c> statement, and the members are declared in the opposite order. If any of
/// these changes needed an emitter change, the emitter would be fitted to
/// <c>Counter.cs</c> rather than implementing the scheme.
/// </summary>
[Invariant("n >= 0")]
public sealed class Tally
{
    /// <summary>
    /// A read-only method (R4.11): expression-bodied, and reaching the field through an
    /// explicit receiver.
    /// </summary>
    [Ensures("Result == @this.Value")]
    public int Read() => this.n;

    /// <summary>
    /// A mutator written with <c>++</c>. Normalize desugars it to an assignment, so it
    /// reaches the emitter in exactly the shape <c>Counter.Increment</c> does.
    /// </summary>
    [Requires("@this.Value < 2147483647")]
    [Ensures("@this.Value == Old(@this.Value) + 1")]
    public void Bump()
    {
        this.n++;
    }

    [Spec]
    public SpecInt Value => Model;

    [Ensures("@this.Value == 0")]
    public Tally()
    {
        this.n = 0;
    }

    [Refine("Result >= 0")]
    [Model]
    private SpecInt Model => this.n;

    private int n;
}
