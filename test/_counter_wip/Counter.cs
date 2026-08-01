using PalLang;

namespace PalCSharp.Tests;

/// <summary>
/// The walking skeleton for the object system: the smallest class that exercises every
/// part of the scheme in <c>doc/translation.md</c> §3.4 and §4.5 — a representation, a
/// user-declared ghost model, an abstraction function, observations that are functions of
/// the model, an invariant, a constructor, a mutator and a read-only method.
///
/// There is no array here on purpose. <c>test/stack_class</c> is the test that shows a
/// class owning its storage, which is the thing a struct cannot do (PALCS0511); this one
/// isolates the object machinery from the ownership machinery so that a failure in either
/// is unambiguous.
/// </summary>
[Invariant("count >= 0")]
public sealed class Counter
{
    private int count;

    /// <summary>
    /// The abstraction function (R3.9). Its return type <em>is</em> the model type, so the
    /// model of a <c>Counter</c> is a mathematical integer — chosen here, not derived by
    /// the compiler. This is the one member allowed to read <c>count</c>, and it is
    /// <c>private</c> because only the object's own invariant consumes it (R4.10b).
    /// </summary>
    [Model]
    private SpecInt Model => count;

    /// <summary>
    /// An observation (R3.9c): a pure function of the model, never of the representation.
    /// It is <c>public</c> because contracts naming it are compiled outside the class.
    /// </summary>
    [Spec]
    public SpecInt Value => Model;

    /// <summary>
    /// The constructor constrains the <em>initial model</em> (R4.12). Without the
    /// <c>[Ensures]</c> a caller would learn only that the object is well formed, which is
    /// the weak-specification failure the whole scheme exists to avoid.
    /// </summary>
    [Ensures("@this.Value == 0")]
    public Counter()
    {
        count = 0;
    }

    /// <summary>
    /// A mutator. The receiver is spelled <c>@this</c> (R4.10a) because a spec string is
    /// compiled as the body of a static method, where a bare <c>this</c> is a C# error.
    /// The postcondition relates the new model to the old one — which is exactly what an
    /// un-indexed invariant could never express.
    /// </summary>
    [Requires("@this.Value < 2147483647")]
    [Ensures("@this.Value == Old(@this.Value) + 1")]
    public void Increment()
    {
        count = count + 1;
    }

    /// <summary>
    /// A read-only method: it assigns no field, so its contract collapses to
    /// <c>preserves</c> (R4.11).
    /// </summary>
    [Ensures("Result == @this.Value")]
    public int Get()
    {
        return count;
    }
}
