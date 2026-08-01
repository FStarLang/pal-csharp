using PalLang;

namespace PalCSharp.Tests;

/// <summary>
/// Using an object from outside it — the half of the scheme that
/// <c>test/counter_class</c> cannot show, because there every specification is written
/// against the object's own fields.
///
/// Here the object is opaque. Each method holds <c>class_Counter__inv c m</c> and never
/// unfolds it; everything it can say about <c>c</c> comes from the <c>[Spec]</c> member
/// <c>Value</c> applied to the model. That is the point of R3.9/R3.10: the client
/// reasons about an abstraction, and the representation is not merely private by
/// convention but unreachable.
/// </summary>
public static class CounterUse
{
    /// <summary>
    /// R4.11 in the negative. Calling a mutator makes the receiver's post-state model an
    /// existential, so this method cannot promise the caller the model it was given —
    /// only how the new one relates to the old. The two calls compose because the
    /// precondition is strong enough to re-establish <c>Increment</c>'s own precondition
    /// after the first one.
    /// </summary>
    [Requires("@c.Value < 2147483646")]
    [Ensures("@c.Value == Old(@c.Value) + 2")]
    public static void TwiceUp(Counter c)
    {
        c.Increment();
        c.Increment();
    }

    /// <summary>
    /// R4.11 in the positive. Only read-only methods are called, so the model does not
    /// move and the caller keeps the binder it came in with — which is what makes the
    /// postcondition provable without an existential to reconcile.
    /// </summary>
    [Ensures("Result == @c.Value")]
    public static int Peek(Counter c)
    {
        return c.Get();
    }

    /// <summary>
    /// R4.12 from the caller's side. The constructor's postcondition is all this method
    /// knows about the object, and it is enough: the invariant it returns is owned here,
    /// and freshness comes free from the frame rule (F15).
    /// </summary>
    [Ensures("Result == 0")]
    public static int FreshIsZero()
    {
        Counter c = new Counter();
        return c.Get();
    }
}
