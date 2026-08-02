using PalLang;

namespace PalCSharp.Tests;

/// <summary>
/// Using the stack from outside it. The storage is unreachable here — <c>items</c> is not
/// merely private by convention, it is behind <c>class_Stack__inv</c>, which this code
/// never unfolds — so everything these methods know comes from the observations applied
/// to the model.
/// </summary>
public static class StackUse
{
    /// <summary>
    /// R4.14 with a resource inside: the stack allocated here is dropped at the exit, and
    /// dropping it discards the array's <c>A.pts_to</c> along with it. That is sound
    /// precisely because the CLR collects both (F15), and it is why nothing here has to
    /// name the storage in order to be rid of it.
    /// </summary>
    [Ensures("Result == 7")]
    public static int PushThenPop()
    {
        Stack s = new Stack(4);
        s.Push(7);
        return s.Pop();
    }

    /// <summary>
    /// The precondition is arithmetic on the model, and it has to be: R4.11 makes the
    /// receiver's post-state model an existential after the first call, so the second
    /// call's precondition can only be re-established through what the first one promised.
    /// </summary>
    [Requires("@s.Count + 2 <= @s.Capacity")]
    [Ensures("@s.Capacity == Old(@s.Capacity)")]
    [Ensures("@s.Count == Old(@s.Count) + 2")]
    public static void PushTwo(Stack s, int a, int b)
    {
        s.Push(a);
        s.Push(b);
    }

    /// <summary>A read-only use: the model does not move, so the caller keeps its binder.</summary>
    [Ensures("Result == @s.Count")]
    public static int Depth(Stack s)
    {
        return s.Size();
    }
}
