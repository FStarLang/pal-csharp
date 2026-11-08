// EXPECT: PALCS0001
using PalLang;

namespace PalCSharp.Tests.Diagnostics;

[Spec]
public struct NestedModel
{
    public SpecInt Value;
}

[Invariant("0 <= n")]
public sealed class NestedCell
{
    private int n;

    [Model]
    private NestedModel Model => new NestedModel { Value = n };

    [Spec]
    public SpecInt Value => Model.Value;

    [Ensures("@this.Value == 0")]
    public NestedCell()
    {
        n = 0;
    }

    [Ensures("Result == @this.Value")]
    public int Get()
    {
        return n;
    }
}

/// <summary>
/// F19. The object is abandoned inside the <c>if</c>, so R4.14's discard lands where the
/// block closes — and a block in statement position has no postcondition of its own, so
/// Pulse is still solving for one and cannot open the object's model existential.
/// Refusing is the honest answer; the same allocation in a branch that <em>returns</em>
/// is fine, because then the block's postcondition is the method's.
/// </summary>
public static class NestedUse
{
    [Ensures("Result == 42")]
    public static int AbandonedInABlock(bool b)
    {
        int answer = 42;
        if (b)
        {
            NestedCell c = new NestedCell();
            c.Get();
        }
        return answer;
    }
}
