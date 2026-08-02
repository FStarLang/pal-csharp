// EXPECT: PALCS0526
using PalLang;

namespace PalCSharp.Tests.Diagnostics;

/// <summary>
/// R4.10a. A contract is bound as the body of a static shim method, so a bare `this`
/// does not resolve; the receiver is a parameter and is written `@this`. This is the one
/// error every user hits once, so it gets its own message rather than Roslyn's, which
/// talks about a static method the user never wrote.
/// </summary>
[Spec]
public struct BareThisModel
{
    public SpecInt Value;
}

[Invariant("0 <= n")]
public sealed class BareThisCounter
{
    private int n;

    [Model]
    private BareThisModel Model => new BareThisModel { Value = n };

    [Spec]
    public SpecInt Value => Model.Value;

    [Ensures("Result == this.Value")]
    public int Get()
    {
        return n;
    }
}
