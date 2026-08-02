// EXPECT: PALCS0525
using PalLang;

namespace PalCSharp.Tests.Diagnostics;

/// <summary>
/// R4.10b. The shim lives in its own namespace, so a contract sees exactly what a client
/// sees. `Value` is a perfectly good `[Spec]` observation, but it is private, so no caller
/// could state this postcondition — and the diagnostic says so at the point of use rather
/// than letting the contract bind against an abstraction nobody else can name.
/// </summary>
[Spec]
public struct PrivateSpecModel
{
    public SpecInt Value;
}

[Invariant("0 <= n")]
public sealed class PrivateSpecCounter
{
    private int n;

    [Model]
    private PrivateSpecModel Model => new PrivateSpecModel { Value = n };

    [Spec]
    private SpecInt Value => Model.Value;

    [Ensures("Result == @this.Value")]
    public int Get()
    {
        return n;
    }
}
