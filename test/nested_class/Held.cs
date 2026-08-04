using PalLang;

namespace PalCSharp.Tests;

/// <summary>
/// R4.12b. An owner that does not build its sub-object but is <em>handed</em> one. A
/// constructor body may only initialise fields, so an object parameter it stores is
/// necessarily given away: the argument's invariant leaves the caller and becomes part of
/// the new object's. So a constructor consumes every object parameter, and no annotation
/// says so — the rule reads it off the shape of a constructor.
///
/// <para>This was <c>test/pulse_refusals/cases/OwnershipTransfer.cs</c> until R4.12b was
/// written. The refusal was real: without the rule, the constructor's <c>fold</c> consumed
/// <c>given</c>'s invariant and R4.10's postcondition owed the same invariant back to the
/// caller, so one resource had two claimants and Pulse said so. R4.12b removes the second
/// claimant rather than adding a proof step, which is why the case moved here instead of
/// being annotated into submission.</para>
/// </summary>
[Invariant("0 <= inner.N")]
public sealed class Held
{
    private Counter inner;

    [Model]
    private CounterModel Model => inner.State;

    [Spec]
    public SpecInt N => Model.N;

    [Ensures("@this.N == Old(given.N)")]
    public Held(Counter given)
    {
        inner = given;
    }

    [Requires("@this.N < 2147483647")]
    [Ensures("@this.N == Old(@this.N) + 1")]
    public void Bump()
    {
        inner.Bump();
    }

    [Ensures("Result == @this.N")]
    public int Inspect()
    {
        return inner.Value();
    }
}
