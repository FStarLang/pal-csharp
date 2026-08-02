using PalLang;

namespace PalCSharp.Tests;

[Spec]
public struct CounterModel
{
    public SpecInt N;
}

/// <summary>The inner object. It knows nothing about being owned.</summary>
[Invariant("0 <= k")]
public sealed class Counter
{
    private int k;

    [Refine("0 <= Result.N && Result.N <= 2147483647")]
    [Model]
    private CounterModel Model => new CounterModel { N = k };

    [Spec]
    public SpecInt N => Model.N;

    /// <summary>
    /// R3.10b. How an owner names a sub-object's whole model. A `[Spec]` member returning
    /// the model type is the ordinary mechanism doing an extra job: in a specification the
    /// field `lo` denotes `model_lo`, so `lo.State` is `spec_Counter_State model_lo`, which
    /// is that model. No new annotation was needed for composition.
    /// </summary>
    [Spec]
    public CounterModel State => Model;

    [Requires("0 <= start")]
    [Ensures("@this.N == start")]
    public Counter(int start)
    {
        k = start;
    }

    [Requires("@this.N < 2147483647")]
    [Ensures("@this.N == Old(@this.N) + 1")]
    public void Bump()
    {
        k = k + 1;
    }

    [Ensures("Result == @this.N")]
    public int Value()
    {
        return k;
    }
}
