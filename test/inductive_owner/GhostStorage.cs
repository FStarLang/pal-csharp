using System;
using PalLang;

[assembly: IncludePulseFile("GhostStorageState.fst")]
[assembly: IncludePulseFile("GhostStoragePlain.fst")]
namespace PalCSharp.Tests;

[SpecType("GhostStorageState.state")]
public readonly struct GhostStorageState<T> { }

[SpecType("GhostStorageState.model")]
public readonly struct GhostStorageModel<T> { }

public static class GhostStorageSpec
{
    [SpecOp("GhostStorageState.make")]
    public static GhostStorageState<T> Make<T>(int value) => throw new InvalidOperationException();
    [SpecOp("GhostStorageState.value")]
    public static SpecInt Value<T>(GhostStorageState<T> state) => throw new InvalidOperationException();
    [SpecOp("GhostStorageState.observe")]
    public static GhostStorageModel<T> Observe<T>(GhostStorageState<T> state) => throw new InvalidOperationException();
    [SpecOp("GhostStorageState.model_value")]
    public static SpecInt ModelValue<T>(GhostStorageModel<T> value) => throw new InvalidOperationException();
}

public class GhostStorageOwner<T>
{
    private int runtimeValue;

    [GhostField("GhostStorageSpec.Make<T>(0)")]
    private ref GhostStorageState<T> state => throw new InvalidOperationException("Specification only");

    [Model] private GhostStorageModel<T> Model => GhostStorageSpec.Observe(state);
    [Spec] public SpecInt Value => GhostStorageSpec.ModelValue(Model);

    [Ensures("@this.Value == initial")]
    public GhostStorageOwner(int initial)
    {
        Pal.Assert(GhostStorageSpec.Value(state) == 0);
        runtimeValue = initial;
        Pal.UpdateGhost(ref state, GhostStorageSpec.Make<T>(initial));
    }

    [Ensures("@this.Value == 7")]
    public GhostStorageOwner() : this(7)
    {
        Pal.Assert(GhostStorageSpec.Value(state) == 7);
    }

    // A ghost-only write MUST be classified as mutating the model.
    [Ensures("@this.Value == next")]
    public void AdvanceProof(int next)
    {
        Ghost<SpecInt> before = default;
        Pal.Capture(ref before, GhostStorageSpec.Value(state));
        Pal.UpdateGhost(ref this.state, GhostStorageSpec.Make<T>(next));
        Pal.Assert(before.Value == Pal.Old(this.Value));
    }

    [Ensures("@this.Value == next")]
    public void ViaAlias(int next)
    {
        GhostStorageOwner<T> alias = this;
        Pal.UpdateGhost(ref alias.state, GhostStorageSpec.Make<T>(next));
        Pal.Assert(GhostStorageSpec.Value(state) == next);
    }

    public int Read() => runtimeValue;
}

public sealed class GhostStorageDerived<T> : GhostStorageOwner<T>
{
    [Ensures("@this.Value == 7")]
    public GhostStorageDerived() : base() { }
}

[Plain]
public sealed class GhostStoragePlain
{
    [GhostField("OwnerSpec.Make(0)")]
    public ref OwnerState State { get { throw new InvalidOperationException("Specification only"); } }

    [Ensures("GhostStoragePlainSpec.Zero(Result)")]
    public GhostStoragePlain() { }
}

public static class GhostStoragePlainSpec
{
    [SpecOp("GhostStoragePlain.zero")]
    public static SlProp Zero(GhostStoragePlain value) => throw new InvalidOperationException();
}
