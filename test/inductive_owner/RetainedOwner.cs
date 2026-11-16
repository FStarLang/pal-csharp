#if PAL
using System;
using System.Diagnostics;
using PalLang;
[assembly: IncludePulseFile("RetainedOwner.fst")]
namespace PalCSharp.Tests;

[SpecType("RetainedOwner.payload")]
public readonly struct RetainedPayload { }
[SpecType("RetainedOwner.state")]
public readonly struct RetainedState { }

public static class RetainedSpec
{
    [SpecOp("RetainedOwner.empty")]
    public static RetainedState Empty() => throw new InvalidOperationException();
    [SpecOp("RetainedOwner.full")]
    public static SlProp Held(RetainedPayload payload) => throw new InvalidOperationException();
    [SpecOp("RetainedOwner.value")]
    public static SpecInt Value(RetainedPayload payload) => throw new InvalidOperationException();
    [SpecOp("RetainedOwner.of_payload")]
    public static RetainedState State(RetainedPayload payload) => throw new InvalidOperationException();
    [SpecOp("RetainedOwner.state_held")]
    public static SlProp StateHeld(RetainedState state, Perm permission) => throw new InvalidOperationException();
    [SpecOp("RetainedOwner.state_value")]
    public static SpecInt StateValue(RetainedState state) => throw new InvalidOperationException();
    [SpecOp("RetainedOwner.model_value")]
    public static SpecInt ModelValue(CellOwner owner) => throw new InvalidOperationException();
    [SpecOp("RetainedOwner.pair")]
    public static RetainedPayload Pair([Plain] CellOwner owner, SpecInt value) => throw new InvalidOperationException();
    [SpecOp("RetainedOwner.describes")]
    public static bool Describes(RetainedPayload payload, [Plain] CellOwner owner, SpecInt value) =>
        throw new InvalidOperationException();
}

public static class RetainedProof
{
    [Lemma, GhostArg("SpecInt model"), Requires("LeaseSpec.Inv(owner, model, Perm.Full)")]
    [Requires("model == value")]
    [Ensures("RetainedSpec.Held(Result)")]
    [Ensures("RetainedSpec.Value(Result) == value")]
    [PulseBody("RetainedOwner.retain $(owner) $(model)")]
    public static Ghost<RetainedPayload> Retain([Plain, Consumes] CellOwner owner, Ghost<SpecInt> value) =>
        throw new InvalidOperationException();

    [Lemma, Conditional("PAL"), GhostArg("SpecInt model"), Requires("LeaseSpec.Inv(owner, model, Perm.Full)")]
    [Requires("model == value")]
    [Requires("RetainedSpec.Describes(payload, owner, value)")]
    [Ensures("RetainedSpec.Held(payload)")]
    [PulseBody("RetainedOwner.retain_void $(owner) $(model) $(payload)")]
    public static void RetainVoid([Plain, Consumes] CellOwner owner, Ghost<SpecInt> value,
        Ghost<RetainedPayload> payload) { }
}

[Invariant("RetainedSpec.StateHeld(payload, Pal.Permission())")]
public sealed class RetainingHolder
{
    private RetainedState payload;
    [Model] private SpecInt Model => RetainedSpec.StateValue(payload);
    [Spec] public SpecInt Value => Model;

    [Ensures("@this.Value == Pal.Old(owner.Value)")]
    public RetainingHolder([Consumes] CellOwner owner)
    {
        payload = RetainedSpec.Empty();
        var alias = owner;
        Ghost<SpecInt> value = alias.Value;
        Pal.Assert(RetainedSpec.ModelValue(alias) == value.Value);
        Ghost<RetainedPayload> retained = RetainedProof.Retain(alias, value);
        payload = RetainedSpec.State(retained.Value);
        Pal.Assert(this.Value == Pal.Old(owner.Value));
    }
    [Ensures("@this.Value == initial")]
    public RetainingHolder(int initial)
    {
        payload = RetainedSpec.Empty();
        var owner = new CellOwner(initial);
        var alias = owner;
        Ghost<SpecInt> value = alias.Value;
        Pal.Assert(RetainedSpec.ModelValue(alias) == value.Value);
        Ghost<RetainedPayload> retained = RetainedSpec.Pair(alias, value.Value);
        RetainedProof.RetainVoid(alias, value, retained);
        payload = RetainedSpec.State(retained.Value);
    }
}
#endif
