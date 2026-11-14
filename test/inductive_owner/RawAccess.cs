#if PAL
using System;
using PalLang;
[assembly: IncludePulseFile("RawAccess.fst")]
namespace PalCSharp.Tests;

[SpecType("Class_RawOwner.class_RawOwner__raw")]
public readonly struct RawSnapshot { }

public static class RawSpec
{
    [SpecOp("RawAccess.raw")]
    public static SlProp Raw([Plain] RawOwner? owner, RawSnapshot snapshot, Perm permission) =>
        throw new InvalidOperationException();
    [SpecOp("RawAccess.value")]
    public static int Value(RawSnapshot snapshot) => throw new InvalidOperationException();
    [SpecOp("RawAccess.with_value")]
    public static RawSnapshot WithValue(RawSnapshot snapshot, int value) => throw new InvalidOperationException();
    [SpecOp("RawAccess.with_state")]
    public static RawSnapshot WithState(RawSnapshot snapshot, RetainedPayload payload) =>
        throw new InvalidOperationException();
    [SpecOp("RawAccess.half")]
    public static Perm Half() => throw new InvalidOperationException();
}

public sealed class RawOwner
{
    private int value;
    private RetainedState state;
    [Model] private int Model => value;
    [Spec] public int Value => Model;

    public RawOwner(int initial)
    {
        value = initial;
        state = RetainedSpec.Empty();
    }

    [GhostArg("RawSnapshot before"), GhostArg("Perm permission")]
    [Requires("RawSpec.Raw(owner, before, permission)")]
    [Ensures("RawSpec.Raw(owner, before, permission)")]
    [Ensures("Result == RawSpec.Value(before)")]
    public static int Load([Plain] RawOwner owner) => owner.value;

    [GhostArg("RawSnapshot before")]
    [Requires("RawSpec.Raw(owner, before, RawSpec.Half())")]
    [Ensures("RawSpec.Raw(owner, before, RawSpec.Half())")]
    [Ensures("Result == RawSpec.Value(before)")]
    public static int NullableLoad([Plain] RawOwner? owner) => owner!.value;

    [GhostArg("RawSnapshot before")]
    [Requires("RawSpec.Raw(owner, before, Perm.Full)")]
    [Ensures("RawSpec.Raw(owner, RawSpec.WithValue(before, next), Perm.Full)")]
    public static void Store([Plain] RawOwner owner, int next)
    {
        owner.value = next;
    }

    [GhostArg("RawSnapshot before")]
    [Requires("RawSpec.Raw(other, before, Perm.Full)")]
    [Ensures("RawSpec.Raw(other, RawSpec.WithValue(before, next), Perm.Full)")]
    [Ensures("Result == next")]
    public static int CellStore([Plain] RawOwner owner, [Plain] RawOwner other, int next)
    {
        owner = other;
        owner.value = next;
        return owner.value;
    }

    [GhostArg("RawSnapshot before")]
    [Requires("RawSpec.Raw(owner, before, Perm.Full)")]
    [Ensures("RawSpec.Raw(owner, RawSpec.WithState(before, payload), Perm.Full)")]
    public static void Commit([Plain] RawOwner owner, Ghost<RetainedPayload> payload)
    {
        owner.state = RetainedSpec.State(payload.Value);
    }
}
#endif
