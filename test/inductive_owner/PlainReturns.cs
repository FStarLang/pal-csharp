using System;
using System.Diagnostics;
using PalLang;

[assembly: IncludePulseFile("PlainReturns.fst")]

namespace PalCSharp.Tests;

public static class PlainReturnSpec
{
    [SpecOp("PlainReturns.held")]
    public static SlProp Held<T>(CallbackCell<T>? cell, CallbackSnapshot<T> snapshot) =>
        throw new InvalidOperationException();
}

public static class PlainReturnProof
{
    [Lemma, Conditional("PAL")]
    [Requires("PlainReturnSpec.Held(old, snapshot)")]
    [Requires("old == cell")]
    [Ensures("PlainReturnSpec.Held(cell, snapshot)")]
    [PulseBody("PlainReturns.reindex $(old) $(cell) $(snapshot)")]
    public static void Reindex<T>(CallbackCell<T>? old, CallbackCell<T>? cell,
        Ghost<CallbackSnapshot<T>> snapshot) { }
}

public static class PlainReturns
{
    [Requires("calls < int.MaxValue")]
    [Ensures("Result == cell && calls == Pal.Old(calls) + 1")]
    [Requires("PlainReturnSpec.Held(cell, snapshot)")]
    [Ensures("PlainReturnSpec.Held(Result, snapshot)")]
    public static CallbackCell<T>? Observe<T>(CallbackCell<T>? cell,
        ref int calls, Ghost<CallbackSnapshot<T>> snapshot = default)
    {
        calls++;
        return cell;
    }

    [Requires("calls < int.MaxValue")]
    [Requires("PlainReturnSpec.Held(cell, snapshot)")]
    [Ensures("Result == cell && calls == Pal.Old(calls) + 1")]
    [Ensures("PlainReturnSpec.Held(Result, snapshot)")]
    public static CallbackCell<T>? Nullable<T>(CallbackCell<T>? cell,
        ref int calls, Ghost<CallbackSnapshot<T>> snapshot)
    {
        var cleanup = new PlainCleanupOwner();
        CallbackCell<T>? result = Observe(cell, ref calls);
        return result;
    }

    [Requires("calls < int.MaxValue")]
    [Requires("PlainReturnSpec.Held(cell, snapshot)")]
    [Ensures("Result == cell && calls == Pal.Old(calls) + 1")]
    [Ensures("PlainReturnSpec.Held(Result, snapshot)")]
    public static CallbackCell<T> NonNull<T>(CallbackCell<T> cell,
        ref int calls, Ghost<CallbackSnapshot<T>> snapshot)
    {
        var cleanup = new PlainCleanupOwner();
        CallbackCell<T> result = PlainTuples.Observe(cell, ref calls);
        PlainReturnProof.Reindex(cell, result, snapshot);
        return result;
    }

    [Requires("calls < int.MaxValue")]
    [Requires("PlainReturnSpec.Held(cell, snapshot)")]
    [Ensures("Result == cell && calls == Pal.Old(calls) + 1")]
    [Ensures("PlainReturnSpec.Held(Result, snapshot)")]
    public static CallbackCell<T>? EffectfulReturn<T>(CallbackCell<T>? cell,
        ref int calls, Ghost<CallbackSnapshot<T>> snapshot)
    {
        var cleanup = new PlainCleanupOwner();
        return Observe(cell, ref calls);
    }
}
