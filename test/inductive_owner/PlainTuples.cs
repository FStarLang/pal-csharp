using PalLang;

namespace PalCSharp.Tests;

public static class PlainTuples
{
    [Ensures("Result.Item1 == first && Result.Item2 == second")]
    public static (CallbackCell<T>, CallbackCell<T>) Pair<T>(
        CallbackCell<T> first, CallbackCell<T> second) => (first, second);

    [Ensures("Result.Item1 == first && Result.Item2 == second")]
    public static (CallbackCell<T>?, CallbackCell<T>?) NullablePair<T>(
        CallbackCell<T>? first, CallbackCell<T>? second) => (first, second);

    [Ensures("Result.Item1 == null && Result.Item2 == null")]
    public static (CallbackCell<T>?, CallbackCell<T>?) Empty<T>() => default;

    [Requires("calls < int.MaxValue")]
    [Ensures("Result == cell && calls == Pal.Old(calls) + 1")]
    public static CallbackCell<T> Observe<T>(CallbackCell<T> cell, ref int calls)
    {
        calls++;
        return cell;
    }

    [Requires("calls < int.MaxValue")]
    [Ensures("Result == first && calls == Pal.Old(calls) + 1")]
    public static CallbackCell<T> RoundTrip<T>(
        CallbackCell<T> first, CallbackCell<T> second, ref int calls)
    {
        var pair = (Observe(first, ref calls), second);
        return pair.Item1;
    }

    [Requires("entries.Length > 0 && entries[0].Item1 == cell")]
    [Ensures("Result == entries[0].Item1")]
    public static CallbackCell<T>? GhostSequence<T>(CallbackCell<T>? cell,
        Ghost<Seq<(CallbackCell<T>?, CallbackCell<T>)>> entries) => cell;
}
