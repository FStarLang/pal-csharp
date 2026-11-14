using System;
using PalLang;

[assembly: IncludePulseFile("CallbackCells.fst")]

namespace PalCSharp.Tests;

[Plain]
public sealed class CallbackCell<T>
{
    public T item = default!;
}

[SpecType("Class_CallbackCell.class_CallbackCell__raw")]
public readonly struct CallbackSnapshot<T> { }

public static class CallbackCellSpec
{
    [SpecOp("CallbackCells.raw")]
    public static SlProp Raw<T>(CallbackCell<T> cell, CallbackSnapshot<T> snapshot, Perm permission) =>
        throw new InvalidOperationException();

    [SpecOp("CallbackCells.value")]
    public static T Value<T>(CallbackSnapshot<T> snapshot) => throw new InvalidOperationException();

    [SpecOp("CallbackCells.int_value")]
    public static SpecInt IntValue(CallbackSnapshot<int> snapshot) => throw new InvalidOperationException();
}

public static class CallbackCells
{
    [Lemma]
    [Requires("cell == expected")]
    [Ensures("cell == expected")]
    [PulseBody("()")]
    public static void Witness<T>(CallbackCell<T> cell, Ghost<CallbackCell<T>?> expected) { }

    [GhostArg("CallbackCell<T>? witness")]
    [Requires("cell == witness")]
    [Ensures("Result == witness")]
    public static CallbackCell<T> NamedWitness<T>(CallbackCell<T> cell)
    {
#if PAL
        Witness(cell, Pal.Ghost<CallbackCell<T>?>("witness"));
#endif
        return cell;
    }

    [GhostArg("CallbackSnapshot<T> Before"), GhostArg("Perm Permission")]
    [Preserves("CallbackCellSpec.Raw(cell, Before, Permission)")]
    [Requires("Pal.CallBound(action) > 0")]
    [Ensures("Pal.Trace<T, T>(action).Length == 1")]
    [Ensures("Pal.Same(Pal.Trace<T, T>(action)[0].Item1, CallbackCellSpec.Value(Before))")]
    [Ensures("Pal.Same(Pal.Trace<T, T>(action)[0].Item2, Result)")]
    public static T Visit<T>(CallbackCell<T> cell,
        [Callback("CallbackSnapshot<T> snapshot", "CallbackCellSpec.Raw(argument, snapshot, permission)",
                  "CallbackCellSpec.Value(snapshot)", Bounded = true)] Func<CallbackCell<T>, T> action)
    {
        return action(cell);
    }

    [GhostArg("CallbackSnapshot<T> Before"), GhostArg("Perm Permission")]
    [Preserves("CallbackCellSpec.Raw(cell, Before, Permission)")]
    [Ensures("Pal.Same(Result, CallbackCellSpec.Value(Before))")]
    public static T Read<T>(CallbackCell<T> cell)
    {
        return Visit(cell, node =>
        {
#if PAL
            Pal.Protocol<T, T>(trace => trace.Length == 0 ||
                trace.Length == 1 && Pal.Same(trace[0].Item1, trace[0].Item2), 1);
#endif
            return node.item;
        });
    }

    [GhostArg("CallbackSnapshot<int> Before"), GhostArg("Perm Permission")]
    [Preserves("CallbackCellSpec.Raw(cell, Before, Permission)")]
    [Ensures("Result == CallbackCellSpec.IntValue(Before)")]
    public static int ReadInt(CallbackCell<int> cell)
    {
        return Visit(cell, node =>
        {
#if PAL
            Pal.Protocol<int, int>(trace => trace.Length == 0 ||
                trace.Length == 1 && Pal.Same(trace[0].Item1, trace[0].Item2), 1);
#endif
            return node.item;
        });
    }
}
