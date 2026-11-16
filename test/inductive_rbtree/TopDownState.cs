using System;
using PalLang;

[assembly: IncludePulseFile("InductiveState.fst")]

namespace PalCSharp.Tests.Inductive;

[SpecType("InductiveState.state")]
public readonly struct RbState<T> { }

public static class RbState
{
    private static Exception Ghost() => new InvalidOperationException("Specification only");
    [SpecOp("InductiveState.labels")]
    public static RbLabels<T> Labels<T>(RbState<T> state) => throw Ghost();
    [SpecOp("InductiveState.start")]
    public static RbState<T> Start<T>(Ghost<RbLabels<T>> nodes) => throw Ghost();
    [SpecOp("InductiveState.recolor")]
    public static RbState<T> Recolor<T>(RbState<T> state, RbNode<T>? node, bool red) => throw Ghost();
    [SpecOp("InductiveState.split")]
    public static RbState<T> Split<T>(RbState<T> state, RbNode<T> node) => throw Ghost();
    [SpecOp("InductiveState.balance")]
    public static RbState<T> Balance<T>(RbState<T> state, RbNode<T> node) => throw Ghost();
    [SpecOp("InductiveState.black")]
    public static RbState<T> Black<T>(RbState<T> state) => throw Ghost();
    [SpecOp("InductiveState.link")]
    public static RbState<T> Link<T>(RbState<T> state, RbNode<T> parent, RbNode<T> node, T key, bool right) => throw Ghost();
}
