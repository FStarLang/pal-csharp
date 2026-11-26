using System;
using System.Diagnostics;
using PalLang;

[assembly: IncludePulseFile("Handoff.fst")]

[SpecType("Class_Owner.class_Owner__model")]
public readonly struct HandoffModel<T> { }

public static class HandoffSpec
{
    [SpecOp("Handoff.inv")]
    public static SlProp Inv<T>([Plain] Owner<T> source, HandoffModel<T> model, Perm permission) =>
        throw new InvalidOperationException();

    [SpecOp("Handoff.window")]
    public static SlProp Window<T>([Plain] Owner<T> source, [Plain] Owner<T> alias, HandoffModel<T> model, Perm permission) =>
        throw new InvalidOperationException();
}

public static class HandoffProof
{
    [Lemma, Conditional("PAL"), GhostArg("Owner<T> source"), GhostArg("HandoffModel<T> model")]
    [Requires("HandoffSpec.Inv(source, model, permission)")]
    [Ensures("HandoffSpec.Inv(source, model, permission)")]
    public static void Inspect<T>(Ghost<Perm> permission) { }

    [Lemma, Conditional("PAL"), GhostArg("HandoffModel<T> model")]
    [Requires("HandoffSpec.Inv(source, model, permission)")]
    [Requires("ReferenceEquals(source, alias)")]
    [Ensures("HandoffSpec.Window(source, alias, model, permission)")]
    [PulseBody("Handoff.open_alias $(source) $(alias) $(model) $(permission)")]
    public static void OpenGhost<T>(Ghost<Owner<T>> source, [Plain] Owner<T> alias, Ghost<Perm> permission) { }

    [Lemma, Conditional("PAL"), GhostArg("HandoffModel<T> model")]
    [Requires("HandoffSpec.Inv(source, model, permission)")]
    [Ensures("HandoffSpec.Inv(source, model, permission)")]
    public static void Keep<T>(Ghost<Owner<T>> source, Ghost<Perm> permission) { }

    // A binding beside a checked lemma must not erase the lemma's module.
    [SpecOp("Handoff.identity")]
    public static bool Identity(bool b) => throw new InvalidOperationException();

    [Lemma, Conditional("PAL"), GhostArg("HandoffModel<T> model")]
    [Requires("HandoffSpec.Inv(source, model, permission)")]
    [Requires("ReferenceEquals(source, alias)")]
    [Ensures("HandoffSpec.Window(source, alias, model, permission)")]
    [PulseBody("Handoff.open_alias $(source) $(alias) $(model) $(permission)")]
    public static void Open<T>([Plain] Owner<T> source, [Plain] Owner<T> alias, Ghost<Perm> permission) { }
}
