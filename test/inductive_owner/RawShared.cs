#if PAL
using System;
using PalLang;
[assembly: IncludePulseFile("RawShared.fst")]
namespace PalCSharp.Tests;

[SpecType("Class_RawGeneric.class_RawGeneric__raw")]
public readonly struct RawGenericSnapshot<A, B> { }

public static class RawSharedSpec
{
    [SpecOp("RawShared.raw")]
    public static SlProp Raw<A, B>([Plain] RawReverse<B, A> owner, RawGenericSnapshot<A, B> before,
        Perm permission) => throw new InvalidOperationException();
    [SpecOp("RawShared.value")]
    public static A Value<A, B>(RawGenericSnapshot<A, B> before) => throw new InvalidOperationException();
    [SpecOp("RawShared.with_value")]
    public static RawGenericSnapshot<A, B> WithValue<A, B>(RawGenericSnapshot<A, B> before, A value) =>
        throw new InvalidOperationException();
}

public class RawGeneric<A, B>
{
    private A value = default!;
    private B marker = default!;
    [Model] private (A, B) Model => (value, marker);

    [GhostArg("RawGenericSnapshot<A, B> before"), GhostArg("Perm permission")]
    [Requires("RawSharedSpec.Raw(owner, before, permission)")]
    [Ensures("RawSharedSpec.Raw(owner, before, permission)")]
    [Ensures("Pal.Same(Result, RawSharedSpec.Value(before))")]
    public static A Load([Plain] RawReverse<B, A> owner) => owner.value;

    [GhostArg("RawGenericSnapshot<A, B> before")]
    [Requires("RawSharedSpec.Raw(owner, before, Perm.Full)")]
    [Ensures("RawSharedSpec.Raw(owner, RawSharedSpec.WithValue(before, next), Perm.Full)")]
    public static void Store([Plain] RawReverse<B, A> owner, A next)
    {
        owner.value = next;
    }
}

// Reversed type arguments make normalization of the instantiated representation
// observable: RawReverse<B,A> owns a RawGeneric<A,B> record, not RawGeneric<B,A>.
public sealed class RawReverse<X, Y> : RawGeneric<Y, X> { }
#endif
