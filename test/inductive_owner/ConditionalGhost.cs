using System;
using PalLang;

namespace PalCSharp.Tests;

[Invariant("value == OwnerSpec.Value(state)")]
public sealed class ConditionalGhostOwner
{
    private int value;
#if PAL
    private OwnerState state = OwnerSpec.Make(0);
#else
    [Spec]
    private ref OwnerState state => throw new InvalidOperationException("Specification only");
#endif

    [Model]
    private SpecInt Model => OwnerSpec.Value(state);

    [Spec]
    public SpecInt Value => Model;

    [Ensures("@this.Value == initial")]
    public ConditionalGhostOwner(int initial)
    {
        value = initial;
        Pal.UpdateGhost(ref state, OwnerSpec.Make(initial));
    }

    [Ensures("@this.Value == next")]
    public void Replace(int next)
    {
        Ghost<SpecInt> before = default;
        Pal.Capture(ref before, this.Value);
        OwnerState progress = default;
        Pal.UpdateGhost(ref progress, state);
        Pal.Assert(OwnerSpec.Value(progress) == before.Value);
        value = next;
        Pal.UpdateGhost(ref progress, OwnerSpec.Make(next));
        Pal.UpdateGhost(ref state, OwnerSpec.Make(next));
        Pal.Assert(OwnerSpec.Value(progress) == this.Value);
        Pal.Assert(before.Value == Pal.Old(this.Value));
    }

    [Ensures("Result == @this.Value")]
    public int Read() => value;
}
