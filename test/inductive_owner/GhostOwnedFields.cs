using PalLang;
using System;

[assembly: IncludePulseFile("GhostOwnedFields.fst")]

namespace PalCSharp.Tests;

public static class GhostFieldSpecs
{
    [SpecOp("GhostOwnedFields.twice")]
    public static SpecInt Twice(SpecInt value) => throw new InvalidOperationException();
}

[Spec]
public struct GhostHolderModel
{
    public SpecInt First;
    public SpecInt Second;
}

public sealed class GhostFieldHolder
{
    private CellOwner child;
    private CurrentModelOwner other;

#if PAL
    [Model] private GhostHolderModel Model =>
        new GhostHolderModel { First = child.Value, Second = other.Value };
    [Spec] public SpecInt Value => Model.First;
    [Spec] public SpecInt Other => Model.Second;
    [Spec] public SpecInt Total => Model.First + Model.Second;
#endif

    [Ensures("@this.Value == first && @this.Other == second")]
    [Requires("0 <= second && second <= 100")]
    public GhostFieldHolder(int first, int second)
    {
        child = new CellOwner(first);
        other = new CurrentModelOwner(second);
    }

    [Ensures("Result == @this.Value")]
    public int ReadThroughLoan()
    {
        var alias = this;
        int result = child.Read();
#if PAL
        Ghost<SpecInt> value = child.Value;
        Ghost<SpecInt> second = other.Value;
        LeaseProof.Begin(value, Pal.Permission());
        // Capture the other field's current model, without closing child's loan.
        Pal.Assert(GhostFieldSpecs.Twice(other.Value) == GhostFieldSpecs.Twice(second.Value));
        Pal.Assert(Pal.Old(this.Value) == value.Value);
        LeaseProof.Keep(value.Value + other.Value - second.Value, Pal.Permission());
        LeaseProof.End(value, Pal.Permission());
        // Whole-receiver/nested observations must still have all dependencies.
        Pal.Assert(this.Total == value.Value + second.Value);
        Pal.Assert(alias.Total == value.Value + second.Value);
#endif
        return result;
    }

    [Ensures("Result == @this.Value")]
    public int ReadWithDistinctOwner(GhostFieldHolder distinct)
    {
        int result = child.Read();
#if PAL
        Ghost<SpecInt> value = child.Value;
        LeaseProof.Begin(value, Pal.Permission());
        // Same class, different compiler slot: retain its own ownership/model.
        Pal.Assert(distinct.Total == Pal.Old(distinct.Total));
        LeaseProof.End(value, Pal.Permission());
#endif
        return result;
    }
}
