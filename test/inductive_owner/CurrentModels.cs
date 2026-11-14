using PalLang;

namespace PalCSharp.Tests;

[Invariant("OwnerSpec.Holds(cell, cached, Pal.Permission())")]
public sealed class CurrentModelOwner
{
    private OwnedCell cell;
    private int cached;

    [Model]
    [Refine("0 <= Result && Result <= 100")]
    private SpecInt Model => cached;
    [Spec] public SpecInt Value => Model;

    [Requires("0 <= value && value <= 100")]
    [Ensures("@this.Value == value")]
    public CurrentModelOwner(int value)
    {
        cell = MakeCell(value);
        cached = value;
    }

    [Ensures("OwnerSpec.Holds(Result, value, Perm.Full)")]
    private static OwnedCell MakeCell(int value)
    {
        var cell = new OwnedCell(value);
        OwnerProof.Close(cell, value);
        return cell;
    }

    [Requires("@this.Value > 0")]
    [Ensures("@this.Value == Pal.Old(@this.Value) - 1")]
    public void Step()
    {
        OwnerProof.Open(cell, cached);
        cell.value = cached - 1;
        cached--;
        OwnerProof.Close(cell, cached);
    }

    [Ensures("@this.Value == 0 && Result == Pal.Old(@this.Value)")]
    public int Drain()
    {
        int completed = 0;
        while (cached > 0)
        {
            Pal.Invariant(OwnerSpec.Holds(cell, cached, Perm.Full));
            Pal.Invariant(0 <= completed && completed + this.Value == Pal.Old(this.Value));
            Pal.Decreases(this.Value);
            Step();
            completed++;
            Pal.Assert(this.Value == Pal.Old(this.Value) - completed);
        }
        return completed;
    }

    [Requires("@this.Value > 0")]
    [Ensures("Result == Pal.Old(@this.Value) - 1 && @this.Value == Result")]
    public int StepThenCount()
    {
        Step();
        int completed = 0;
        while (completed < cached)
        {
            Pal.Invariant(OwnerSpec.Holds(cell, cached, Perm.Full));
            Pal.Invariant(this.Value == Pal.Old(this.Value) - 1);
            Pal.Invariant(0 <= completed && completed <= this.Value);
            Pal.Decreases(this.Value - completed);
            completed++;
        }
        return completed;
    }
}
