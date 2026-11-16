using PalLang;

[assembly: IncludePulseFile("PlainLocals.fst")]

namespace PalCSharp.Tests;

public static class PlainLocals
{
    [Requires("calls < int.MaxValue")]
    [Ensures("calls == Pal.Old(calls) + 1")]
    [Ensures("Result == cell")]
    public static OwnedCell? Observe(OwnedCell? cell, ref int calls)
    {
        ++calls;
        return cell;
    }

    [Ensures("Result")]
    public static bool RequirePresent(OwnedCell cell)
    {
        return cell != null;
    }

    [Requires("calls < int.MaxValue")]
    [Ensures("calls == Pal.Old(calls) + 1")]
    [Ensures("Result == (replacement != null)")]
    public static bool NullTests(OwnedCell cell, OwnedCell? replacement, ref int calls)
    {
        cell = Observe(replacement, ref calls)!;
        if (null == cell)
            return false;
        bool present = cell != null && null != cell;
        return present && RequirePresent(cell!);
    }

    [Requires("calls < int.MaxValue")]
    [Ensures("calls == Pal.Old(calls) + 1")]
    [Ensures("OwnerSpec.Raw(Result, PlainLocalSpec.Snapshot(value), Perm.Full)")]
    public static OwnedCell Make(ref int calls, int value)
    {
        ++calls;
        OwnedCell result = new OwnedCell(value);
        PlainLocalProof.Canonical(result, value);
        return result;
    }

    [Requires("calls < int.MaxValue")]
    [Ensures("OwnerSpec.Held(Result, chooseLeft ? left : right)")]
    public static OwnedCell FromCalls(bool chooseLeft, int left, int right, ref int calls)
    {
        OwnedCell result = chooseLeft ? Make(ref calls, left) : Make(ref calls, right);
        int observed = result.Current;
        Pal.Assert(observed == (chooseLeft ? left : right));
        return result;
    }

    [Ensures("OwnerSpec.Held(Result, chooseLeft ? left : right)")]
    public static OwnedCell Create(bool chooseLeft, int left, int right)
    {
        OwnedCell result;
        if (chooseLeft)
            result = new OwnedCell(left);
        else
            result = new OwnedCell(right);
        Pal.Join(PlainLocalSpec.Held(result, chooseLeft ? left : right));
        PlainLocalProof.Assigned(result, (SpecInt)(chooseLeft ? left : right));
        int observed = result.Current;
        Pal.Assert(observed == (chooseLeft ? left : right));
        return result;
    }
}

public static class PlainLocalSpec
{
    [SpecOp("PlainLocals.snapshot")]
    public static CellSnapshot Snapshot(int value) => throw new System.InvalidOperationException();

    [SpecOp("PlainLocals.held")]
    public static SlProp Held(OwnedCell? cell, SpecInt value) => throw new System.InvalidOperationException();
}

public static class PlainLocalProof
{
    [Lemma]
    [Requires("OwnerSpec.Held(cell, value)")]
    [Ensures("OwnerSpec.Raw(cell, PlainLocalSpec.Snapshot(value), Perm.Full)")]
    [PulseBody("PlainLocals.canonical $(cell) $(value)")]
    public static void Canonical(OwnedCell cell, int value) { }

    [Lemma]
    [Preserves("PlainLocalSpec.Held(cell, value)")]
    [Ensures("cell != null")]
    [PulseBody("PlainLocals.assigned $(cell) $(value)")]
    public static void Assigned(OwnedCell? cell, Ghost<SpecInt> value) { }
}

[Invariant("value == 0")]
public sealed class PlainCleanupOwner
{
    private int value;
    [Model] private SpecInt Model => value;
    [Spec] public SpecInt Value => Model;

    [Ensures("@this.Value == 0")]
    public PlainCleanupOwner() { value = 0; }

    [Requires("calls < int.MaxValue")]
    [Ensures("calls == Pal.Old(calls) + 1")]
    [Ensures("@this.Value == Pal.Old(@this.Value)")]
    [Ensures("Result == cell")]
    public OwnedCell Identity(OwnedCell cell, ref int calls)
    {
        ++calls;
        return cell;
    }

    [Requires("calls < int.MaxValue")]
    [Ensures("@this.Value == Pal.Old(@this.Value)")]
    public bool Conditional(bool chooseLeft, OwnedCell cell, ref int calls)
    {
        int initial = value;
        bool same = (chooseLeft ? Identity(cell, ref calls) : Identity(cell, ref calls)) == cell;
        // This store requires the receiver's raw cell after each branch call.
        // Its saved concrete value also makes the final owner model explicit.
        value = initial;
        Pal.Assert(value == initial);
        return same;
    }
}
