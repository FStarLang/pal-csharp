using System;
using System.Diagnostics;
using PalLang;

[assembly: IncludePulseFile("OwnerState.fst")]
[assembly: IncludePulseFile("OwnerCells.fst")]
[assembly: IncludePulseFile("OwnerLease.fst")]
[assembly: IncludePulseFile("OwnerLease.Mixed.fst")]

namespace PalCSharp.Tests;

[Plain]
public sealed class OwnedCell
{
    public int value;

    [Ensures("OwnerSpec.Held(Result, initial)")]
    public OwnedCell(int initial) { value = initial; }

    [GhostArg("CellSnapshot Before"), GhostArg("Perm Permission")]
    [Preserves("OwnerSpec.Raw(@this, Before, Permission)")]
    [Ensures("Result == OwnerSpec.RawValue(Before)")]
    public int Current => value;

    [GhostArg("CellSnapshot Before"), GhostArg("Perm Permission")]
    [Preserves("OwnerSpec.Raw(@this, Before, Permission)")]
    [Ensures("Result == OwnerSpec.RawValue(Before)")]
    public int ReadWithWitness()
    {
        OwnerProof.Bounds(this);
        int result = value;
        Pal.Assert(OwnerSpec.RawValue(Pal.Ghost<CellSnapshot>("Before")) == result);
        return result;
    }

    [Requires("OwnerSpec.Cell(@this)")]
    [Ensures("OwnerSpec.Held(@this, next)")]
    public void Replace(int next) { value = next; }
}

[SpecType("OwnerState.state")]
public readonly struct OwnerState { }

[SpecType("Class_OwnedCell.class_OwnedCell__raw")]
public readonly struct CellSnapshot { }

// Pointer-bearing value records do not supply pointee ownership.
public struct CellHandle
{
    public OwnedCell Cell;
#if PAL
    public OwnerState Witness;
#endif
}

[Invariant("cell == null")]
public sealed class EmptyOwner
{
    private OwnedCell? cell = null;
#if PAL
    private OwnerState witness = OwnerSpec.Make(0);
    [Model]
    private SpecInt Model => OwnerSpec.Value(witness);
    [Spec]
    public SpecInt Value => Model;
#endif

    [Ensures("@this.Value == 0")]
    public EmptyOwner() { Pal.Assert(true); }

    [Ensures("Result")]
    public bool IsEmpty() => cell == null;
}

public static class OwnerSpec
{
    [SpecOp("OwnerState.make")]
    public static OwnerState Make(int value) => throw new InvalidOperationException();
    [SpecOp("OwnerState.value")]
    public static SpecInt Value(OwnerState state) => throw new InvalidOperationException();
    [SpecOp("OwnerCells.holds")]
    public static SlProp Holds(OwnedCell cell, SpecInt value, Perm permission) => throw new InvalidOperationException();
    [SpecOp("OwnerCells.opened")]
    public static SlProp Opened(OwnedCell cell, SpecInt value, Perm permission) => throw new InvalidOperationException();
    [SpecOp("OwnerCells.held")]
    public static SlProp Held(OwnedCell cell, int value) => throw new InvalidOperationException();
    [SpecOp("OwnerCells.cell")]
    public static SlProp Cell(OwnedCell cell) => throw new InvalidOperationException();
    [SpecOp("OwnerCells.raw")]
    public static SlProp Raw(OwnedCell cell, CellSnapshot snapshot, Perm permission) => throw new InvalidOperationException();
    [SpecOp("OwnerCells.raw_value")]
    public static SpecInt RawValue(CellSnapshot snapshot) => throw new InvalidOperationException();
}

public static class OwnerProof
{
    [Lemma, Conditional("PAL")]
    [GhostArg("CellSnapshot snapshot"), GhostArg("Perm permission")]
    [Preserves("OwnerSpec.Raw(cell, snapshot, permission)")]
    [Ensures("int.MinValue <= OwnerSpec.RawValue(snapshot) && OwnerSpec.RawValue(snapshot) <= int.MaxValue")]
    public static void Bounds(OwnedCell cell) { }

    [Lemma, Conditional("PAL")]
    [PulseBody("OwnerCells.close $(cell) $(value)")]
    [Requires("OwnerSpec.Held(cell, value)")]
    [Ensures("OwnerSpec.Holds(cell, value, Perm.Full)")]
    public static void Close(OwnedCell cell, int value) { }

    [Lemma, Conditional("PAL")]
    [PulseBody("OwnerCells.open_cell $(cell) $(value)")]
    [Requires("OwnerSpec.Holds(cell, value, Perm.Full)")]
    [Ensures("OwnerSpec.Held(cell, value)")]
    public static void Open(OwnedCell cell, int value) { }
}

public static class LeaseSpec
{
    [SpecOp("OwnerLease.inv")]
    public static SlProp Inv(CellOwner owner, SpecInt value, Perm permission) => throw new InvalidOperationException();
    [SpecOp("OwnerLease.opened")]
    public static SlProp Opened(CellOwner owner, SpecInt value, Perm permission) => throw new InvalidOperationException();
}

public static class LeaseProof
{
    [Lemma, Conditional("PAL"), GhostArg("CellOwner owner"), GhostArg("SpecInt model")]
    [Requires("LeaseSpec.Inv(owner, model, permission)")]
    [Requires("model == value")]
    [Ensures("LeaseSpec.Opened(owner, model, permission)")]
    [PulseBody("OwnerLease.begin_read $(owner) $(model) $(permission)")]
    public static void Begin(Ghost<SpecInt> value, Ghost<Perm> permission) { }

    [Lemma, Conditional("PAL"), GhostArg("CellOwner owner"), GhostArg("SpecInt model")]
    [Requires("model == value")]
    [Preserves("LeaseSpec.Opened(owner, model, permission)")]
    [Ensures("model == value")]
    public static void Keep(Ghost<SpecInt> value, Ghost<Perm> permission) { }

    [Lemma, Conditional("PAL"), GhostArg("CellOwner owner"), GhostArg("SpecInt model")]
    [Requires("LeaseSpec.Opened(owner, model, permission)")]
    [Requires("model == value")]
    [Ensures("LeaseSpec.Inv(owner, model, permission)")]
    [PulseBody("OwnerLease.end_read $(owner) $(model) $(permission)")]
    public static void End(Ghost<SpecInt> value, Ghost<Perm> permission) { }
}

// The compiler owns the owner's record. The explicit spatial invariant owns
// the referenced cell; the erased witness supplies the abstraction's value.
[Invariant("OwnerSpec.Holds(cell, OwnerSpec.Value(state), Pal.Permission())")]
public sealed class CellOwner
{
    private OwnedCell cell;
#if PAL
    private OwnerState state;

    [Model]
    private SpecInt Model => OwnerSpec.Value(state);

    [Spec]
    public SpecInt Value => Model;
#endif

    [Ensures("@this.Value == initial")]
    public CellOwner(int initial)
    {
        cell = MakeCell(initial);
#if PAL
        state = OwnerSpec.Make(initial);
#endif
    }

    [Ensures("OwnerSpec.Holds(Result, initial, Perm.Full)")]
    private static OwnedCell MakeCell(int initial)
    {
        var cell = new OwnedCell(initial);
        OwnerProof.Close(cell, initial);
        return cell;
    }

    [Ensures("Result == @this.Value")]
    public int Read()
    {
#if PAL
        OpenState(cell, state, Pal.Permission());
#endif
        int result = cell.Current;
#if PAL
        CloseState(cell, state, Pal.Permission());
#endif
        return result;
    }

    [Lemma, Conditional("PAL")]
    [PulseBody("OwnerCells.open_state $(cell) $(state) $(p)")]
    [Requires("OwnerSpec.Holds(cell, OwnerSpec.Value(state), p)")]
    [Ensures("OwnerSpec.Opened(cell, OwnerSpec.Value(state), p)")]
    private static void OpenState(OwnedCell cell, OwnerState state, Ghost<Perm> p) { }

    [Lemma, Conditional("PAL")]
    [PulseBody("OwnerCells.close_state $(cell) $(state) $(p)")]
    [Requires("OwnerSpec.Opened(cell, OwnerSpec.Value(state), p)")]
    [Ensures("OwnerSpec.Holds(cell, OwnerSpec.Value(state), p)")]
    private static void CloseState(OwnedCell cell, OwnerState state, Ghost<Perm> p) { }

    [Ensures("@this.Value == value")]
    public void Set(int value)
    {
#if PAL
        OpenState(cell, state, Perm.Full);
#endif
        cell.Replace(value);
        OwnerProof.Close(cell, value);
#if PAL
        state = OwnerSpec.Make(value);
#endif
    }

    [Ensures("@this.Value == (choose ? first : second)")]
    public void SetJoinedTail(bool choose, int first, int second)
    {
#if PAL
        OpenState(cell, state, Perm.Full);
#endif
        if (choose)
        {
            cell.Replace(first);
            OwnerProof.Close(cell, first);
#if PAL
            state = OwnerSpec.Make(first);
#endif
        }
        else
        {
            cell.Replace(second);
            OwnerProof.Close(cell, second);
#if PAL
            state = OwnerSpec.Make(second);
#endif
        }
#if PAL
        Pal.Join(OwnerSpec.Holds(cell, OwnerSpec.Value(state), Perm.Full));
        Pal.Join(OwnerSpec.Value(state) == (choose ? first : second));
#endif
    }

    [Frac("p")]
    [Ensures("Result == @this.Value && @this.Value == Pal.Old(@this.Value)")]
    public int ReadWithLease()
    {
#if PAL
        Ghost<SpecInt> snapshot = this.Value;
        LeaseProof.Begin(snapshot, Pal.Permission());
        LeaseProof.Keep(snapshot, Pal.Permission());
        Pal.Assert(snapshot.Value == snapshot.Value);
        LeaseProof.End(snapshot, Pal.Permission());
#endif
        return Read();
    }

}

public static class OwnerClients
{
    [Ensures("Result == cell")]
    public static OwnedCell? PointerLoopReturn(OwnedCell? cell)
    {
        while (cell != null)
        {
            Pal.Decreases(0);
            Pal.Invariant(Pal.Implies(Pal.Returned(), Pal.ReturnValue<OwnedCell?>() == cell));
            return cell;
        }
        return null;
    }

    [Ensures("Result == (a == b ? 1 : 2)")]
    public static int PointerChoice(OwnedCell a, OwnedCell b) => a == b ? 1 : 2;

    [GhostArg("CellSnapshot snapshot"), GhostArg("Perm permission")]
    [Preserves("OwnerSpec.Raw(handle.Cell, snapshot, permission)")]
    [Ensures("Result == OwnerSpec.RawValue(snapshot)")]
    public static int ReadHandle(CellHandle handle) => handle.Cell.ReadWithWitness();

    [Ensures("Result")]
    public static bool Same(CellOwner owner)
    {
        Pal.Share(owner);
        bool result = Equal(owner, owner);
        Pal.Gather(owner);
        return result;
    }

    [Ensures("Result == (a.Value == b.Value)")]
    public static bool Equal([Frac("p")] CellOwner a, [Frac("q")] CellOwner b)
    {
        return a.Read() == b.Read();
    }
}
