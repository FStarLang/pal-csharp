using System;
using System.Diagnostics;
using System.Diagnostics.CodeAnalysis;
using System.Runtime.CompilerServices;
using PalLang;
using static System.Collections.ThrowHelper;

// §33. The shapes of dotnet/runtime's `OrderedDictionary<TKey,TValue>`, each rule exercised by
// the member that names it.
[assembly: TranslateAnnotatedOnly]
[assembly: SpecBinding("P:System.IntPtr.Size", "Pulse.Lib.CSharp.Platform.intptr_size")]

[Spec]
public struct OrderedTableModel
{
    public Seq<OrderedTable.Slot> Slots;
    public bool NoBuckets;
}

[Invariant("_slots != null")]
[Invariant("_wide == (IntPtr.Size == 8)")]
public class OrderedTable
{
    public struct Slot
    {
        public int Key;
        public int Next;
    }

    private Slot[] _slots;
    private int[]? _buckets;
    private bool _wide;

    [Model]
    private OrderedTableModel Model => new OrderedTableModel { Slots = Pal.Contents(_slots), NoBuckets = _buckets == null };

    [Spec] internal bool SpecNoBuckets => Model.NoBuckets;
    [Spec] internal Seq<Slot> SpecSlots => Model.Slots;

    // R33.4. A bound machine-integer member (`IntPtr.Size`) in code and in an invariant.
    public OrderedTable()
    {
        _slots = new Slot[4];
        _buckets = null;
        _wide = IntPtr.Size == 8;
    }

    // R33.1.
    [Requires("n >= 0")]
    [Ensures("Result == n")]
    private static int Guarded(int n)
    {
        ThrowIfNegative(n);
        return n;
    }

    // R33.6. `is null` on an array is a real test, not `false`.
    [Ensures("Result == @this.SpecNoBuckets")]
    private bool NoBuckets() => _buckets is null;

    [Ensures("Result == !@this.SpecNoBuckets")]
    private bool HasBuckets() => _buckets is not null;

    // R33.3. A `ref`-returning method with `Debug.Assert`s and a two-way `return ref`.
    private ref Slot SlotAt(int i, bool first)
    {
        Debug.Assert(i >= 0);
        if (first) return ref _slots[0];
        else return ref _slots[i];
    }

    [Requires("0 <= i && i < @this.SpecSlots.Length")]
    [Ensures("Result == @this.SpecSlots[i].Key")]
    private int KeyAt(int i) => SlotAt(i, false).Key;

    // R33.2. `r` is declared between the jump and its label.
    [Ensures("Result >= 0")]
    private static int Clamp(int n)
    {
        if (n < 0) goto Negative;
        int r = n;
        return r;

    Negative:
        r = 0;
        return r;
    }

    // R33.2 and R33.5. A chain walk through a rebound `ref` local, leaving by forward
    // `goto`s; the label after the `[DoesNotReturn]` call is reached only by jumps.
    [Requires("0 <= start")]
    [Ensures("-1 <= Result && Result < @this.SpecSlots.Length")]
    [Throws(typeof(InvalidOperationException))]
    private int Find(int start, int key)
    {
        ref Slot slot = ref Unsafe.NullRef<Slot>();
        Slot[] slots = _slots;
        int i = start;
        int steps = 0;
        while (steps < slots.Length)
        {
            Pal.Invariant(Pal.Returned() || 0 <= i);
            Pal.Invariant(Pal.Implies(Pal.Returned(), -1 <= Pal.Result<int>() && Pal.Result<int>() < slots.Length));
            Pal.Invariant(slots == _slots);
            Pal.Invariant(steps <= slots.Length);
            Pal.Decreases(slots.Length - steps);
            if ((uint)i >= (uint)slots.Length)
            {
                goto NotFound;
            }
            slot = ref slots[i];
            if (slot.Key == key)
            {
                goto Found;
            }
            i = slot.Next;
            if (i < 0) goto NotFound;
            steps++;
        }
        goto Cycle;

    NotFound:
        return -1;

    Cycle:
        System.Collections.ThrowHelper.ThrowCycle();

    Found:
        return i;
    }

    // R33.8. `a?.Length ?? d` on an array.
    [Ensures("Pal.Implies(@this.SpecNoBuckets, Result == 0) && Result >= 0")]
    public int BucketCount => _buckets?.Length ?? 0;

    [Ensures("Result == 3")]
    private static int Fill(int k, out int v, ref int a, ref int b)
    {
        v = k;
        a = 1;
        b = 2;
        Pal.Assert(a == 1);
        return 3;
    }

    // R33.7. An `out _` discard, and one local passed twice by `ref` to parameters the callee
    // only assigns.
    [Ensures("Result == 3")]
    public static int Discard(int k)
    {
        int _ = 0;
        return Fill(k, out int _, ref _, ref _);
    }
}
