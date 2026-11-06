using System;
using System.Collections.Generic;
using PalLang;

#pragma warning disable CS0649, CS0414

// §24. A hash chain walked the way `HashSet<T>.FindItemIndex` walks it, exercising the rules
// that walk needs: a field read into an array local (R24.19), a `ref`-returning helper inlined
// (R24.9), a `ref` local bound to an element (R24.8), a `uint` index (R24.16), a `uint`
// counter incremented (R24.16), a `[PulseBody]` spec function in an invariant (R24.17), a
// comparer in a `[Spec]` struct (R24.18) and `EqualityComparer<T>.Default` (R24.20).
[assembly: SpecBinding("T:System.Collections.Generic.IEqualityComparer`1", "Pulse.Lib.CSharp.Equality.comparer")]
[assembly: SpecBinding("M:System.Collections.Generic.IEqualityComparer`1.Equals(`0,`0)", "Pulse.Lib.CSharp.Equality.equals")]
[assembly: SpecBinding("M:System.Collections.Generic.IEqualityComparer`1.GetHashCode(`0)", "Pulse.Lib.CSharp.Equality.get_hash_code")]
[assembly: SpecBinding("T:System.Collections.Generic.EqualityComparer`1", "Pulse.Lib.CSharp.Equality.comparer")]
[assembly: SpecBinding("P:System.Collections.Generic.EqualityComparer`1.Default", "Pulse.Lib.CSharp.Equality.default_comparer")]
[assembly: SpecBinding("M:System.Collections.Generic.EqualityComparer`1.Equals(`0,`0)", "Pulse.Lib.CSharp.Equality.equals")]

[Spec]
public struct ChainModel<T>
{
    public SpecInt Count;
    public IEqualityComparer<T>? Comparer;
}

[Invariant("0 <= _count && _count <= _entries.Length")]
[Invariant("(_buckets == null) == (_entries == null)")]
[Invariant("_buckets.Length == _entries.Length")]
[Invariant("_entries == null || _entries.Length > 0")]
[Invariant("_buckets == null || Chain<T>.Sized(Contents(_buckets), _entries.Length)")]
public class Chain<T>
{
    private int[]? _buckets;
    private Entry[]? _entries;
    private int _count;
    private IEqualityComparer<T>? _comparer;

    [Model]
    private ChainModel<T> Model => new ChainModel<T> { Count = _count, Comparer = _comparer };

    [Spec] public IEqualityComparer<T>? SpecComparer => Model.Comparer;

    // R24.17: defined in F*; its C# body is never looked at.
    [Spec]
    [PulseBody("Seq.length $(buckets) == $(n) /\\ (forall (k: nat). {:pattern Seq.index $(buckets) k} k < Seq.length $(buckets) ==> FStar.Int32.v (Seq.index $(buckets) k) >= 0)")]
    private static bool Sized(Seq<int> buckets, SpecInt n) => throw new InvalidOperationException();

    private ref int GetBucketRef(int hashCode)
    {
        int[] buckets = _buckets!;
        return ref buckets[(uint)hashCode % (uint)buckets.Length];
    }

    [Ensures("Result >= -1")]
    private int FirstWithHash(int hashCode)
    {
        int[]? buckets = _buckets;
        if (buckets != null)
        {
            Entry[]? entries = _entries;
            uint steps = 0;
            int i = GetBucketRef(hashCode) - 1;
            while ((uint)i < (uint)entries!.Length)
            {
                Pal.Invariant(steps <= (uint)entries.Length);
                Pal.Invariant(Pal.Implies(Pal.Returned(), Pal.Result<int>() >= -1));
                Pal.Decreases((uint)entries.Length - steps);
                ref Entry entry = ref entries[i];
                if (entry.HashCode == hashCode)
                {
                    return i;
                }
                i = entry.Next;
                if (steps >= (uint)entries.Length)
                {
                    return -1;
                }
                steps++;
            }
        }
        return -1;
    }

    [Ensures("Result == (@this.SpecComparer == null)")]
    public bool UsesDefault() => _comparer == null;

    [Ensures("Result == EqualityComparer<T>.Default.Equals(a, b)")]
    public static bool Same(T a, T b) => EqualityComparer<T>.Default.Equals(a, b);

    private struct Entry
    {
        public int HashCode;
        public int Next;
        public T Value;
    }
}
