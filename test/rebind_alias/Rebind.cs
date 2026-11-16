using System.Runtime.CompilerServices;
using PalLang;

#pragma warning disable CS0649, CS0414

// §30. The aliases `HashSet<T>.AddIfNotPresent` and `Dictionary<TKey,TValue>.TryInsert` keep
// across a resize: a `ref` local declared null (`Unsafe.NullRef`) and bound on each path
// (R30.1), rebound after a call that replaces the array it points into (R30.1), and an
// array local re-read from its field after that call (R30.2).
[Spec]
public struct RebindModel
{
    public SpecInt Count;
    public SpecInt Length;
}

[Invariant("_slots.Length == _heads.Length && _slots.Length > 0 && _slots.Length <= 1000")]
[Invariant("0 <= _count && _count <= _slots.Length")]
public sealed class Rebind
{
    private int[] _heads = new int[1];
    private int[] _slots = new int[1];
    private int _count;

    [Ensures("@this.SpecCount == Old(@this.SpecCount) + 1")]
    [Requires("@this.SpecCount < 500")]
    public void Add(int h, bool first)
    {
        int[] slots = _slots;
        ref int head = ref Unsafe.NullRef<int>();
        if (first)
        {
            head = ref HeadRef(h);
        }
        else
        {
            h = h / 2;
            head = ref HeadRef(h);
        }
        int count = _count;
        if (count == slots.Length)
        {
            Grow();
            head = ref HeadRef(h);
            slots = _slots;
        }
        slots[count] = head;
        head = count + 1;
        _count = count + 1;
    }

    [Model]
    private RebindModel Model => new RebindModel { Count = _count, Length = _slots.Length };

    [Spec] public SpecInt SpecCount => Model.Count;
    [Spec] public SpecInt SpecLength => Model.Length;

    [Ensures("@this.SpecCount == Old(@this.SpecCount) && @this.SpecLength > Old(@this.SpecLength)")]
    [Requires("@this.SpecLength < 500")]
    private void Grow()
    {
        int size = _slots.Length * 2;
        _heads = new int[size];
        _slots = new int[size];
    }

    private ref int HeadRef(int h)
    {
        int[] heads = _heads;
        return ref heads[(uint)h % (uint)heads.Length];
    }
}
