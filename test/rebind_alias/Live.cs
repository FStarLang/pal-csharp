using PalLang;

#pragma warning disable CS0649, CS0414

// §30, from `Dictionary<TKey,TValue>`: `a?.Length ?? 0` (R30.14); an element field as the
// argument of an inlined `ref` helper (R30.15); a `ref` local into an array local that was
// re-read from its field before the alias was declared (R30.16); and a by-value argument
// to a throwing helper inside a loop, whose value the invariant still knows (R30.17).
[Spec]
public struct LiveModel
{
    public SpecInt Length;
}

public struct Slot
{
    public int Code;
    public int Value;
}

[Invariant("_slots == null || (_slots.Length > 0 && _slots.Length == _heads.Length && _slots.Length <= 1000)")]
[Invariant("_slots != null || _heads.Length == 1")]
public sealed class Live
{
    private Slot[]? _slots;
    private int[] _heads = new int[1];

    [Model]
    private LiveModel Model => new LiveModel { Length = _heads.Length };

    [Spec] public SpecInt SpecLength => Model.Length;

    [Ensures("Result == 0 || Result == @this.SpecLength")]
    public int Capacity => _slots?.Length ?? 0;

    [Requires("@this.SpecLength < 500")]
    [Ensures("@this.SpecLength > 0")]
    public void Put(int code, int value)
    {
        Slot[]? slots = _slots;
        if (slots == null || slots.Length < 2)
        {
            Grow();
            slots = _slots;
        }
        ref Slot slot = ref slots![0];
        slot.Code = code;
        slot.Value = value;
    }

    [Requires("slots.Length > 0")]
    public void Touch(Slot[] slots)
    {
        _heads[0] = 0;
        ref int head = ref HeadRef(slots[0].Code);
        head = 1;
    }

    [Ensures("@this.SpecLength >= 2 && @this.SpecLength > Old(@this.SpecLength)")]
    [Requires("@this.SpecLength < 500")]
    private void Grow()
    {
        int size = (_slots?.Length ?? 1) * 2;
        _heads = new int[size];
        _slots = new Slot[size];
    }

    private ref int HeadRef(int h)
    {
        int[] heads = _heads;
        return ref heads[(uint)h % (uint)heads.Length];
    }

    [Ensures("Result == key")]
    public static int Find(int key, int[] keys)
    {
        int i = 0;
        while (i < keys.Length)
        {
            Pal.Invariant(0 <= i && i <= keys.Length);
            Pal.Decreases(keys.Length - i);
            if (keys[i] == key && i < 0)
            {
                Fail(key);
            }
            i++;
        }
        return key;
    }

    [System.Diagnostics.CodeAnalysis.DoesNotReturn]
    [Throws(typeof(System.InvalidOperationException))]
    [Ensures("false")]
    private static void Fail(int key) => throw new System.InvalidOperationException();
}
