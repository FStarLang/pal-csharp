using System.Diagnostics;
using PalLang;

#pragma warning disable CS0649, CS0414

// §30. `HashSet<T>.Resize`: a `for` loop inside an `if` that is not the method's last
// statement, and a `ref` local inside a loop body's `if` that is not the body's last
// (R30.10); a ghost statement after an array local has moved into a field (R30.11).
[Spec]
public struct GrowModel
{
    public SpecInt Length;
}

[Invariant("_items.Length > 0 && _items.Length <= 1000")]
public sealed class Grow
{
    private int[] _items = new int[1];

    [Lemma]
    [Ensures("true")]
    [Conditional("PAL")]
    private static void Note(SpecInt n) { }

    [Requires("@this.SpecLength <= newSize && newSize <= 1000")]
    [Ensures("@this.SpecLength == newSize")]
    public void Resize(int newSize, bool clear)
    {
        int[] items = new int[newSize];
        if (clear)
        {
            for (int i = 0; i < newSize; i++)
            {
                Pal.Invariant(items.Length == newSize && 0 <= i);
                items[i] = 0;
            }
        }

        for (int i = 0; i < newSize; i++)
        {
            Pal.Invariant(items.Length == newSize && 0 <= i);
            if (i % 2 == 0)
            {
                ref int slot = ref items[i];
                slot = i;
            }
            Note(i);
        }

        _items = items;
        Note(_items.Length);
    }

    [Model]
    private GrowModel Model => new GrowModel { Length = _items.Length };

    [Spec] public SpecInt SpecLength => Model.Length;
}
