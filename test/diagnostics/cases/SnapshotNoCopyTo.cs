// EXPECT: PALCS0864
using System.Collections;
using System.Collections.Generic;
using PalLang;

[assembly: TranslateAnnotatedOnly]

[Spec]
public struct RowModel
{
    public Seq<int> Items;
}

// A sealed class passed at an enumerable parameter is passed as a snapshot of its items
// (R34.26), which needs its `CopyTo` translated.
public sealed class Row : IEnumerable<int>
{
    private int[] _items = new int[0];

    [Model]
    private RowModel Model => new RowModel { Items = Pal.Contents(_items) };

    [Spec] public Seq<int> Items => Model.Items;

    [Ensures("Result == @this.Items.Length")]
    public int Count => _items.Length;

    public IEnumerator<int> GetEnumerator() => ((IEnumerable<int>)_items).GetEnumerator();

    IEnumerator IEnumerable.GetEnumerator() => GetEnumerator();
}

public static class SnapshotNoCopyTo
{
    [Ensures("true")]
    public static int Size(IEnumerable<int> items)
    {
        int n = 0;
        foreach (int x in items)
        {
            Pal.Invariant(n == Pal.Index(x));
            n++;
        }
        return n;
    }

    [Ensures("true")]
    public static int Bad(Row r) => Size(r);
}
