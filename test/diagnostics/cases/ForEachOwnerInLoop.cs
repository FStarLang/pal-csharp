// EXPECT: PALCS0714
// R27.51. A `foreach` over an object of the method's class is translated only directly in
// a block of the method, outside any loop: here it is inside a `while`.
using System;
using PalLang;

[assembly: TranslateAnnotatedOnly]

[Spec]
public struct CellsModel
{
    public Seq<int> Items;
    public SpecInt Version;
}

public class Cells
{
    private int[] _items;
    private int _version;

    [Model]
    private CellsModel Model => new CellsModel { Items = Pal.Contents(_items), Version = _version };

    [Spec] public SpecInt SpecVersion => Model.Version;

    [Ensures("true")]
    public Cells() { _items = new int[0]; }

    [Ensures("ReferenceEquals(Result._cells, @this) && Result._index == 0")]
    public Enumerator GetEnumerator() => new Enumerator(this);

    [Ensures("true")]
    public int Twice(Cells other)
    {
        int n = 0;
        while (n < 2)
        {
            Pal.Decreases(2 - n);
            foreach (int x in other) { }
            n++;
        }
        return n;
    }

    public struct Enumerator
    {
        private readonly Cells _cells;
        private int _index;

        [Ensures("ReferenceEquals(@this._cells, cells) && @this._index == 0")]
        internal Enumerator(Cells cells) { _cells = cells; _index = 0; }

        [Ensures("true")]
        public bool MoveNext() { _index++; return false; }

        [Ensures("true")]
        public int Current => 0;
    }
}
