using System;
using System.Collections;
using System.Collections.Generic;
using PalLang;

// §34. Members that take an `IEnumerable<T>` or `ICollection<T>`, in the style of
// dotnet/runtime's `List<T>.AddRange`: a type test dispatches to the collection's
// `Count` and `CopyTo`, and otherwise an enumerator walks the items.
[assembly: TranslateAnnotatedOnly]

[Spec]
public struct BagModel
{
    public Seq<int> Items;
    public Seq<int> Store;
}

[Invariant("0 <= _size")]
[Invariant("_size <= _items.Length")]
public class Bag
{
    private int[] _items;
    private int _size;

    [Model]
    private BagModel Model => new BagModel { Items = Pal.Slice(Pal.Contents(_items), 0, _size), Store = Pal.Contents(_items) };

    [Spec] public Seq<int> Items => Model.Items;

    [Spec] public Seq<int> Store => Model.Store;

    [Ensures("@this.Items.Length == 0")]
    public Bag()
    {
        _items = new int[4];
        _size = 0;
    }

    // R34.15. A chained constructor whose one call may raise, leaving the object built so far.
    [Throws(typeof(ArgumentOutOfRangeException), "capacity < 0")]
    [Ensures("@this.Items.Length == 0")]
    public Bag(int capacity) : this()
    {
        Reserve(capacity);
    }

    [Throws(typeof(ArgumentOutOfRangeException), "capacity < 0")]
    [Ensures("@this.Items == Pal.Old(@this.Items)")]
    public void Reserve(int capacity)
    {
        if (capacity < 0)
            throw new ArgumentOutOfRangeException(nameof(capacity));
        if (capacity > _items.Length)
        {
            int[] grown = new int[capacity];
            Array.Copy(_items, grown, _size);
            _items = grown;
        }
    }

    [Requires("@this.Items.Length < int.MaxValue")]
    [Ensures("@this.Items == Pal.Snoc(Pal.Old(@this.Items), item)")]
    public void Add(int item)
    {
        if (_size == _items.Length)
        {
            int[] grown = new int[_size < 1073741823 ? 2 * _size + 1 : int.MaxValue];
            Array.Copy(_items, grown, _size);
            _items = grown;
        }
        _items[_size] = item;
        _size++;
    }

    [Requires("@this.Store.Length < min")]
    [Ensures("@this.Store.Length >= min")]
    [Ensures("@this.Items == Pal.Old(@this.Items)")]
    [Ensures("Pal.Slice(@this.Store, 0, Pal.Old(@this.Store).Length) == Pal.Old(@this.Store)")]
    private void GrowTo(int min)
    {
        int[] grown = new int[min];
        Array.Copy(_items, grown, _items.Length);
        _items = grown;
    }

    // R34.17. An arm that grows the receiver, before the write that needs the new capacity.
    [Requires("@this.Items.Length == 0")]
    [Requires("Pal.Contents(items).Length < int.MaxValue")]
    [Ensures("@this.Items.Length == Pal.Contents(items).Length")]
    public void Fill(IEnumerable<int> items)
    {
        int i = 0;
        foreach (int x in items)
        {
            Pal.Invariant(0 <= i && i <= _items.Length && i == Pal.Index(x) && _size == 0);
            if (_items.Length == i)
                GrowTo(i + 1);
            _items[i++] = x;
        }
        _size = i;
    }

    // R34.4–R34.7. The fast path copies a collection; the slow path enumerates.
    [Requires("@this.Items.Length + Pal.Contents(collection).Length <= int.MaxValue")]
    [Ensures("@this.Items == Pal.Concat(Pal.Old(@this.Items), Pal.Contents(collection))")]
    public void AddRange(IEnumerable<int> collection)
    {
        if (collection == null)
            throw new ArgumentNullException(nameof(collection));

        if (collection is ICollection<int> c)
        {
            int count = c.Count;
            if (count > 0)
            {
                if (_items.Length - _size < count)
                {
                    int[] grown = new int[_size + count];
                    Array.Copy(_items, grown, _size);
                    _items = grown;
                }
                c.CopyTo(_items, _size);
                _size += count;
            }
        }
        else
        {
            using (IEnumerator<int> en = collection.GetEnumerator())
            {
                while (en.MoveNext())
                {
                    Pal.Invariant(0 <= _size && _size <= _items.Length);
                    Pal.Invariant(Pal.Slice(Pal.Contents(_items), 0, _size) ==
                        Pal.Concat(Pal.Old(this.Items), Pal.Slice(Pal.Contents(collection), 0, Pal.Index(en))));
                    Add(en.Current);
                }
            }
        }
    }
}

public static class Sums
{
    // R34.6. A static walk over an enumerable.
    [Ensures("Result == Pal.Contents(items).Length")]
    public static int CountAll(IEnumerable<int> items)
    {
        int n = 0;
        using IEnumerator<int> en = items.GetEnumerator();
        while (en.MoveNext())
        {
            Pal.Invariant(n == Pal.Index(en));
            n++;
        }
        return n;
    }

    // R34.3. An `ICollection<T>` parameter is a collection: its `Count` is its length.
    [Ensures("Result == Pal.Contents(items).Length")]
    public static int Size(ICollection<int> items) => items.Count;

    // R34.8. A `foreach` over an enumerable.
    [Ensures("0 <= Result && Result <= Pal.Contents(items).Length")]
    public static int CountPositive(IEnumerable<int> items)
    {
        int n = 0;
        foreach (int x in items)
        {
            Pal.Invariant(0 <= n && n <= Pal.Index(x));
            if (x > 0) n++;
        }
        return n;
    }

    // R34.19. A deconstructing `foreach` over pairs: the components rebuild the pair.
    [Ensures("0 <= Result && Result <= Pal.Contents(items).Length")]
    public static int CountOrdered(IEnumerable<(int Lo, int Hi)> items)
    {
        int n = 0;
        foreach ((int lo, int hi) in items)
        {
            Pal.Invariant(0 <= n && n <= Pal.Index(lo));
            Pal.Assert(Pal.Same((lo, hi), Pal.Contents(items)[Pal.Index(lo) - 1]));
            if (lo <= hi) n++;
        }
        return n;
    }

    // R34.20. `as ICollection<T>`: a non-null alias is the collection, with its `Count`.
    [Ensures("Result == Pal.Contents(items).Length")]
    public static int SizeOf(IEnumerable<int> items)
    {
        var c = items as ICollection<int>;
        if (c is not null)
        {
            return c.Count;
        }
        int n = 0;
        foreach (int x in items)
        {
            Pal.Invariant(n == Pal.Index(x));
            n++;
        }
        return n;
    }

    // R34.16. A `Comparison<T>` is a comparer; testing it against `null` is `is_null`.
    [Throws(typeof(ArgumentNullException), "comparison == null")]
    [Ensures("Result == (comparison != null)")]
    public static bool Checked(Comparison<int> comparison)
    {
        if (comparison == null) throw new ArgumentNullException(nameof(comparison));
        return comparison != null;
    }
}

// R34.9-R34.14. A copy of an enumeration into a growing array, in the style of the BCL's
// `EnumerableHelpers.ToArray`, and an object built from it through an `out` field.
[Invariant("0 <= _size")]
[Invariant("_size <= _items.Length")]
public class Snapshot
{
    private int[] _items;
    private int _size;

    [Model]
    private BagModel Model => new BagModel { Items = Pal.Slice(Pal.Contents(_items), 0, _size), Store = Pal.Contents(_items) };

    [Spec] public Seq<int> Items => Model.Items;

    // R34.14. `out _size`.
    [Ensures("@this.Items == Pal.Contents(items)")]
    public Snapshot(IEnumerable<int> items)
    {
        _items = Copy(items, out _size);
    }

    [Ensures("0 <= length && length <= Pal.Contents(Result).Length")]
    [Ensures("Pal.Contents(Result).Length <= int.MaxValue")]
    [Ensures("Pal.Slice(Pal.Contents(Result), 0, length) == Pal.Contents(items)")]
    [Wrapping]
    private static int[] Copy(IEnumerable<int> items, out int length)
    {
        // R34.13. A `const` local.
        const int Max = 0X7FFFFFC7;
        // R34.9. A `return` inside a `using` block that code follows.
        using (IEnumerator<int> en = items.GetEnumerator())
        {
            if (en.MoveNext())
            {
                // R34.10. A reassigned array local.
                int[] arr = new int[4];
                arr[0] = en.Current;
                int count = 1;
                while (en.MoveNext())
                {
                    Pal.Invariant(1 <= count && count == Pal.Index(en) && count <= arr.Length);
                    Pal.Invariant(Pal.Slice(Pal.Contents(arr), 0, count) == Pal.Slice(Pal.Contents(items), 0, count));
                    if (count == arr.Length)
                    {
                        // R34.11, R34.12. A declaration in a non-final arm; a wrapping shift.
                        int newLength = count << 1;
                        if ((uint)newLength > Max)
                        {
                            newLength = Max <= count ? count + 1 : Max;
                        }
                        Array.Resize(ref arr, newLength);
                    }
                    arr[count++] = en.Current;
                }
                length = count;
                return arr;
            }
        }
        length = 0;
        return new int[0];
    }
}

[Spec]
public struct TallyModel
{
    public SpecInt Count;
}

// R34.21. A constructor whose body only calls the object's methods runs over the object
// closed, its invariant first folded at the fields' defaults.
[Invariant("0 <= _n")]
public class Tally
{
    private int _n;

    [Model]
    private TallyModel Model => new TallyModel { Count = _n };

    [Spec] public SpecInt Count => Model.Count;

    [Requires("@this.Count < int.MaxValue")]
    [Ensures("@this.Count == Pal.Old(@this.Count) + 1")]
    public void Bump() { _n++; }

    [Requires("Pal.Contents(items).Length < int.MaxValue")]
    [Ensures("@this.Count == Pal.Contents(items).Length")]
    public Tally(IEnumerable<int> items)
    {
        foreach (int x in items)
        {
            Pal.Invariant(this.Count == Pal.Index(x));
            Bump();
        }
    }
}

[Spec]
public struct PairsModel
{
    public Seq<int> Keys;
    public Seq<int> Values;
}

// R34.22-R34.24. An `IDictionary<K,V>` argument, in the style of `SortedList`'s: its
// count sizes the object through the chained constructor, its keys and values are copied
// out and sorted together, and a duplicate is reported with the key read for the message.
[Invariant("_keys.Length == _values.Length")]
public class Pairs
{
    private int[] _keys;
    private int[] _values;
    private IComparer<int> _cmp;

    [Model]
    private PairsModel Model => new PairsModel { Keys = Pal.Contents(_keys), Values = Pal.Contents(_values) };

    [Spec] public Seq<int> Keys => Model.Keys;
    [Spec] public Seq<int> Values => Model.Values;

    // R34.24. Read in a constructor as the field it returns.
    private IComparer<int> Cmp { get { return _cmp; } }

    [Requires("n >= 0")]
    [Ensures("@this.Keys.Length == n")]
    public Pairs(int n, IComparer<int> cmp)
    {
        _keys = new int[n];
        _values = new int[n];
        _cmp = cmp;
    }

    [Throws(typeof(ArgumentException))]
    [Ensures("@this.Keys.Length == Pal.Contents(d).Length")]
    [Ensures("@this.Values.Length == Pal.Contents(d).Length")]
    public Pairs(IDictionary<int, int> d, IComparer<int> cmp)
        : this(d?.Count ?? throw new ArgumentNullException(nameof(d)), cmp)
    {
        int[] keys = _keys;
        d.Keys.CopyTo(keys, 0);
        d.Values.CopyTo(_values, 0);
        IComparer<int> c = Cmp;
        Array.Sort<int, int>(keys, _values, c);
        int i = 1;
        if (keys.Length > 1 && c.Compare(keys[0], keys[i]) == 0)
        {
            // R34.23, and the object built so far is discarded.
            throw new ArgumentException(keys[i].ToString());
        }
    }
}

[Spec]
public struct RowModel
{
    public Seq<int> Items;
}

// R34.26. A sealed class whose `Count`, `CopyTo` and `GetEnumerator` are translated: an
// object of it at an enumerable parameter is passed as a snapshot of its items.
public sealed class Row : IEnumerable<int>
{
    private int[] _items;

    [Model]
    private RowModel Model => new RowModel { Items = Pal.Contents(_items) };

    [Spec] public Seq<int> Items => Model.Items;

    [Requires("n >= 0")]
    [Ensures("@this.Items.Length == n")]
    public Row(int n)
    {
        _items = new int[n];
    }

    [Ensures("Result == @this.Items.Length")]
    [Ensures("@this.Items == Pal.Old(@this.Items)")]
    public int Count => _items.Length;

    [Requires("0 <= index && index + @this.Items.Length <= Pal.Contents(array).Length")]
    [Ensures("Pal.Contents(array) == Pal.Splice(Pal.Old(Pal.Contents(array)), index, index + @this.Items.Length, @this.Items)")]
    [Ensures("@this.Items == Pal.Old(@this.Items)")]
    public void CopyTo(int[] array, int index)
    {
        Array.Copy(_items, 0, array, index, _items.Length);
    }

    [Ensures("ReferenceEquals(Result._row, @this) && Result._index == 0")]
    public Enumerator GetEnumerator() => new Enumerator(this);

    IEnumerator<int> IEnumerable<int>.GetEnumerator() => GetEnumerator();

    IEnumerator IEnumerable.GetEnumerator() => GetEnumerator();

    public struct Enumerator : IEnumerator<int>
    {
        private readonly Row _row;
        private int _index;

        [Ensures("ReferenceEquals(@this._row, row) && @this._index == 0")]
        internal Enumerator(Row row)
        {
            _row = row;
            _index = 0;
        }

        public int Current => _row._items[_index - 1];

        object IEnumerator.Current => Current;

        public bool MoveNext() => ++_index <= _row._items.Length;

        public void Reset() => _index = 0;

        public void Dispose() { }
    }
}

public static class Rows
{
    // R34.26. `CountAll` walks a snapshot of the row's items.
    [Requires("n >= 0")]
    [Ensures("Result == n")]
    public static int CountRow(int n)
    {
        Row r = new Row(n);
        return Sums.CountAll(r);
    }

    [Requires("n >= 0")]
    [Ensures("Pal.Contents(Result).Length == n")]
    public static int[] Make(int n) => new int[n];

    // R34.26. An array local initialised by a call owns the array the call returns.
    [Requires("n > 0")]
    [Ensures("Result == 7")]
    public static int First(int n)
    {
        int[] a = Make(n);
        a[0] = 7;
        Pal.Assert(Pal.Contents(a)[0] == 7);
        return a[0];
    }
}
