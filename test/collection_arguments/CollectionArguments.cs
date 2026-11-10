using System;
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
}

[Invariant("0 <= _size")]
[Invariant("_size <= _items.Length")]
public class Bag
{
    private int[] _items;
    private int _size;

    [Model]
    private BagModel Model => new BagModel { Items = Pal.Slice(Pal.Contents(_items), 0, _size) };

    [Spec] public Seq<int> Items => Model.Items;

    [Ensures("@this.Items.Length == 0")]
    public Bag()
    {
        _items = new int[4];
        _size = 0;
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
    private BagModel Model => new BagModel { Items = Pal.Slice(Pal.Contents(_items), 0, _size) };

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
