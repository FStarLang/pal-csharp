using System;
using System.Collections;
using System.Diagnostics;
using System.Diagnostics.CodeAnalysis;
using PalLang;

[assembly: TranslateAnnotatedOnly]

[Spec]
public struct BagModel<T>
{
    public Seq<T> Items;
    public SpecInt Version;
}

[Invariant("0 <= _size")]
[Invariant("_size <= _items.Length")]
public class Bag<T> : IEnumerable
{
    private T[] _items;
    private int _size;
    [Wrapping] private int _version;

    [Model]
    private BagModel<T> Model => new BagModel<T>
    {
        Items = Pal.Slice(Pal.Contents(_items), 0, _size),
        Version = _version,
    };

    [Spec] public Seq<T> Items => Model.Items;
    [Spec] public SpecInt SpecCount => Model.Items.Length;
    [Spec] public SpecInt SpecVersion => Model.Version;

    [Ensures("@this.SpecCount == 0")]
    public Bag()
    {
        _items = new T[0];
    }

    [Ensures("@this.SpecCount == 0")]
    public void Clear()
    {
        _size = 0;
        _version++;
    }

    [Ensures("ReferenceEquals(Result._list, @this) && Result._version == @this.SpecVersion && Result._index == 0")]
    public Enumerator GetEnumerator() => new Enumerator(this);

    // R29.4. The boxed enumerator is related to the struct it boxes, not compared.
    [Ensures("Pal.Exists((Bag<T>.Enumerator e) => Pal.Boxes(Result, e) && ReferenceEquals(e._list, @this) && e._version == @this.SpecVersion && e._index == 0)")]
    IEnumerator IEnumerable.GetEnumerator() => GetEnumerator();

    [Ensures("Pal.Boxes(Result.Key, key) && Pal.Boxes(Result.Value, value)")]
    public static DictionaryEntry Entry(int key, T value) => new DictionaryEntry(key, value);

    public struct Enumerator : IEnumerator
    {
        private readonly Bag<T> _list;
        private readonly int _version;
        private int _index;
        private T? _current;

        [Ensures("ReferenceEquals(@this._list, list) && @this._version == list.SpecVersion && @this._index == 0")]
        internal Enumerator(Bag<T> list)
        {
            _list = list;
            _version = list._version;
            _index = 0;
            _current = default;
        }

        [Throws(typeof(InvalidOperationException), "@this._version != @this._list.SpecVersion")]
        [Ensures("Result == (0 <= Pal.Old(@this._index) && Pal.Old(@this._index) < @this._list.SpecCount)")]
        [Ensures("Pal.Implies(Result, @this._index == Pal.Old(@this._index) + 1 && Pal.Same(@this._current, @this._list.Items[Pal.Old(@this._index)]))")]
        [Ensures("Pal.Implies(!Result, @this._index == -1)")]
        public bool MoveNext()
        {
            Bag<T> localList = _list;

            if (_version != localList._version)
            {
                throw new InvalidOperationException();
            }

            if ((uint)_index < (uint)localList._size)
            {
                _current = localList._items[_index];
                _index++;
                return true;
            }

            _current = default;
            _index = -1;
            return false;
        }

        // A loop in a borrowing member keeps the borrowed object and the readonly fields
        // without being told (R28.4).
        [Requires("0 <= @this._index && @this._index <= n")]
        [Ensures("@this._index == n")]
        public void SkipTo(int n)
        {
            while (_index < n)
            {
                Pal.Invariant(_index <= n);
                Pal.Decreases(n - _index);
                _index++;
            }
        }

        [Ensures("Pal.Same(Result, @this._current)")]
        public T Current => _current!;

        // R29.4: a self-call of a borrowing reader, then a box.
        [Ensures("Pal.Boxes(Result, @this._current)")]
        object? IEnumerator.Current => Current;

        [Ensures("@this._index == 0")]
        void IEnumerator.Reset()
        {
            _index = 0;
            _current = default;
        }

        [Ensures("true")]
        public void Dispose()
        {
        }
    }
}
