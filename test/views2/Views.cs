using System;
using System.Collections;
using System.Collections.Generic;
using PalLang;

[assembly: TranslateAnnotatedOnly]
// R29.4. The shared empty enumerator.
[assembly: SpecBinding("M:Helpers.Empty``1", "Pulse.Lib.CSharp.Obj.empty_enumerator")]

// doc/translation.md §35: views, wrapping enumerators and non-generic members.

[Spec]
public struct ShelfModel<T>
{
    public Seq<T> Items;
    public SpecInt Version;
}

[Invariant("0 <= _size")]
[Invariant("_size <= _items.Length")]
public class Shelf<T> : IEnumerable<T>
{
    private T[] _items;
    private int _size;
    [Wrapping] private int _version;

    [Model]
    private ShelfModel<T> Model => new ShelfModel<T>
    {
        Items = Pal.Slice(Pal.Contents(_items), 0, _size),
        Version = _version,
    };

    [Spec] public Seq<T> Items => Model.Items;
    [Spec] public SpecInt SpecCount => Model.Items.Length;
    [Spec] public SpecInt SpecVersion => Model.Version;

    [Ensures("@this.SpecCount == 0")]
    public Shelf()
    {
        _items = new T[0];
    }

    [Ensures("Result == (0 <= index && index < @this.SpecCount)")]
    [Ensures("Pal.Implies(Result, Pal.Same(value, @this.Items[index]))")]
    public bool TryGet(int index, out T value)
    {
        if ((uint)index < (uint)_size)
        {
            value = _items[index];
            return true;
        }
        value = default!;
        return false;
    }

    // R35.2. An `out var` in a returned expression is declared before the `return`.
    [Ensures("Result == (0 <= index && index < @this.SpecCount)")]
    public bool Has(int index)
    {
        return TryGet(index, out T? value) || false;
    }

    [Ensures("@this.SpecCount == 0")]
    public void Clear()
    {
        _size = 0;
        _version++;
    }

    // R35.1. `ThrowIfNull` with a constant parameter name is a null check.
    [Throws(typeof(ArgumentNullException), "Pal.IsNull(pair.Key)")]
    [Ensures("Pal.Same(Result, pair.Value)")]
    public static T ValueOf(KeyValuePair<string, T> pair)
    {
        ArgumentNullException.ThrowIfNull(pair.Key, nameof(pair));
        return pair.Value;
    }

    // R35.7. A type test of `object` at a type parameter.
    [Ensures("Result == Pal.IsA<T>(o)")]
    public static bool Is(object? o) => o is T;

    // R35.11. `ThrowIfNull` of a non-nullable `object` tests it.
    [Throws(typeof(ArgumentNullException), "Pal.IsNull(o)")]
    [Ensures("!Pal.IsNull(o)")]
    public static void NotNull(object o) => ArgumentNullException.ThrowIfNull(o);

    [Throws(typeof(ArgumentNullException), "Pal.IsNull(o)")]
    [Throws(typeof(ArgumentException), "!Pal.IsNull(o) && !Pal.IsA<T>(o)")]
    [Ensures("Pal.IsA<T>(o) && Pal.Same(Result, Pal.Unbox<T>(o))")]
    public static T Take(object o)
    {
        ArgumentNullException.ThrowIfNull(o);
        if (o is not T t)
        {
            throw new ArgumentException();
        }
        return t;
    }

    [Requires("Pal.IsA<T>(o)")]
    [Ensures("Pal.Same(Result, Pal.Unbox<T>(o))")]
    public static T Cast(object o) => (T)o;

    // A box of a non-null value is a value of its type.
    [Requires("!Pal.IsNull(x)")]
    [Ensures("Result")]
    public static bool RoundTrip(T x)
    {
        object? o = x;
        return o is T;
    }

    [Ensures("ReferenceEquals(Result._shelf, @this) && Result._version == @this.SpecVersion && Result._index == 0")]
    public Enumerator GetEnumerator() => new Enumerator(this);

    // R35.3. A wrapping struct is created by its constructor.
    [Ensures("ReferenceEquals(Result._inner._shelf, @this) && Result._inner._version == @this.SpecVersion && Result._inner._index == 0")]
    public Wrapper GetWrapper() => new Wrapper(this);

    // R35.6. A collection interface is an `obj`, and the view it returns is boxed.
    [Ensures("Pal.Implies(@this.SpecCount != 0, Pal.Exists((Shelf<T>.Enumerator e) => Pal.Boxes(Result, e) && ReferenceEquals(e._shelf, @this) && e._version == @this.SpecVersion && e._index == 0))")]
    IEnumerator<T> IEnumerable<T>.GetEnumerator() =>
        _size == 0 ? Helpers.Empty<T>() : GetEnumerator();

    IEnumerator IEnumerable.GetEnumerator() => GetEnumerator();

    [Ensures("Pal.Exists((Shelf<T> s) => Pal.Boxes(Result, s) && ReferenceEquals(s, @this))")]
    public IEnumerable<T> AsEnumerable() => this;

    public struct Enumerator : IEnumerator<T>
    {
        private readonly Shelf<T> _shelf;
        private readonly int _version;
        private int _index;

        [Spec] internal bool SpecFresh => _version == _shelf.SpecVersion;
        [Spec] internal SpecInt SpecIndex => _index;
        // R35.5. An auto-property, read by a `[Spec]` property a wrapper's contract expands.
        [Spec] internal T SpecCurrent => Current;

#pragma warning disable CS8618 // `Current` is `default` until `MoveNext` sets it, as in the runtime's enumerators.
        [Ensures("ReferenceEquals(@this._shelf, shelf) && @this._version == shelf.SpecVersion && @this._index == 0")]
        internal Enumerator(Shelf<T> shelf)
        {
            _shelf = shelf;
            _version = shelf._version;
        }
#pragma warning restore CS8618

        public T Current { get; private set; }

        object? IEnumerator.Current => Current;

        [Requires("0 <= @this._index")]
        [Throws(typeof(InvalidOperationException), "@this._version != @this._shelf.SpecVersion")]
        [Ensures("@this._version == @this._shelf.SpecVersion && 0 <= @this._index")]
        [Ensures("Result == (Pal.Old(@this._index) < @this._shelf.SpecCount)")]
        [Ensures("Pal.Implies(Result, @this._index == Pal.Old(@this._index) + 1 && Pal.Same(@this.Current, @this._shelf.Items[Pal.Old(@this._index)]))")]
        [Ensures("Pal.Implies(!Result, @this._index == Pal.Old(@this._index))")]
        public bool MoveNext()
        {
            Shelf<T> shelf = _shelf;
            if (_version != shelf._version)
            {
                throw new InvalidOperationException();
            }
            if ((uint)_index < (uint)shelf._size)
            {
                Current = shelf._items[_index];
                _index++;
                return true;
            }
            return false;
        }

        [Throws(typeof(InvalidOperationException), "@this._version != @this._shelf.SpecVersion")]
        [Ensures("@this._version == @this._shelf.SpecVersion && @this._index == 0")]
        void IEnumerator.Reset()
        {
            if (_version != _shelf._version)
            {
                throw new InvalidOperationException();
            }
            _index = 0;
            Current = default!;
        }

        public void Dispose() { }
    }

    public struct Wrapper : IEnumerator<T>
    {
        internal Shelf<T>.Enumerator _inner;

        // R35.3. Built by a method of the borrowed object's class.
        [Ensures("@this._inner.SpecFresh && @this._inner.SpecIndex == 0")]
        internal Wrapper(Shelf<T> shelf) => _inner = shelf.GetEnumerator();

        // R35.5. The held struct's auto-property is its backing field.
        [Ensures("Pal.Same(Result, @this._inner.SpecCurrent)")]
        public T Current => _inner.Current;

        [Ensures("Pal.Boxes(Result, @this._inner.SpecCurrent)")]
        object? IEnumerator.Current => Current;

        [Requires("0 <= @this._inner.SpecIndex")]
        [Throws(typeof(InvalidOperationException), "!@this._inner.SpecFresh")]
        [Ensures("@this._inner.SpecFresh && 0 <= @this._inner.SpecIndex")]
        public bool MoveNext() => _inner.MoveNext();

        // R35.4. A generic helper forwarding to the struct's `Reset` is that call.
        [Throws(typeof(InvalidOperationException), "!@this._inner.SpecFresh")]
        [Ensures("@this._inner.SpecFresh && @this._inner.SpecIndex == 0")]
        void IEnumerator.Reset() => Helpers.Reset(ref _inner);

        [Ensures("true")]
        public readonly void Dispose() { }
    }
}

internal static class Helpers
{
    internal static void Reset<E>(ref E enumerator) where E : IEnumerator => enumerator.Reset();
    internal static IEnumerator<T> Empty<T>() => ((IEnumerable<T>)Array.Empty<T>()).GetEnumerator();
}
