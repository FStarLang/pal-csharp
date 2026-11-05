using System;
using System.Collections.Generic;
using System.Diagnostics.CodeAnalysis;
using PalLang;

// §25. A sorted set of keys in the style of dotnet/runtime's `SortedList<TKey,TValue>`,
// verified in place: each rule of the sorted-collections section is exercised by the
// member that names it.
[assembly: TranslateAnnotatedOnly]

[Spec]
public struct SortedKeysModel<T>
{
    public Seq<T> Keys;
    // R25.1. A comparer is a spec value.
    public IComparer<T> Comparer;
}

[Invariant("0 <= _size")]
[Invariant("_size <= _keys.Length")]
// R25.2. `notnull` is accepted and ignored.
public class SortedKeys<T> where T : notnull
{
    private T[] _keys;
    private int _size;
    private readonly IComparer<T> _comparer;
    // R25.3. A field of a type with no mapping is omitted under `TranslateAnnotatedOnly`.
    private View? _view;

    private sealed class View { }

    public void DropView() => _view = null;

    public bool HasView => _view != null;

    [Refine("Pal.StrictlySorted(Result.Comparer, Result.Keys)")]
    [Model]
    private SortedKeysModel<T> Model => new SortedKeysModel<T>
    {
        Keys = Pal.Slice(Pal.Contents(_keys), 0, _size),
        Comparer = _comparer,
    };

    [Spec]
    public Seq<T> SpecKeys => Model.Keys;

    [Spec]
    public SpecInt SpecCount => Model.Keys.Length;

    [Spec]
    public IComparer<T> SpecComparer => Model.Comparer;

    // R25.8 `Array.Empty`; R25.4 `??` on a comparer.
    [Ensures("@this.SpecCount == 0")]
    [Ensures("Pal.IsNull(comparer) ? @this.SpecComparer == Comparer<T>.Default : @this.SpecComparer == comparer")]
    public SortedKeys(IComparer<T>? comparer)
    {
        _keys = Array.Empty<T>();
        _size = 0;
        _comparer = comparer ?? Comparer<T>.Default;
    }

    // R25.7 `ThrowIfNegative`.
    [Throws(typeof(ArgumentOutOfRangeException), "capacity < 0")]
    [Ensures("@this.SpecCount == 0")]
    [Ensures("@this.SpecComparer == Comparer<T>.Default")]
    public SortedKeys(int capacity)
    {
        ArgumentOutOfRangeException.ThrowIfNegative(capacity);
        _keys = new T[capacity];
        _comparer = Comparer<T>.Default;
    }

    // R25.1. `IComparer<T>.Compare` is `Order.compare`.
    [Ensures("Result == (Pal.Compare(c, x, y) < 0)")]
    public static bool Less(IComparer<T> c, T x, T y) => c.Compare(x, y) < 0;

    // R25.4. `== null` on a type parameter is `is_null`.
    [Ensures("Result == Pal.IsNull(x)")]
    public static bool IsMissing(T x) => x == null;

    // R25.5 `Array.BinarySearch`; R25.6 `KeyIndex`; R25.7 `ThrowIfNull`.
    [Throws(typeof(ArgumentNullException), "Pal.IsNull(key)")]
    [Ensures("Result == Pal.KeyIndex(@this.SpecComparer, @this.SpecKeys, key)")]
    public int IndexOf(T key)
    {
        ArgumentNullException.ThrowIfNull(key);
        int i = Array.BinarySearch<T>(_keys, 0, _size, key, _comparer);
        return i >= 0 ? i : -1;
    }

    // R25.6 `LowerBound`: where a missing key would go.
    [Requires("!Pal.IsNull(key)")]
    [Ensures("Pal.KeyIndex(@this.SpecComparer, @this.SpecKeys, key) == -1 ? Result == Pal.LowerBound(@this.SpecComparer, @this.SpecKeys, key) : Result == Pal.KeyIndex(@this.SpecComparer, @this.SpecKeys, key)")]
    public int Position(T key)
    {
        int i = Array.BinarySearch<T>(_keys, 0, _size, key, _comparer);
        return i >= 0 ? i : ~i;
    }

    // R25.9. A message argument is evaluated for no effect.
    [Throws(typeof(ArgumentOutOfRangeException), "index < 0 || index >= @this.SpecCount")]
    [Ensures("0 <= index && index < Pal.Old(@this.SpecCount)")]
    [Ensures("@this.SpecComparer == Pal.Old(@this.SpecComparer)")]
    [Ensures("@this.SpecKeys == Pal.Concat(Pal.Slice(Pal.Old(@this.SpecKeys), 0, index), Pal.Slice(Pal.Old(@this.SpecKeys), index + 1, Pal.Old(@this.SpecCount)))")]
    public void RemoveAt(int index)
    {
        if (index < 0 || index >= _size)
            throw new ArgumentOutOfRangeException(nameof(index), index, "index out of range");
        _size--;
        if (index < _size)
            Array.Copy(_keys, index + 1, _keys, index, _size - index);
        _keys[_size] = default!;
        Pal.Assert(Pal.Slice(Pal.Contents(_keys), 0, _size) ==
            Pal.Concat(Pal.Slice(Pal.Old(this.SpecKeys), 0, index), Pal.Slice(Pal.Old(this.SpecKeys), index + 1, Pal.Old(this.SpecCount))));
    }

    // R25.10. The `if` whose arm moves the receiver does not join.
    [Throws(typeof(ArgumentNullException), "Pal.IsNull(key)")]
    [Ensures("Result == (Pal.KeyIndex(Pal.Old(@this.SpecComparer), Pal.Old(@this.SpecKeys), key) >= 0)")]
    [Ensures("Result ? @this.SpecKeys == Pal.Concat(Pal.Slice(Pal.Old(@this.SpecKeys), 0, Pal.KeyIndex(Pal.Old(@this.SpecComparer), Pal.Old(@this.SpecKeys), key)), Pal.Slice(Pal.Old(@this.SpecKeys), Pal.KeyIndex(Pal.Old(@this.SpecComparer), Pal.Old(@this.SpecKeys), key) + 1, Pal.Old(@this.SpecCount))) : @this.SpecKeys == Pal.Old(@this.SpecKeys)")]
    public bool Remove(T key)
    {
        int i = IndexOf(key);
        if (i >= 0)
            RemoveAt(i);
        return i >= 0;
    }
}
