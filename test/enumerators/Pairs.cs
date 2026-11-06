using System;
using System.Collections;
using System.Collections.Generic;
using PalLang;

// R28: a borrowing struct nested in a class nested in a generic class, whose `Current`
// is a pair. R29.3: that class borrows too, and is cached by `??=` (R29.3b). R29.1: a
// KeyValuePair is a pair.
[Spec]
public struct PairsModel<K, V>
{
    public Seq<(K, V)> Items;
    public SpecInt Version;
}

[Invariant("0 <= _size")]
[Invariant("_size <= _nodes.Length")]
public class Pairs<K, V>
{
    private (K, V)[] _nodes;
    private int _size;
    [Wrapping] private int _version;
    private View? _view;

    [Model]
    private PairsModel<K, V> Model => new PairsModel<K, V>
    {
        Items = Pal.Slice(Pal.Contents(_nodes), 0, _size),
        Version = _version,
    };

    [Spec] public Seq<(K, V)> Items => Model.Items;
    [Spec] public SpecInt SpecCount => Model.Items.Length;
    [Spec] public SpecInt SpecVersion => Model.Version;

    [Ensures("@this.SpecCount == 0")]
    public Pairs()
    {
        _nodes = new (K, V)[0];
    }

    [Ensures("@this.SpecCount == 0")]
    public void Clear()
    {
        _size = 0;
        _version++;
    }

    [Ensures("Result == @this.SpecCount")]
    public int Count => _size;

    [Ensures("ReferenceEquals(Result._pairs, @this)")]
    public View Items2 => _view ??= new View(this);

    [Requires("0 < @this.SpecCount")]
    [Ensures("Pal.Same(Result.Key, @this.Items[0].Item1) && Pal.Same(Result.Value, @this.Items[0].Item2)")]
    public KeyValuePair<K, V> First() => KeyValuePair.Create(_nodes[0].Item1, _nodes[0].Item2);

    [Ensures("Pal.Same(Result.Key, k) && Pal.Same(Result.Value, v)")]
    public static KeyValuePair<K, V> Make(K k, V v)
    {
        var p = new KeyValuePair<K, V>(k, v);
        return new KeyValuePair<K, V>(p.Key, p.Value);
    }

    public sealed class View
    {
        internal readonly Pairs<K, V> _pairs;

        [Ensures("ReferenceEquals(@this._pairs, pairs)")]
        internal View(Pairs<K, V> pairs) => _pairs = pairs;

        [Ensures("Result == @this._pairs.SpecCount")]
        public int Count => _pairs.Count;

        [Ensures("ReferenceEquals(Result._pairs, @this._pairs) && Result._version == @this._pairs.SpecVersion && Result._index == 0")]
        public Enumerator GetEnumerator() => new Enumerator(_pairs);

        // R29.5: the array is named after the call that refolds its owner.
        [Requires("@this._pairs.SpecCount <= Pal.Contents(array).Length")]
        [Ensures("Pal.Contents(array) == Pal.Splice(Pal.Old(Pal.Contents(array)), 0, @this._pairs.SpecCount, @this._pairs.Items)")]
        public void CopyTo((K, V)[] array) => Array.Copy(_pairs._nodes, 0, array, 0, _pairs.Count);

        [Throws(typeof(NotSupportedException))]
        [Ensures("false")]
        public void Clear() => throw new NotSupportedException();

        public struct Enumerator : IEnumerator
        {
            private readonly Pairs<K, V> _pairs;
            private readonly int _version;
            private int _index;
            private (K, V) _current;

            [Ensures("ReferenceEquals(@this._pairs, pairs) && @this._version == pairs.SpecVersion && @this._index == 0")]
            internal Enumerator(Pairs<K, V> pairs)
            {
                _pairs = pairs;
                _version = pairs._version;
                _index = 0;
                _current = default;
            }

            [Requires("0 <= @this._index && @this._index <= @this._pairs.SpecCount")]
            [Throws(typeof(InvalidOperationException), "@this._version != @this._pairs.SpecVersion")]
            [Ensures("Result == (Pal.Old(@this._index) < @this._pairs.SpecCount)")]
            [Ensures("Pal.Implies(Result, @this._index == Pal.Old(@this._index) + 1 && Pal.Same(@this._current, @this._pairs.Items[Pal.Old(@this._index)]))")]
            public bool MoveNext()
            {
                if (_version != _pairs._version) throw new InvalidOperationException();
                if (_index < _pairs._size)
                {
                    _current = _pairs._nodes[_index];
                    _index++;
                    return true;
                }
                return false;
            }

            [Ensures("Pal.Same(Result, @this._current)")]
            public (K, V) Current => _current;

            object IEnumerator.Current => _current;

            void IEnumerator.Reset() => _index = 0;
        }
    }
}
