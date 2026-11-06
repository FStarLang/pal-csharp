using System;
using System.Collections;
using PalLang;

// R28: a borrowing struct nested in a class nested in a generic class, whose `Current`
// is a pair.
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

    public sealed class View
    {
        internal readonly Pairs<K, V> _pairs;

        internal View(Pairs<K, V> pairs) => _pairs = pairs;

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
