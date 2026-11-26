// EXPECT: PALCS0866
using System;
using System.Collections;
using System.Collections.Generic;
using PalLang;
[assembly: TranslateAnnotatedOnly]

// The public int Current is NOT the actual long interface slot. An implicit
// int-to-long conversion in a proof traversal must not disguise that mismatch.
[Invariant("_items.Length == 1")]
public sealed class Dual : IEnumerable<long>
{
    private long[] _items;
    [Model, Refine("Result.Length == 1")]
    private Seq<long> Model => Pal.Contents(_items);
    [Ensures("true")]
    public Dual() { _items = new long[1]; _items[0] = 99; }
    [Ensures("Result == 1")]
    public int Count => _items.Length;
    [Frac("p"), Requires("index == 0 && Pal.Contents(array).Length == 1"), Ensures("true")]
    public void CopyTo(long[] array, int index) => Array.Copy(_items, 0, array, index, 1);
    [Ensures("ReferenceEquals(Result._owner, @this)")]
    public Enumerator GetEnumerator() => new Enumerator(this);
    IEnumerator<long> IEnumerable<long>.GetEnumerator() => GetEnumerator();
    IEnumerator IEnumerable.GetEnumerator() => GetEnumerator();

    [EnumerationProtocol, Ensures("true")]
    public IEnumerable<long> Trace()
    {
        Enumerator e = GetEnumerator();
        while (e.MoveNext())
        {
            Pal.Decreases(1);
            yield return e.Current;
        }
        e.Dispose();
    }

    [EnumerationState(nameof(Ready), nameof(Remaining), nameof(Value), nameof(Valid))]
    public struct Enumerator : IEnumerator<int>, IEnumerator<long>
    {
        private readonly Dual _owner;
        [Spec] public bool Ready => true;
        [Spec] public Seq<int> Remaining => Pal.EmptySeq<int>();
        [Spec] public int Value => 99;
        [Spec] public bool Valid => true;
        [Ensures("ReferenceEquals(@this._owner, owner)")]
        internal Enumerator(Dual owner) { _owner = owner; }
        [Ensures("true")] public bool MoveNext() => false;
        [Ensures("Result == 99")] public int Current => 99;
        long IEnumerator<long>.Current => 0;
        object IEnumerator.Current => Current;
        public void Reset() { }
        [Ensures("true")] public void Dispose() { }
    }
}

public static class Client
{
    [Ensures("true")]
    public static bool Test(IEnumerable<long> source)
    {
        if (source is Dual target) return target.Count == 1;
        return false;
    }
    [Ensures("true")]
    public static bool Run()
    {
        Dual source = new Dual();
        return Test(source);
    }
}
