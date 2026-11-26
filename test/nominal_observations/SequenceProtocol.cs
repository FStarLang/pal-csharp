using System.Collections;
using System.Collections.Generic;
using PalLang;

public class Stream<T> : IEnumerable<T>
{
    private T item;
    [Model, Refine("Result.Length == 1")]
    private Seq<T> Model => Pal.Snoc(Pal.EmptySeq<T>(), item);
    [Spec, EnumerationModel] public Seq<T> Elements => Model;

    [Ensures("@this.Elements.Length == 1 && Pal.Same(@this.Elements[0], value)")]
    public Stream(T value) { item = value; }
    [EnumerationObservation(nameof(Elements), Length = true)]
    [Ensures("Result == @this.Elements.Length")] public int Count => 1;
    [Spec] public bool Kind => true;
    [EnumerationObservation(nameof(Kind))] public bool Flag => true;
    [Frac("p")]
    [Requires("index >= 0 && index + @this.Elements.Length <= Pal.Contents(array).Length")]
    [Ensures("Pal.Contents(array) == Pal.Splice(Pal.Old(Pal.Contents(array)), index, index + @this.Elements.Length, @this.Elements)")]
    public void CopyTo(T[] array, int index) { array[index] = item; }

    // These concrete facts imply Ready, full Pending, empty CurrentItems and
    // invalid Current. No logical default(T) is needed.
    [Ensures("ReferenceEquals(Result.owner, @this) && Result.index == 0")]
    public Cursor GetEnumerator() => new Cursor(this);
    IEnumerator<T> IEnumerable<T>.GetEnumerator() => GetEnumerator();
    IEnumerator IEnumerable.GetEnumerator() => GetEnumerator();

    [EnumerationProtocol, Frac("p")]
    [Ensures("@this.Elements.Length == 1 && @this.Kind")]
    [Ensures("Pal.Yielded<T>().Length == 1 && Pal.Same(Pal.Yielded<T>()[0], @this.Elements[0])")]
    public IEnumerable<T> Trace()
    {
        Cursor e = GetEnumerator();
        while (e.MoveNext())
        {
            Pal.Invariant(e.Ready);
            Pal.Invariant(Pal.Yielded<T>().Length == (e.Index == 0 ? 0 : 1));
            Pal.Invariant(Pal.Implies(Pal.Yielded<T>().Length == 1,
                Pal.Same(Pal.Yielded<T>()[0], this.Elements[0])));
            Pal.Decreases(e.Pending.Length);
            yield return e.Current;
        }
        e.Dispose();
    }

    [EnumerationState(nameof(Ready), nameof(Pending), nameof(CurrentItems), nameof(Valid))]
    public struct Cursor : IEnumerator<T>
    {
        private readonly Stream<T> owner;
        private int index;
        [Spec] public SpecInt Index => index;
        [Spec] public bool Ready => 0 <= index && index <= 2;
        [Spec] public bool Valid => index == 1;
        [Spec] public Seq<T> Pending => index == 0 ? owner.Elements : Pal.EmptySeq<T>();
        [Spec] public Seq<T> CurrentItems => index == 1 ? owner.Elements : Pal.EmptySeq<T>();

        [Ensures("ReferenceEquals(@this.owner, source) && @this.Index == 0")]
        internal Cursor(Stream<T> source) { owner = source; index = 0; }

        [Requires("@this.Ready")]
        [Ensures("Result == (Pal.Old(@this.Index) == 0) && @this.Index == (Result ? 1 : 2)")]
        public bool MoveNext()
        {
            if (index == 0) { index = 1; return true; }
            index = 2;
            return false;
        }
        [Ensures("Pal.Same(Result, @this.owner.Elements[0])")]
        public T Current => owner.item;
        object IEnumerator.Current => Current!;
        [Ensures("@this.Index == 0")] public void Reset() { index = 0; }
        [Ensures("true")] public void Dispose() { }
    }
}

public static class SequenceProtocolClient
{
    [Ensures("Result == ((input is Stream<T>) && Pal.Contents(input).Length > 0)")]
    public static bool Consume<T>(IEnumerable<T> input)
    {
        var source = input as Stream<T>;
        if (source != null)
        {
            Pal.Assert(Pal.Contents(input).Length == 1);
            Stream<T>.Cursor cursor = source.GetEnumerator();
            bool moved = cursor.MoveNext();
            if (moved)
            {
                T value = cursor.Current;
                Pal.Assert(Pal.Same(value, Pal.Contents(input)[0]));
            }
            cursor.Dispose();
            return moved;
        }
        return false;
    }

    // Early scope exit releases the retained resource, but must not manufacture
    // an executable Dispose call that the C# program did not perform.
    [Ensures("Result == ((input is Stream<T>) && Pal.Contents(input).Length > 0)")]
    public static bool Partial<T>(IEnumerable<T> input)
    {
        var source = input as Stream<T>;
        if (source != null)
        {
            var cursor = source.GetEnumerator();
            return cursor.MoveNext();
        }
        return false;
    }

    [Ensures("Result")]
    public static bool Hit<T>(T value)
    {
        var source = new Stream<T>(value);
        bool result = Consume(source);
        Pal.Assert(source.Elements.Length == 1 && Pal.Same(source.Elements[0], value));
        bool partial = Partial(source);
        Pal.Assert(source.Elements.Length == 1 && Pal.Same(source.Elements[0], value));
        return result && partial;
    }

    [Ensures("Result")]
    public static bool Miss<T>(T value)
    {
        var source = new Stream<T>(value);
        bool result = ObservationClient.Observe(source);
        Pal.Assert(source.Elements.Length == 1 && Pal.Same(source.Elements[0], value));
        return !result && source.Count == 1;
    }
}
