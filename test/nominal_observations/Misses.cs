using System.Collections;
using System.Collections.Generic;
using PalLang;

// Nonsealed and unrelated to the cast target. The client uses a fresh instance,
// not an unchecked static-type claim about its subclasses or interface map.
public class Cargo<T> : IEnumerable<T>
{
    private T item;
    [Model, Refine("Result.Length == 1")]
    private Seq<T> Model => Pal.Snoc(Pal.EmptySeq<T>(), item);
    [Spec, EnumerationModel] public Seq<T> Elements => Model;

    [Ensures("@this.Elements.Length == 1 && Pal.Same(@this.Elements[0], value)")]
    public Cargo(T value) { item = value; }

    [Ensures("@this.Elements.Length == 1 && Pal.Same(@this.Elements[0], value)")]
    public void Replace(T value) { item = value; }

    [Ensures("Result == @this.Elements.Length")]
    public int Count => 1;

    [Frac("p")]
    [Requires("index >= 0 && index + @this.Elements.Length <= Pal.Contents(array).Length")]
    [Ensures("Pal.Contents(array) == Pal.Splice(Pal.Old(Pal.Contents(array)), index, index + @this.Elements.Length, @this.Elements)")]
    public void CopyTo(T[] array, int index) { array[index] = item; }

    [Ensures("Pal.Yielded<T>() == @this.Elements")]
    public IEnumerator<T> GetEnumerator() { yield return item; }
    IEnumerator IEnumerable.GetEnumerator() => GetEnumerator();
}

public static class MissClient
{
    [Ensures("Result")]
    public static bool Ordinary<T>(T value, IComparer<T> comparer)
    {
        var receiver = new Packet<T>(value, comparer);
        var source = new Cargo<T>(value);
        source.Replace(value);
        bool first = ObservationClient.Observe(source);
        bool second = ObservationClient.ObservePattern(source);
        bool helper = receiver.CompareObserved(source);
        Pal.Assert(source.Elements.Length == 1 && Pal.Same(source.Elements[0], value));
        return !first && !second && !helper && source.Count == 1;
    }

    [Ensures("Result")]
    public static bool View<T>(T value, IComparer<T> comparer)
    {
        var receiver = new Packet<T>(value, comparer);
        var view = receiver.EmptyView(comparer);
        var source = new Cargo<T>(value);
        bool result = view.CompareObserved(source);
        Pal.Assert(source.Elements.Length == 1 && Pal.Same(source.Elements[0], value));
        return !result && source.Count == 1;
    }
}
