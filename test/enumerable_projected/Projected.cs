using System;
using System.Collections;
using System.Collections.Generic;
using PalLang;

[assembly: TranslateAnnotatedOnly]

[Spec]
public struct ParcelModel<T, TTag>
{
    public Seq<T> Values;
    public Seq<TTag> Tags;
    public SpecInt Revision;
}

[Invariant("_items.Length == 1 && _tags.Length == 1 && _revision >= 0")]
public sealed class Parcel<T, TTag> : IEnumerable<T>
{
    private T[] _items;
    private TTag[] _tags;
    private int _revision;

    [Model]
    [Refine("Result.Values.Length == 1 && Result.Tags.Length == 1 && Result.Revision >= 0")]
    private ParcelModel<T, TTag> Model => new ParcelModel<T, TTag>
    {
        Values = Pal.Contents(_items),
        Tags = Pal.Contents(_tags),
        Revision = _revision,
    };

    [Spec, EnumerationModel] public Seq<T> Elements => Model.Values;
    [Spec] public TTag Tag => Model.Tags[0];
    [Spec] public SpecInt Revision => Model.Revision;

    [Ensures("@this.Elements.Length == 1 && Pal.Same(@this.Elements[0], value) && Pal.Same(@this.Tag, tag) && @this.Revision == 5")]
    public Parcel(T value, TTag tag)
    {
        _items = new T[1];
        _items[0] = value;
        _tags = new TTag[1];
        _tags[0] = tag;
        _revision = 5;
    }

    [Ensures("Result == @this.Elements.Length")]
    public int Count => _items.Length;

    [Frac("p")]
    [Requires("index >= 0 && index + @this.Elements.Length <= Pal.Contents(array).Length")]
    [Ensures("Pal.Contents(array) == Pal.Splice(Pal.Old(Pal.Contents(array)), index, index + @this.Elements.Length, @this.Elements)")]
    public void CopyTo(T[] array, int index) =>
        Array.Copy(_items, 0, array, index, _items.Length);

    [Ensures("Pal.Yielded<T>().Length == 1 && Pal.Same(Pal.Yielded<T>()[0], @this.Elements[0])")]
    public IEnumerator<T> GetEnumerator()
    {
        yield return _items[0];
    }
    IEnumerator IEnumerable.GetEnumerator() => GetEnumerator();

    // This is intentionally mutable and changes information omitted by Elements.
    [Ensures("@this.Elements == Pal.Old(@this.Elements) && @this.Revision == 9")]
    public void ChangeRevision() { _revision = 9; }
}

public static class Projected
{
    [Requires("Pal.Contents(other).Length == 1")]
    [Ensures("Result == (other is Parcel<T, int>)")]
    public static bool Test<T>(IEnumerable<T> other, bool quick)
    {
        var candidate = other as Parcel<T, int>;
        if (candidate != null)
        {
            // Nested early return: evaluate before restoring the concrete loan.
            if (quick) return candidate.Count == 1;
            Pal.Assert(candidate.Revision >= 0);
            return candidate.Count == 1;
        }
        using IEnumerator<T> e = other.GetEnumerator();
        bool more = e.MoveNext();
        T item = e.Current;
        return !more;
    }

    [Requires("Pal.Contents(other).Length == 1")]
    [Ensures("Result == (other is Parcel<T, int>)")]
    public static bool Mixed<T>(IEnumerable<T> other, bool quick)
    {
        bool result = false;
        var candidate = other as Parcel<T, int>;
        if (null != candidate)
        {
            if (quick) return candidate.Count == 1;
            result = candidate.Count == 1;
        }
        return result;
    }

    [Requires("Pal.Contents(other).Length == 1")]
    [Ensures("Result == (other is Parcel<T, int>)")]
    public static bool PatternEarly<T>(IEnumerable<T> other)
    {
        if (other is Parcel<T, int> candidate) return candidate.Count == 1;
        return false;
    }

    [Ensures("Result == true")]
    public static bool Generic<T>(T value, bool quick)
    {
        Parcel<T, int> source = new Parcel<T, int>(value, 31);
        bool result = Test(source, quick);
        Pal.Assert(Pal.Same(source.Elements[0], value) && source.Tag == 31 && source.Revision == 5);
        return result;
    }

    [Ensures("Result == true")]
    public static bool Successful(bool quick)
    {
        Parcel<int, int> source = new Parcel<int, int>(7, 31);
        bool result = Test(source, quick);
        bool mixed = Mixed(source, quick);
        bool pattern = PatternEarly(source);
        Pal.Assert(mixed && pattern);
        Pal.Assert(source.Elements[0] == 7 && source.Tag == 31 && source.Revision == 5);
        return result;
    }

    [Ensures("Result == false")]
    public static bool Failed(bool quick)
    {
        // Same generic definition, different nominal instantiation.
        Parcel<int, bool> source = new Parcel<int, bool>(7, true);
        bool result = Test(source, quick);
        bool mixed = Mixed(source, quick);
        bool pattern = PatternEarly(source);
        Pal.Assert(!mixed && !pattern);
        Pal.Assert(source.Elements[0] == 7 && source.Tag == true && source.Revision == 5);
        return result;
    }
}
