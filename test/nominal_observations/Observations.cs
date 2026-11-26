using System;
using System.Collections;
using System.Collections.Generic;
using PalLang;

[assembly: TranslateAnnotatedOnly]

[Spec]
public struct PacketModel<T>
{
    public Seq<T> Items;
    public IComparer<T> Order;
}

public class Packet<T> : IEnumerable<T>
{
    private T item;
    private IComparer<T> order;

    [Model, Refine("Result.Items.Length == 1")]
    private PacketModel<T> Model => new PacketModel<T> { Items = Pal.Snoc(Pal.EmptySeq<T>(), item), Order = order };
    [Spec, EnumerationModel] public virtual Seq<T> Items => Model.Items;
    [Spec] public virtual IComparer<T> Order => Model.Order;

    [Ensures("@this.Items.Length == 1 && Pal.Same(@this.Items[0], item) && Pal.Same(@this.Order, comparer)")]
    public Packet(T item, IComparer<T> comparer)
    {
        this.item = item;
        order = comparer;
    }

    [EnumerationObservation(nameof(Items), Length = true)]
    public virtual int Count => 1;

    [EnumerationObservation(nameof(Order))]
    public virtual IComparer<T> Comparer => order;

    [Frac("p")]
    [Requires("index >= 0 && index + @this.Items.Length <= Pal.Contents(array).Length")]
    [Ensures("Pal.Contents(array) == Pal.Splice(Pal.Old(Pal.Contents(array)), index, index + @this.Items.Length, @this.Items)")]
    public virtual void CopyTo(T[] array, int index) { array[index] = item; }

    [Ensures("Result.Items.Length == 0 && Pal.Same(Result.Order, comparer)")]
    [return: Exactly(typeof(Packet<>.Empty))]
    public Packet<T> EmptyView(IComparer<T> comparer) => new Empty(item, this, comparer);

    [Ensures("Pal.Yielded<T>() == @this.Items")]
    public virtual IEnumerator<T> GetEnumerator()
    {
        yield return item;
    }
    IEnumerator IEnumerable.GetEnumerator() => GetEnumerator();

    [Requires("other.Items.Length >= 0")]
    [Ensures("Result == Pal.Same(@this.Order, other.Order)")]
    [Ensures("other.Order == Pal.Old(other.Order)")]
    [Requires("other.Items.Length >= 0", At = typeof(Packet<>.Empty))]
    [Ensures("Result == Pal.Same(@this.Order, other.Order)", At = typeof(Packet<>.Empty))]
    [Ensures("other.Order == Pal.Old(other.Order)", At = typeof(Packet<>.Empty))]
    private bool SameOrder(Packet<T> other)
    {
        return Comparer == other.Comparer || Comparer == other.Comparer;
    }

    [Ensures("Result == (Pal.Contents(input).Length > 0)")]
    [Ensures("Result == (Pal.Contents(input).Length > 0)", At = typeof(Packet<>.Empty))]
    private bool AnySnapshot(IEnumerable<T> input)
    {
        using IEnumerator<T> iterator = input.GetEnumerator();
        return iterator.MoveNext();
    }

    [Ensures("Result == (input is Packet<T>)")]
    [Ensures("Result == (input is Packet<T>)", At = typeof(Packet<>.Empty))]
    public bool CompareObserved(IEnumerable<T> input)
    {
        var candidate = input as Packet<T>;
        if (candidate != null && SameOrder(candidate))
        {
            bool same = SameOrder(candidate);
            Pal.Assert(same == Pal.Same(this.Order, candidate.Order));
            return true;
        }
        bool nonempty = AnySnapshot(input);
        Pal.Assert(nonempty == (Pal.Contents(input).Length > 0));
        if (input is Packet<T> again) return true;
        return false;
    }

    // Different ownership and a different scalar observation from the source.
    public sealed class Empty : Packet<T>
    {
        private readonly Packet<T> source;
        private readonly IComparer<T> selected;
        private int cache;
        [Spec] public override Seq<T> Items => Pal.Slice(source.Items, 0, 0);
        [Spec] public override IComparer<T> Order => selected;

        [Ensures("ReferenceEquals(@this.source, owner) && Pal.Same(@this.selected, comparer)")]
        public Empty(T value, Packet<T> owner, IComparer<T> comparer) : base(value, comparer)
        {
            source = owner;
            selected = comparer;
            cache = -1;
        }

        [Ensures("true")]
        public override int Count { get { cache = 0; return cache; } }
        [Ensures("true")]
        public override IComparer<T> Comparer => selected;
        [Ensures("Pal.Yielded<T>() == @this.Items")]
        public override IEnumerator<T> GetEnumerator() { yield break; }

        [Frac("p")]
        [Requires("index >= 0 && index + @this.Items.Length <= Pal.Contents(array).Length")]
        [Ensures("Pal.Contents(array) == Pal.Splice(Pal.Old(Pal.Contents(array)), index, index + @this.Items.Length, @this.Items)")]
        public override void CopyTo(T[] array, int index) { }

        [Ensures("Result == (input is Packet<T>)")]
        public bool CompareHere(IEnumerable<T> input)
        {
            var candidate = input as Packet<T>;
            if (candidate != null)
            {
                bool same = SameOrder(candidate);
                Pal.Assert(same == Pal.Same(this.Order, candidate.Order));
                return true;
            }
            bool nonempty = AnySnapshot(input);
            Pal.Assert(nonempty == (Pal.Contents(input).Length > 0));
            return false;
        }
    }
}

public static class ObservationClient
{
    [Ensures("Result == (source is Packet<T>)")]
    public static bool Observe<T>(IEnumerable<T> source)
    {
        Pal.Assert(Pal.Contents(source).Length >= 0);
        var candidate = source as Packet<T>;
        if (candidate != null)
        {
            int count = candidate.Count;
            IComparer<T> comparer = candidate.Comparer;
            Pal.Assert(count == candidate.Items.Length && Pal.Same(comparer, candidate.Order));
            int again = candidate.Count;
            Pal.Assert(again == count);
            return true;
        }
        return false;
    }

    [Ensures("Result == (source is Packet<T>)")]
    public static bool ObservePattern<T>(IEnumerable<T> source)
    {
        if (source is Packet<T> candidate)
        {
            int count = candidate.Count;
            IComparer<T> comparer = candidate.Comparer;
            Pal.Assert(count == candidate.Items.Length && Pal.Same(comparer, candidate.Order));
            return true;
        }
        return false;
    }

    [Ensures("Result")]
    public static bool Ordinary<T>(T item, IComparer<T> comparer)
    {
        var packet = new Packet<T>(item, comparer);
        bool hit = Observe(packet);
        bool repeated = ObservePattern(packet);
        int count = packet.Count;
        IComparer<T> actual = packet.Comparer;
        return hit && repeated && count == 1 && actual == comparer;
    }

    [Ensures("Result")]
    public static bool View<T>(T item, IComparer<T> first, IComparer<T> second)
    {
        var packet = new Packet<T>(item, first);
        var view = packet.EmptyView(second);
        bool hit = Observe(view);
        bool repeated = ObservePattern(view);
        int count = view.Count;
        IComparer<T> actual = view.Comparer;
        return hit && repeated && count == 0 && actual == second && packet.Count == 1 && packet.Comparer == first;
    }
}
