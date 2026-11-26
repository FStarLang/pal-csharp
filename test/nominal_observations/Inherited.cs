using System.Collections.Generic;
using PalLang;

public class Inherited<T>
{
    protected T item;
    protected IComparer<T> order;
    [Model, Refine("Result.Items.Length == 1")]
    private PacketModel<T> Model => new PacketModel<T> { Items = Pal.Snoc(Pal.EmptySeq<T>(), item), Order = order };
    [Spec] public virtual Seq<T> Items => Model.Items;
    [Spec] public virtual IComparer<T> Order => Model.Order;

    [Ensures("@this.Items.Length == 1 && Pal.Same(@this.Order, comparer)")]
    public Inherited(T value, IComparer<T> comparer) { item = value; order = comparer; }

    [Ensures("Result == @this.Items.Length")]
    protected virtual int CountCore => 1;
    [EnumerationObservation(nameof(Items), Length = true)]
    public int Count => CountCore;
    [EnumerationObservation(nameof(Order))]
    public IComparer<T> Comparer => order;

    [return: Exactly(typeof(Inherited<>.Window))]
    [Ensures("Result.Items.Length == 0 && Pal.Same(Result.Order, comparer)")]
    public Inherited<T> Select(IComparer<T> comparer) => new Window(item, this, comparer);

    [Requires("Pal.Contents(input).Length == 1")]
    [Requires("Pal.Contents(input).Length == 1", At = typeof(Inherited<>.Window))]
    [Ensures("Pal.Same(Result, Pal.Contents(input)[0])")]
    [Ensures("Pal.Same(Result, Pal.Contents(input)[0])", At = typeof(Inherited<>.Window))]
    private T First(IEnumerable<T> input)
    {
        using IEnumerator<T> e = input.GetEnumerator();
        bool more = e.MoveNext();
        return e.Current;
    }

    [Ensures("Pal.Same(Result, input.Items[0])")]
    [Ensures("Pal.Same(Result, input.Items[0])", At = typeof(Inherited<>.Window))]
    public T Adapt([Exactly(typeof(Packet<>))] IEnumerable<T> input) => First(input);

    public sealed class Window : Inherited<T>
    {
        private readonly Inherited<T> source;
        [Spec] public override Seq<T> Items => Pal.Slice(source.Items, 0, 0);
        [Spec] public override IComparer<T> Order => order;
        [Ensures("Result == @this.Items.Length")]
        protected override int CountCore => 0;
        [Ensures("ReferenceEquals(@this.source, owner) && Pal.Same(@this.Order, comparer)")]
        public Window(T value, Inherited<T> owner, IComparer<T> comparer) : base(value, comparer)
        { source = owner; }
    }
}

public static class InheritedClient
{
    [Ensures("Result")]
    public static bool Run<T>(T value, IComparer<T> first, IComparer<T> second)
    {
        var source = new Inherited<T>(value, first);
        var view = source.Select(second);
        int count = view.Count;
        IComparer<T> actual = view.Comparer;
        var input = new Packet<T>(value, first);
        T observed = view.Adapt(input);
        T ordinary = source.Adapt(input);
        Pal.Assert(Pal.Same(observed, value) && Pal.Same(ordinary, value));
        return count == 0 && actual == second && source.Count == 1;
    }
}
