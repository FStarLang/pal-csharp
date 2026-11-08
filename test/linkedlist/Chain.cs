// R31. A ring of nodes owned by the object they point back to: a cyclic region (R31.1),
// the owner's record in the region's module (R31.2), an invariant that names `@this`
// (R31.3), `SpecRing` (R31.4), the receiver as a region operation's owner (R31.5),
// `x?.F` as a value (R31.6) and the model's refinement (R31.7); unlinking compares the
// owner with `this` (R31.8), clears the node with a typed null (R31.9) and splits the
// write of the entry pointer (R31.10).
using PalLang;

[Spec]
public struct ChainModel<T>
{
    public Seq<Link<T>> Links;
    public Seq<T> Values;
    public SpecInt Size;
}

[Invariant("SpecRing.Ring<Link<T>, Chain<T>>(Pal.Heap<Link<T>>(), first, size, @this)")]
public sealed class Chain<T>
{
    internal Link<T>? first;
    internal int size;

    [Refine("Result.Size >= 0 && Result.Links.Length == Result.Size && Result.Values.Length == Result.Size")]
    [Model]
    private ChainModel<T> Model => new ChainModel<T>
    {
        Links = SpecRing.Nodes<Link<T>>(Pal.Heap<Link<T>>(), first, size),
        Values = SpecRing.Items<Link<T>, T>(Pal.Heap<Link<T>>(), SpecRing.Nodes<Link<T>>(Pal.Heap<Link<T>>(), first, size)),
        Size = size,
    };

    [Spec] public Seq<Link<T>> SpecLinks => Model.Links;
    [Spec] public Seq<T> SpecValues => Model.Values;
    [Spec] public SpecInt SpecSize => Model.Size;

    [Ensures("@this.SpecSize == 0 && @this.SpecValues.Length == 0")]
    public Chain()
    {
    }

    [Ensures("@this.SpecSize == 0 ? Result == null : Result == @this.SpecLinks[@this.SpecSize - 1]")]
    public Link<T>? Back()
    {
        SpecRing.Ends<Link<T>>(Pal.Heap<Link<T>>(), first, size);
        return first?.prev;
    }

    [Open]
    [Requires("SpecRing.Shape<Link<T>>(Pal.Heap<Link<T>>(), @this.first, @this.size) && @this.size < int.MaxValue")]
    [Requires("Pal.InRegion(at) && SpecRing.Pos<Link<T>>(SpecRing.Nodes<Link<T>>(Pal.Heap<Link<T>>(), @this.first, @this.size), at) >= 0")]
    [Requires("Pal.InRegion(nw) && SpecRing.Pos<Link<T>>(SpecRing.Nodes<Link<T>>(Pal.Heap<Link<T>>(), @this.first, @this.size), nw) < 0")]
    [Ensures("@this.first == Pal.Old(@this.first) && @this.size == Pal.Old(@this.size) + 1")]
    [Ensures("SpecRing.Shape<Link<T>>(Pal.Heap<Link<T>>(), @this.first, @this.size) && SpecRing.ViewsKept<Link<T>>(Pal.Old(Pal.Heap<Link<T>>()), Pal.Heap<Link<T>>())")]
    [Ensures("SpecRing.Nodes<Link<T>>(Pal.Heap<Link<T>>(), @this.first, @this.size) == SpecRing.InsertAt(SpecRing.Nodes<Link<T>>(Pal.Old(Pal.Heap<Link<T>>()), Pal.Old(@this.first), Pal.Old(@this.size)), SpecRing.InsIndex<Link<T>>(SpecRing.Nodes<Link<T>>(Pal.Old(Pal.Heap<Link<T>>()), Pal.Old(@this.first), Pal.Old(@this.size)), at), nw)")]
    private void Splice(Link<T> at, Link<T> nw)
    {
        Ghost<SpecHeap<Link<T>>> h0 = Pal.Heap<Link<T>>();
        SpecRing.Neighbours<Link<T>>(h0.Value, first, size, at);
        nw.next = at;
        nw.prev = at.prev;
        Ghost<SpecHeap<Link<T>>> h1 = Pal.Heap<Link<T>>();
        at.prev!.next = nw;
        Ghost<SpecHeap<Link<T>>> h2 = Pal.Heap<Link<T>>();
        at.prev = nw;
        SpecRing.Inserted<Link<T>>(h0.Value, h1.Value, h2.Value, Pal.Heap<Link<T>>(), first, size, at, nw);
        size++;
    }

    [Open]
    [Requires("@this.first == null && @this.size == 0 && Pal.InRegion(nw)")]
    [Ensures("@this.first == nw && @this.size == 1")]
    [Ensures("SpecRing.Shape<Link<T>>(Pal.Heap<Link<T>>(), @this.first, @this.size) && SpecRing.ViewsKept<Link<T>>(Pal.Old(Pal.Heap<Link<T>>()), Pal.Heap<Link<T>>())")]
    [Ensures("SpecRing.Nodes<Link<T>>(Pal.Heap<Link<T>>(), @this.first, @this.size) == SpecRing.InsertAt(SpecRing.Nodes<Link<T>>(Pal.Old(Pal.Heap<Link<T>>()), Pal.Old(@this.first), Pal.Old(@this.size)), 0, nw)")]
    private void Start(Link<T> nw)
    {
        Ghost<SpecHeap<Link<T>>> h0 = Pal.Heap<Link<T>>();
        nw.next = nw;
        nw.prev = nw;
        SpecRing.Single<Link<T>>(h0.Value, Pal.Heap<Link<T>>(), first, size, nw);
        first = nw;
        size++;
    }

    [Requires("@this.SpecSize < int.MaxValue")]
    [Ensures("@this.SpecSize == Pal.Old(@this.SpecSize) + 1")]
    [Ensures("@this.SpecLinks == SpecRing.InsertAt(Pal.Old(@this.SpecLinks), 0, Result)")]
    [Ensures("@this.SpecValues == SpecRing.InsertAt(Pal.Old(@this.SpecValues), 0, v)")]
    public Link<T> Front(T v)
    {
        Ghost<SpecHeap<Link<T>>> h0 = Pal.Heap<Link<T>>();
        Ghost<Link<T>?> f0 = first;
        Ghost<SpecInt> n0 = (SpecInt)size;
        Link<T> fresh = new Link<T>(this, v);
        Ghost<SpecHeap<Link<T>>> ha = Pal.Heap<Link<T>>();
        SpecRing.Allocated<Link<T>>(h0.Value, ha.Value, first, size, fresh);
        if (first == null)
        {
            Start(fresh);
        }
        else
        {
            SpecRing.InsHead<Link<T>>(ha.Value, first, size);
            Splice(first, fresh);
            SpecRing.Rotated<Link<T>>(Pal.Heap<Link<T>>(), first, n0.Value, SpecRing.Nodes<Link<T>>(h0.Value, f0.Value, n0.Value), fresh);
            first = fresh;
        }
        SpecRing.Adopted<Link<T>, Chain<T>>(h0.Value, ha.Value, Pal.Heap<Link<T>>(), f0.Value, n0.Value, first, fresh, 0, this);
        return fresh;
    }

    [Requires("Pal.InRegion(at) && SpecRing.Pos<Link<T>>(@this.SpecLinks, at) >= 0")]
    [Ensures("@this.SpecSize == Pal.Old(@this.SpecSize) - 1")]
    [Ensures("@this.SpecLinks == SpecRing.RemoveAt(Pal.Old(@this.SpecLinks), SpecRing.Pos<Link<T>>(Pal.Old(@this.SpecLinks), at))")]
    [Ensures("@this.SpecValues == SpecRing.RemoveAt(Pal.Old(@this.SpecValues), SpecRing.Pos<Link<T>>(Pal.Old(@this.SpecLinks), at))")]
    public void Unlink(Link<T> at)
    {
        Ghost<SpecHeap<Link<T>>> h0 = Pal.Heap<Link<T>>();
        Ghost<Link<T>?> f0 = first;
        Ghost<SpecInt> n0 = (SpecInt)size;
        SpecRing.Member<Link<T>, Chain<T>>(h0.Value, first, size, at, this);
        SpecRing.Neighbours<Link<T>>(h0.Value, first, size, at);
        System.Diagnostics.Debug.Assert(at.owner == this);
        if (at.next == at)
        {
            first = null;
        }
        else
        {
            at.next!.prev = at.prev;
            at.prev!.next = at.next;
            if (first == at)
            {
                first = at.next;
            }
        }
        at.Detach();
        SpecRing.Removed<Link<T>, Chain<T>>(h0.Value, Pal.Heap<Link<T>>(), f0.Value, n0.Value, at, first, this);
        size--;
    }
}

[Region(Cyclic = true)]
public sealed class Link<T>
{
    internal Chain<T>? owner;
    internal Link<T>? next;
    internal Link<T>? prev;
    internal T value;

    [Model] private (T, Chain<T>?) View => (value, owner);

    internal Link(Chain<T> owner, T value)
    {
        this.owner = owner;
        this.value = value;
    }

    [Requires("Pal.InRegion(@this)")]
    [Ensures("SpecRing.Detached<Link<T>>(Pal.Old(Pal.Heap<Link<T>>()), Pal.Heap<Link<T>>(), @this)")]
    internal void Detach()
    {
        owner = null;
        next = null;
        prev = null;
    }
}
