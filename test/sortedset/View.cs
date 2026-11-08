// R32.13. A view: a sealed nested subclass of a generic class with a model, which borrows
// an object of that class (as dotnet/runtime's `SortedSet<T>.TreeSubSet` borrows the set it
// is a view of) and inherits its fields. Calls on the view bind to its overrides, and to the
// base's members verified again at the view against their `At` contracts.
using PalLang;

[Spec]
public struct PileModel<T>
{
    public System.Collections.Generic.IComparer<T> Comparer;
    public SpecInt Count;
    public SpecInt Version;
}

public class Pile<T>
{
    internal System.Collections.Generic.IComparer<T> comparer;
    internal int count;
    internal int version;

    [Model] private PileModel<T> Model => new PileModel<T> { Comparer = comparer, Count = count, Version = version };

    [Spec] internal System.Collections.Generic.IComparer<T> SpecComparer => Model.Comparer;
    [Spec] internal SpecInt SpecCount => Model.Count;
    [Spec] internal SpecInt SpecVersion => Model.Version;

    [Ensures("@this.SpecComparer == c && @this.SpecCount == n && @this.SpecVersion == 0")]
    public Pile(System.Collections.Generic.IComparer<T> c, int n)
    {
        comparer = c;
        count = n;
    }

    [Requires("@this.SpecCount < 1000 && @this.SpecVersion < 1000")]
    [Ensures("@this.SpecCount == Pal.Old(@this.SpecCount) + 1")]
    [Ensures("@this.SpecVersion == Pal.Old(@this.SpecVersion) + 1")]
    [Requires("@this._underlying.SpecCount < 1000 && @this._underlying.SpecVersion < 1000", At = typeof(Pile<>.Top))]
    [Requires("@this.SpecCoherent && @this._countVersion != @this._underlying.SpecVersion + 1", At = typeof(Pile<>.Top))]
    [Ensures("@this._underlying.SpecCount == Pal.Old(@this._underlying.SpecCount) + 1", At = typeof(Pile<>.Top))]
    [Ensures("@this._underlying.SpecVersion == Pal.Old(@this._underlying.SpecVersion) + 1", At = typeof(Pile<>.Top))]
    [Ensures("@this.SpecCoherent", At = typeof(Pile<>.Top))]
    internal virtual void Push()
    {
        count++;
        version++;
    }

    internal virtual void VersionCheck() { }

    [Ensures("Result == @this.SpecCount")]
    [Requires("@this.SpecCoherent", At = typeof(Pile<>.Top))]
    [Ensures("Result == @this.SpecViewCount && @this.SpecCoherent", At = typeof(Pile<>.Top))]
    public virtual int Count
    {
        get
        {
            VersionCheck();
            return count;
        }
    }

    // A member of the base that calls a virtual one: at the view, it is verified again,
    // and its call reaches the view's override.
    [Ensures("Result == (@this.SpecCount >= k)")]
    [Requires("@this.SpecCoherent", At = typeof(Pile<>.Top))]
    [Ensures("Result == (@this.SpecViewCount >= k) && @this.SpecCoherent", At = typeof(Pile<>.Top))]
    public bool AtLeast(int k) => Count >= k;

    [Requires("lo >= 0")]
    [Ensures("Result.SpecLo == lo && Result.SpecCountVersion < 0 && Result.SpecCoherent")]
    [return: Exactly(typeof(Pile<>.Top))]
    public Pile<T> Above(int lo) => new Top(this, lo);

    [Requires("lo >= 0")]
    [Ensures("Result == (@this.SpecCount > lo ? @this.SpecCount - lo : 0)")]
    public int CountAbove(int lo)
    {
        Pile<T> view = Above(lo);
        return view.Count;
    }

    // A writer member of a view, called on a view the method holds, writes the receiver.
    [Requires("lo >= 0 && @this.SpecVersion >= 0 && @this.SpecCount < 1000 && @this.SpecVersion < 1000")]
    [Ensures("@this.SpecCount == Pal.Old(@this.SpecCount) + 1")]
    public void PushAbove(int lo)
    {
        Pile<T> view = Above(lo);
        view.Push();
    }

    // A base member called on a view runs its replica.
    [Requires("lo >= 0")]
    [Ensures("Result == ((@this.SpecCount > lo ? @this.SpecCount - lo : 0) >= k)")]
    public bool AboveAtLeast(int lo, int k)
    {
        Pile<T> view = Above(lo);
        return view.AtLeast(k);
    }

    internal sealed class Top : Pile<T>
    {
        private readonly Pile<T> _underlying;
        private readonly int _lo;
        private int _countVersion;

        [Spec] internal SpecInt SpecLo => _lo;
        [Spec] internal SpecInt SpecCountVersion => _countVersion;
        [Spec] internal SpecInt SpecViewCount => _underlying.SpecCount > _lo ? _underlying.SpecCount - _lo : 0;
        [Spec] internal bool SpecCoherent =>
            _lo >= 0 && Pal.Implies(_countVersion == _underlying.SpecVersion, count == SpecViewCount);

        [Requires("lo >= 0")]
        [Ensures("ReferenceEquals(@this._underlying, u) && @this.SpecLo == lo && @this.SpecCountVersion < 0 && @this.SpecCoherent")]
        public Top(Pile<T> u, int lo) : base(u.comparer, 0)
        {
            _underlying = u;
            _lo = lo;
            version = -1;
            _countVersion = u.version == -1 ? -2 : -1;
        }

        [Requires("@this.SpecCoherent")]
        [Ensures("@this.SpecCoherent && @this._countVersion == @this._underlying.SpecVersion")]
        [Ensures("@this.SpecLo == Pal.Old(@this.SpecLo)")]
        internal override void VersionCheck()
        {
            if (_countVersion != _underlying.version)
            {
                count = _underlying.count > _lo ? _underlying.count - _lo : 0;
                _countVersion = _underlying.version;
            }
        }

        internal override void Push()
        {
            _underlying.Push();
            VersionCheck();
        }
    }
}
