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

    // R32.14. `this as Top` in a member of the base translated at the base: the receiver is
    // exactly a `Pile<T>`, never a view.
    [Ensures("Result == 0")]
    public int Kind()
    {
        Top? top = this as Top;
        if (top != null) return 1;
        return 0;
    }

    // R32.14. A view of another object of the class, named in a loop invariant through a
    // cast to the view's type.
    [Requires("lo >= 0 && other.SpecCount < 1000")]
    [Ensures("Result == (other.SpecCount > lo ? other.SpecCount - lo : 0)")]
    public int CountAboveOf(Pile<T> other, int lo)
    {
        Pile<T> view = other.Above(lo);
        int r = view.Count;
        int i = 0;
        while (i < 2)
        {
            Pal.Invariant(0 <= i && i <= 2 && ((Top)view).SpecCoherent && ((Top)view).SpecLo == lo &&
                          r == ((Top)view).SpecViewCount);
            Pal.Decreases(2 - i);
            r = view.Count;
            i++;
        }
        return r;
    }

    // R32.14. A `return` in an arm that may also complete.
    [Ensures("Result == (b && k == 0 ? 1 : 2)")]
    public static int Nested(bool b, int k)
    {
        if (b)
        {
            if (k == 0)
                return 1;
        }
        return 2;
    }

    internal sealed class Top : Pile<T>
    {
        private int _hi;

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
            _hi = lo;
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

        // R32.14. A call with an omitted optional argument, in an arm of a conditional; and a
        // field no member it reaches writes (`_hi`) is the same after the call.
        [Requires("@this.SpecCoherent && @this._underlying.SpecCount < 1000")]
        [Ensures("Result == (b ? @this.SpecViewCount : @this._hi) && @this.SpecCoherent")]
        internal int Pick(bool b)
        {
            int r = b ? Current() : _hi;
            return r;
        }

        [Requires("@this.SpecCoherent && @this._underlying.SpecCount < 1000 && 0 <= extra && extra <= 1")]
        [Ensures("Result == @this.SpecViewCount + extra && @this.SpecCoherent")]
        internal int Current(int extra = 0)
        {
            Sync(true);
            return count + extra;
        }

        // R35.18. Translated once per constant its callers pass, with the test of `full`
        // decided: `Sync__full_true` and `Sync__full_false`.
        [Requires("@this.SpecCoherent")]
        [Ensures("@this.SpecCoherent && @this.SpecLo == Pal.Old(@this.SpecLo) && @this._hi == Pal.Old(@this._hi)")]
        [Ensures("Pal.Implies(full, @this._countVersion == @this._underlying.SpecVersion)")]
        private void Sync([Specialize] bool full)
        {
            if (full)
            {
                VersionCheck();
            }
        }

        [Requires("@this.SpecCoherent")]
        [Ensures("Result == @this._hi && @this.SpecCoherent")]
        internal int Low()
        {
            Sync(false);
            return _hi;
        }

        internal override void Push()
        {
            _underlying.Push();
            VersionCheck();
        }
    }
}
