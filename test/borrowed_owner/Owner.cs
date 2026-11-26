using PalLang;
using System.Collections.Generic;

[assembly: IncludePulseFile("OwnerFrameState.fst")]

[SpecType("OwnerFrameState.state")]
public readonly struct OwnerFrameState { }

public static class OwnerFrame
{
    [SpecOp("OwnerFrameState.make")]
    public static OwnerFrameState Make(int n) => throw new System.InvalidOperationException();
    [SpecOp("OwnerFrameState.next")]
    public static OwnerFrameState Next(OwnerFrameState s) => throw new System.InvalidOperationException();
}

[Spec]
public struct OwnerModel<T> { public SpecInt Value; public IComparer<T> Comparer; }

public class Owner<T>
{
    [GhostField("OwnerFrame.Make(0)")]
    protected ref OwnerFrameState audit => throw new System.InvalidOperationException("Specification only");
    [GhostField("OwnerFrame.Make(0)")]
    protected ref OwnerFrameState touches => throw new System.InvalidOperationException("Specification only");
    private int value;
    private IComparer<T> comparer = Comparer<T>.Default;
    [Model] private OwnerModel<T> Model => new OwnerModel<T> { Value = value, Comparer = comparer };
    [Spec] public virtual SpecInt SpecValue => Model.Value;
    [Spec] public virtual Owner<T> Identity => this;
    [Spec] public virtual bool OwnerFlag => false;

    [Ensures("ReferenceEquals(@this.Identity, @this)")]
    public void CheckIdentity()
    {
        HandoffProof.Keep<T>(this.Identity, Pal.Permission());
    }

    [Ensures("@this.SpecValue == n")]
    public Owner(int n) { value = n; }

    [Ensures("Result == item")]
    public int Echo(int item) => item;

    // The proof opens the source, and the argument reads it before Echo needs
    // the invariant again. Its erased model must be pinned at this boundary.
    [Requires("ReferenceEquals(raw, @this)")]
    [Ensures("Result == @this.SpecValue")]
    public int ReadWindow([Plain] Owner<T> raw)
    {
        HandoffProof.Open<T>(this, raw, Pal.Permission());
        return Echo(raw.value);
    }

    [Requires("ReferenceEquals(raw, @this)")]
    [Ensures("Result == @this.SpecValue")]
    public int ReadWindowLoop([Plain] Owner<T> raw)
    {
        int i = 0, result = 0;
        while (i < 1)
        {
            Pal.Invariant(0 <= i && i <= 1);
            Pal.Invariant(i == 0 || result == this.SpecValue);
            Pal.Decreases(1 - i);
            HandoffProof.Open<T>(this, raw, Pal.Permission());
            result = Echo(raw.value);
            i++;
        }
        return result;
    }

    [Ensures("Result == next && @this.SpecValue == next")]
    public int ChangeAndRead(int next)
    {
        value = next;
        return Echo(value);
    }

    [Ensures("Result == next && @this.SpecValue == next")]
    public int ChangeArgument(int next) => Echo(ChangeAndRead(next));

    [Requires("ReferenceEquals(raw, @this)")]
    [Ensures("Result == @this.SpecValue")]
    public int ClosedOwnerReads([Plain] Owner<T> raw)
    {
        int result = value;
        HandoffProof.Inspect<T>(Pal.Permission());
        Pal.Assert(result == this.SpecValue);
        HandoffProof.Keep<T>(this.Identity, Pal.Permission());
        HandoffProof.OpenGhost<T>(this.Identity, raw, Pal.Permission());
        return Echo(raw.value);
    }

    [Requires("ReferenceEquals(raw, @this)")]
    [Ensures("Result == @this.SpecValue")]
    public int ClosedOwnerLoop([Plain] Owner<T> raw)
    {
        int result = value, i = 0;
        HandoffProof.Inspect<T>(Pal.Permission());
        while (i < 2)
        {
            Pal.Invariant(0 <= i && i <= 2);
            Pal.Invariant(result == this.SpecValue);
            Pal.Decreases(2 - i);
            HandoffProof.OpenGhost<T>(this.Identity, raw, Pal.Permission());
            result = Echo(raw.value);
            HandoffProof.Inspect<T>(Pal.Permission());
            result = value;
            i++;
        }
        return result;
    }

    [Ensures("Result == @this.SpecValue")]
    [Ensures("Result == @this.SpecValue", At = typeof(Owner<>.Window))]
    public virtual int Value => value;

    [Ensures("Result == @this.SpecValue")]
    [Ensures("Result == @this.SpecValue", At = typeof(Owner<>.Window))]
    public virtual int Stable => value;

    [Ensures("Result == (skip || @this.SpecValue == 7)")]
    [Ensures("Result == (skip || @this.SpecValue == 7)", At = typeof(Owner<>.Window))]
    public bool ShortCircuit(bool skip) => skip || Stable == 7;

    [Ensures("Result == (check && @this.SpecValue == 7)")]
    [Ensures("Result == (check && @this.SpecValue == 7)", At = typeof(Owner<>.Window))]
    public bool AndCircuit(bool check) => check && Stable == 7;

    [Ensures("Result.SpecValue == n")]
    [return: Exactly(typeof(Owner<>.Window))]
    public Owner<T> Select(int n) => new Window(this, n);

    [Ensures("ReferenceEquals(Result.owner, @this) && Result.value == @this.SpecValue && !Result.ended")]
    [Ensures("Result.value == @this.SpecValue && !Result.ended", At = typeof(Owner<>.Window))]
    public Iterator GetEnumerator() => new Iterator(this);

    [Ensures("Result == (@this.SpecValue == other.SpecValue)")]
    [Ensures("Result == (@this.SpecValue == other.SpecValue)", At = typeof(Owner<>.Window))]
    public bool Compare(Owner<T> other)
    {
        Iterator mine = GetEnumerator();
        Iterator theirs = other.GetEnumerator();
        bool mineEnded = !mine.MoveNext();
        bool theirsEnded = !theirs.MoveNext();
        bool equal = mine.Current == theirs.Current;
        while (!mineEnded && !theirsEnded)
        {
            Pal.Invariant(mine.SpecEnded && theirs.SpecEnded && mineEnded == theirsEnded);
            Pal.Invariant(mine.SpecValue == this.SpecValue && theirs.SpecValue == other.SpecValue);
            Pal.Decreases(mineEnded ? 0 : 1);
            mineEnded = !mine.MoveNext();
            theirsEnded = !theirs.MoveNext();
        }
        mine.Dispose();
        theirs.Dispose();
        return equal && mineEnded && theirsEnded;
    }

    public sealed class Window : Owner<T>
    {
        private readonly Owner<T> source;
        private readonly int selected;
        private int cache;
        private bool flag;
        [Spec] public override bool OwnerFlag => flag;
        [Spec] public override SpecInt SpecValue => selected;
        [Spec] public override Owner<T> Identity => source;
        public override int Stable => selected;

        [Ensures("ReferenceEquals(@this.source, owner) && @this.selected == n")]
        public Window(Owner<T> owner, int n) : base(0)
        {
            source = owner;
            selected = n;
        }

        [Ensures("Result == (@this.SpecValue == other.SpecValue)")]
        public bool DirectCompare(Owner<T> other)
        {
            Iterator mine = this.GetEnumerator();
            Iterator theirs = other.GetEnumerator();
            bool moved = mine.MoveNext() && theirs.MoveNext();
            bool equal = mine.Current == theirs.Current;
            mine.Dispose();
            theirs.Dispose();
            return moved && equal;
        }

        public override int Value
        {
            get
            {
                Pal.UpdateGhost(ref touches, OwnerFrame.Next(touches));
                flag = !flag;
                cache = selected;
                return cache;
            }
        }
    }

    public struct Iterator
    {
        private readonly Owner<T> owner;
        private readonly int value;
        private bool ended;
        [Spec] public SpecInt SpecValue => value;
        [Spec] public bool SpecEnded => ended;
        [Spec] public bool SpecOwnerFlag => owner.OwnerFlag;

        [Ensures("ReferenceEquals(@this.owner, source) && @this.SpecValue == source.SpecValue && !@this.SpecEnded")]
        public Iterator(Owner<T> source) : this(source, false) { }

        [Ensures("ReferenceEquals(@this.owner, source) && @this.SpecValue == source.SpecValue && !@this.SpecEnded")]
        private Iterator(Owner<T> source, bool unused) { owner = source; value = source.Value; ended = false; }

        [Ensures("Result == !Pal.Old(@this.SpecEnded) && @this.SpecEnded")]
        public bool MoveNext()
        {
            bool moved = !ended;
            int i = 0;
            while (i < 1)
            {
                Pal.Invariant(0 <= i && i <= 1);
                Pal.Decreases(1 - i);
                int observed = owner.Value;
                i++;
            }
            ended = true;
            return moved;
        }

        [Ensures("Result == @this.SpecValue")]
        public int Current => value;

        [Ensures("Result == @this.SpecValue && @this.SpecOwnerFlag == Pal.Old(@this.SpecOwnerFlag)")]
        public int ReadCurrent() => Current;

        [Ensures("true")]
        public void Dispose() { }

        [Ensures("true")]
        public void CheckOwnerIdentity()
        {
            HandoffProof.Keep<T>(owner.Identity, Pal.Permission());
        }
    }
}

public static class BorrowedOwnerClient
{
    [Ensures("Result == 7")]
    public static int ReadonlyRetainedOwner()
    {
        var source = new Owner<int>(33);
        var view = source.Select(7);
        var iterator = view.GetEnumerator();
        int result = iterator.ReadCurrent();
        iterator.Dispose();
        return result;
    }

    [Ensures("Result")]
    public static bool GetterJoins(bool skip)
    {
        var source = new Owner<int>(33);
        var view = source.Select(7);
        bool left = view.ShortCircuit(skip);
        bool right = view.AndCircuit(!skip);
        return left && (skip || right);
    }

    [Ensures("Result == 7")]
    public static int ConditionOnly()
    {
        var source = new Owner<int>(7);
        var iterator = source.GetEnumerator();
        int n = 0;
        if (iterator.MoveNext()) { n = 1; }
        Pal.Assert(n == 1 && iterator.SpecValue == 7);
        int result = iterator.Current;
        iterator.Dispose();
        return result;
    }

    [Ensures("Result")]
    public static bool CompareSelected()
    {
        var source = new Owner<int>(33);
        var view = new Owner<int>.Window(source, 7);
        var other = new Owner<int>(7);
        bool direct = view.DirectCompare(other);
        bool inherited = view.Compare(other);
        return direct && inherited;
    }

    [Ensures("!Result")]
    public static bool CompareDistinct()
    {
        var source = new Owner<int>(33);
        var view = source.Select(7);
        var other = new Owner<int>(33);
        return view.Compare(other);
    }

    [Ensures("Result == 7")]
    public static int Run()
    {
        var source = new Owner<int>(33);
        var view = source.Select(7);
        var iterator = view.GetEnumerator();
        bool moved = iterator.MoveNext();
        iterator.CheckOwnerIdentity();
        Pal.Assert(moved);
        int value = iterator.Current;
        iterator.Dispose();
        Pal.Assert(source.SpecValue == 33);
        return value;
    }

    [Requires("left.SpecValue == right.SpecValue && !ReferenceEquals(left, right)")]
    [Ensures("!ReferenceEquals(left.Identity, right.Identity)")]
    public static void SameModelDistinct(Owner<int> left, Owner<int> right)
    {
        left.CheckIdentity();
        right.CheckIdentity();
    }

    [Ensures("Result == 7")]
    public static int Branch(bool inspect)
    {
        var source = new Owner<int>(33);
        var view = source.Select(7);
        var iterator = view.GetEnumerator();
        bool moved = iterator.MoveNext();
        int result = 7;
        if (inspect && moved)
        {
            result = iterator.Current;
        }
        iterator.Dispose();
        return result;
    }

    [Ensures("true")]
    public static void MutatingBranch(bool inspect)
    {
        var source = new Owner<int>(33);
        var view = source.Select(7);
        var iterator = view.GetEnumerator();
        if (inspect)
        {
            bool moved = iterator.MoveNext();
        }
        iterator.Dispose();
    }

}
