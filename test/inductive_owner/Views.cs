using System;
using System.Diagnostics;
using PalLang;

[assembly: IncludePulseFile("ViewLease.fst")]

namespace PalCSharp.Tests;

[Spec]
public struct ViewOwnerModel<T>
{
    public SpecInt Value;
    public Seq<T> Tag;
}

[SpecType("Class_ViewOwner.class_ViewOwner__model")]
public readonly struct ViewSnapshot<T> { }

public class ViewOwner<T>
{
    private int value;
    private readonly T marker;
    [Refine("Result.Tag.Length == 1")]
    [Model] private ViewOwnerModel<T> Model =>
        new ViewOwnerModel<T> { Value = value, Tag = Pal.Snoc(Pal.EmptySeq<T>(), marker) };
    [Spec] public SpecInt Value => Model.Value;
    [Spec] public T Tag => Model.Tag[0];
    [Spec] public ViewOwnerModel<T> Snapshot => Model;

    [Ensures("@this.Value == initial && Pal.Same(@this.Tag, tag)")]
    public ViewOwner(int initial, T tag) { value = initial; marker = tag; }

    [Ensures("Pal.Same(Result, @this.Tag)")]
    public T Marker => marker;

    [Ensures("@this.Value == next")]
    public void Set(int next) { value = next; }

    [Frac("p"), Ensures("Result == @this.Value")]
    public int Read() => value;

    public sealed class Window : ViewOwner<T>
    {
        private readonly ViewOwner<T> owner;
        private readonly int offset;
        [Spec] public SpecInt SpecOffset => offset;
        [Spec] public SpecInt ProjectedOwnerValue => owner.Value;

        [Ensures("ReferenceEquals(@this.owner, source) && @this.SpecOffset == initial")]
        public Window(ViewOwner<T> source, int initial) : base(0, source.Marker)
        {
            owner = source;
            offset = initial;
        }

        [Ensures("Result == @this.SpecOffset")]
        public int Offset => offset;

        [Requires("@this.SpecOffset == @this.ProjectedOwnerValue")]
        [Ensures("Result == @this.ProjectedOwnerValue")]
        public int DependentOffset => offset;

        [Ensures("Result == @this.ProjectedOwnerValue")]
        public int OwnerValue => owner.Read();

        [Ensures("Result == @this.SpecOffset")]
        [Fuel(0, 0)]
        public int ReadWhileOpened()
        {
            int before = OwnerValue;
#if PAL
            Ghost<SpecInt> snapshot = owner.Value;
            ViewModelProof.ObserveModel(owner, snapshot);
            ViewLeaseProof.Begin<T>(snapshot, Pal.Permission());
#endif
            int result = Offset;
#if PAL
            ViewLeaseProof.EndExplicit(owner, Pal.Old(owner.Value), Pal.Permission());
            ViewModelProof.ObserveModel(owner, snapshot);
#endif
            int after = OwnerValue;
            Pal.Assert(before == after);
            return result;
        }

        [Requires("calls < int.MaxValue")]
        [Ensures("calls == Pal.Old(calls) + (first ? 1 : 0) && Result == @this.SpecOffset")]
        public int CloseAnd(bool first, bool answer, ref int calls)
        {
#if PAL
            ViewLeaseProof.Begin<T>(owner.Value, Pal.Permission());
#endif
            bool closed = false;
            if (first && ViewBranchGate.Tick(ref calls, answer))
            {
#if PAL
                ViewLeaseProof.EndExplicit(owner, Pal.Old(owner.Value), Pal.Permission());
#endif
                closed = true;
            }
#if PAL
            Pal.Join(ViewLeaseSpec.ClosedOrOpened(owner, ViewLeaseSpec.Snapshot(Pal.Old(owner.Snapshot)),
                Pal.Permission(), closed));
            Pal.Join(calls == Pal.Old(calls) + (first ? 1 : 0));
            ViewLeaseProof.Complete(owner, ViewLeaseSpec.Snapshot(Pal.Old(owner.Snapshot)),
                Pal.Permission(), closed);
#endif
#if !PAL
            _ = closed;
#endif
            return Offset;
        }

        [Requires("calls < int.MaxValue")]
        [Ensures("calls == Pal.Old(calls) + (first ? 0 : 1) && Result == @this.SpecOffset")]
        public int CloseOr(bool first, bool answer, ref int calls)
        {
#if PAL
            ViewLeaseProof.Begin<T>(owner.Value, Pal.Permission());
#endif
            bool closed = false;
            if (first || ViewBranchGate.Tick(ref calls, answer))
            {
#if PAL
                ViewLeaseProof.EndExplicit(owner, Pal.Old(owner.Value), Pal.Permission());
#endif
                closed = true;
            }
#if PAL
            Pal.Join(ViewLeaseSpec.ClosedOrOpened(owner, ViewLeaseSpec.Snapshot(Pal.Old(owner.Snapshot)),
                Pal.Permission(), closed));
            Pal.Join(calls == Pal.Old(calls) + (first ? 0 : 1));
            ViewLeaseProof.Complete(owner, ViewLeaseSpec.Snapshot(Pal.Old(owner.Snapshot)),
                Pal.Permission(), closed);
#endif
#if !PAL
            _ = closed;
#endif
            return Offset;
        }

        [Ensures("Result == @this.SpecOffset")]
        public int ReadLoopWhileOpened()
        {
            int before = OwnerValue;
#if PAL
            Ghost<SpecInt> snapshot = owner.Value;
            ViewLeaseProof.Begin<T>(snapshot, Pal.Permission());
#endif
            int result = Offset;
            int i = 0;
            while (i < 2)
            {
                Pal.Invariant(0 <= i && i <= 2 && result == SpecOffset &&
                    value == Pal.Old(value) && Pal.Same(marker, Pal.Old(marker)));
                Pal.Decreases(2 - i);
                result = Offset;
                if (i == 0) { i++; }
                else { i++; }
            }
#if PAL
            ViewLeaseProof.End<T>(snapshot, Pal.Permission());
#endif
            int after = OwnerValue;
            Pal.Assert(before == after);
            return result;
        }

        [Ensures("Result == @this.ProjectedOwnerValue")]
        public int ReadOwnerLoop()
        {
            int before = OwnerValue;
            int result = before;
            int i = 0;
            while (i < 2)
            {
                Pal.Invariant(0 <= i && i <= 2 && result == before &&
                    offset == Pal.Old(offset) && value == Pal.Old(value) &&
                    Pal.Same(marker, Pal.Old(marker)));
                Pal.Decreases(2 - i);
                result = OwnerValue;
                i++;
            }
            return result;
        }
    }

    [Ensures("Result == 3 && @this.Value == 11")]
    public int RetainedView()
    {
        Window view = new Window(this, 3);
        int first = view.ReadWhileOpened();
        Set(11);
        int second = view.ReadWhileOpened();
        Pal.Assert(first == second);
        return second;
    }

    [Ensures("Result == @this.Value")]
    public int ReadDependent()
    {
        int snapshot = Read();
        Window view = new Window(this, snapshot);
        return view.DependentOffset;
    }
}

public static class ViewLeaseSpec
{
    [SpecOp("ViewLease.snapshot_of")]
    public static ViewSnapshot<T> Snapshot<T>(ViewOwnerModel<T> model) => throw new InvalidOperationException();
    [SpecOp("ViewLease.closed_or_opened")]
    public static SlProp ClosedOrOpened<T>([Plain] ViewOwner<T> owner, ViewSnapshot<T> snapshot,
        Perm permission, bool closed) => throw new InvalidOperationException();

    [SpecOp("ViewLease.inv")]
    public static SlProp Inv<T>(ViewOwner<T> owner, ViewSnapshot<T> snapshot, Perm permission) => throw new InvalidOperationException();
    [SpecOp("ViewLease.opened")]
    public static SlProp Opened<T>(ViewOwner<T> owner, ViewSnapshot<T> snapshot, Perm permission) => throw new InvalidOperationException();
    [SpecOp("Class_ViewOwner.spec_ViewOwner_Value")]
    public static SpecInt Value<T>(ViewSnapshot<T> snapshot) => throw new InvalidOperationException();
}

public static class ViewModelProof
{
    [SpecOp("ViewLease.observe_model")]
    public static void ObserveModel<T>(ViewOwner<T> owner, Ghost<SpecInt> snapshot) =>
        throw new InvalidOperationException();
}

public static class ViewLeaseProof
{
    [Lemma, Conditional("PAL")]
    [Requires("ViewLeaseSpec.ClosedOrOpened(owner, snapshot, permission, closed)")]
    [Ensures("ViewLeaseSpec.Inv(owner, snapshot, permission)")]
    [PulseBody("ViewLease.complete $(owner) $(snapshot) $(permission) $(closed)")]
    public static void Complete<T>([Plain] ViewOwner<T> owner,
        Ghost<ViewSnapshot<T>> snapshot, Ghost<Perm> permission, Ghost<bool> closed) { }

    [Lemma, Conditional("PAL"), GhostArg("ViewSnapshot<T> model")]
    [Requires("ViewLeaseSpec.Opened(owner, model, permission)")]
    [Requires("ViewLeaseSpec.Value(model) == snapshot")]
    [Ensures("ViewLeaseSpec.Inv(owner, model, permission)")]
    [PulseBody("ViewLease.end_read $(owner) $(model) $(permission)")]
    public static void EndExplicit<T>([Plain] ViewOwner<T> owner,
        Ghost<SpecInt> snapshot, Ghost<Perm> permission) { }

    [Lemma, Conditional("PAL"), GhostArg("ViewOwner<T> owner"), GhostArg("ViewSnapshot<T> model")]
    [Requires("ViewLeaseSpec.Inv(owner, model, permission)")]
    [Requires("ViewLeaseSpec.Value(model) == snapshot")]
    [Ensures("ViewLeaseSpec.Opened(owner, model, permission)")]
    [PulseBody("ViewLease.begin_read $(owner) $(model) $(permission)")]
    public static void Begin<T>(Ghost<SpecInt> snapshot, Ghost<Perm> permission) { }

    [Lemma, Conditional("PAL"), GhostArg("ViewOwner<T> owner"), GhostArg("ViewSnapshot<T> model")]
    [Requires("ViewLeaseSpec.Opened(owner, model, permission)")]
    [Requires("ViewLeaseSpec.Value(model) == snapshot")]
    [Ensures("ViewLeaseSpec.Inv(owner, model, permission)")]
    [PulseBody("ViewLease.end_read $(owner) $(model) $(permission)")]
    public static void End<T>(Ghost<SpecInt> snapshot, Ghost<Perm> permission) { }
}

public static class ViewBranchGate
{
    [Requires("calls < int.MaxValue")]
    [Ensures("calls == Pal.Old(calls) + 1 && Result == answer")]
    public static bool Tick(ref int calls, bool answer)
    {
        calls++;
        return answer;
    }
}
