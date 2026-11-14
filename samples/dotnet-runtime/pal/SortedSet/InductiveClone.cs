#if PAL
using System;
using System.Diagnostics;
using PalLang;
using static System.Collections.Generic.SortedSetClone;
using static System.Collections.Generic.SortedSetOwnership;

[assembly: IncludePulseFile("SortedSetInductive.Clone.fst")]
[assembly: IncludePulseFile("SortedSetInductive.CloneFocus.fst")]
[assembly: IncludePulseFile("SortedSetInductive.ClonePop.fst")]
[assembly: IncludePulseFile("SortedSetInductive.CloneStep.fst")]
[assembly: IncludePulseFile("SortedSetInductive.CloneClient.fst")]
[assembly: IncludePulseFile("SortedSetInductive.CloneState.fst")]

namespace System.Collections.Generic
{
    [SpecType("SortedSetInductive.ClonePop.witness")]
    internal readonly struct SortedSetCloneWitness<T> { }

    [SpecType("SortedSetInductive.CloneState.budget")]
    internal readonly struct SortedSetCloneBudget { }

    internal static class SortedSetClone
    {
        [SpecOp("Pulse.Lib.CSharp.Tree.left")]
        internal static SortedSetLabels<T> LeftTree<T>(SortedSetLabels<T> source) => throw new InvalidOperationException();
        [SpecOp("Pulse.Lib.CSharp.Tree.right")]
        internal static SortedSetLabels<T> RightTree<T>(SortedSetLabels<T> source) => throw new InvalidOperationException();
        [SpecOp("Pulse.Lib.CSharp.Tree.size")]
        internal static SpecInt Size<T>(SortedSetLabels<T> source) => throw new InvalidOperationException();
        [SpecOp("SortedSetInductive.ClonePop.focus")]
        internal static SortedSetLabels<T> Focus<T>(SortedSetCloneWitness<T> witness) => throw new InvalidOperationException();
        [SpecOp("SortedSetInductive.ClonePop.offset")]
        internal static SpecInt Offset<T>(SortedSetCloneWitness<T> witness) => throw new InvalidOperationException();
        [SpecOp("SortedSetInductive.CloneState.initial")]
        internal static SortedSetCloneBudget Initial<T>(Ghost<SortedSetLabels<T>> source) => throw new InvalidOperationException();
        [SpecOp("SortedSetInductive.CloneState.value")]
        internal static SpecInt Value(SortedSetCloneBudget budget) => throw new InvalidOperationException();
        [SpecOp("SortedSetInductive.CloneState.previous")]
        internal static SortedSetCloneBudget Previous(SortedSetCloneBudget budget) => throw new InvalidOperationException();
        [SpecOp("SortedSetInductive.CloneStep.jobs_for")]
        internal static Seq<(SortedSet<T>.Node, SortedSet<T>.Node)> Jobs<T>(
            SortedSet<T>.Node? source, SortedSet<T>.Node? target) => throw new InvalidOperationException();
        [SpecOp("SortedSetInductive.Clone.cloning")]
        internal static SlProp Cloning<T>(SortedSetLabels<T> source, SortedSet<T>.Node? target,
            Seq<(SortedSet<T>.Node, SortedSet<T>.Node)> pending, SpecInt remaining, Perm permission) => throw new InvalidOperationException();
        [SpecOp("SortedSetInductive.Clone.todo")]
        internal static SlProp Todo<T>(SortedSetLabels<T> source, SortedSet<T>.Node? target, Perm permission) => throw new InvalidOperationException();
        [SpecOp("SortedSetInductive.Clone.restore")]
        internal static SlProp Restore<T>(SortedSetLabels<T> source, SortedSet<T>.Node? root,
            Seq<(SortedSet<T>.Node, SortedSet<T>.Node)> prefix, SpecInt offset, SortedSetLabels<T> focus,
            SortedSet<T>.Node? target, Perm permission) => throw new InvalidOperationException();
        [SpecOp("SortedSetInductive.CloneStep.opened_source")]
        internal static SlProp OpenedSource<T>(SortedSetLabels<T> source, SortedSet<T>.Node? node,
            Perm permission) => throw new InvalidOperationException();
        [SpecOp("SortedSetInductive.CloneClient.opened_job")]
        internal static SlProp OpenedJob<T>(SortedSetLabels<T> source, SortedSet<T>.Node node,
            SortedSet<T>.Node target, Perm permission) => throw new InvalidOperationException();
        [SpecOp("SortedSetInductive.CloneClient.shape")]
        internal static bool Shape<T>(SortedSetLabels<T> source, SortedSet<T>.Node? node,
            SortedSetNodeSnapshot<T> record) => throw new InvalidOperationException();
        [SpecOp("SortedSetInductive.CloneStep.left_stage")]
        internal static SlProp LeftStage<T>(SortedSetLabels<T> source, SortedSet<T>.Node? target,
            Seq<(SortedSet<T>.Node, SortedSet<T>.Node)> prefix,
            Seq<(SortedSet<T>.Node, SortedSet<T>.Node)> pending, Perm permission) => throw new InvalidOperationException();
        [SpecOp("SortedSetInductive.CloneClient.left_opened")]
        internal static SlProp LeftOpened<T>(SortedSetLabels<T> source, SortedSet<T>.Node? node,
            SortedSet<T>.Node? target, Seq<(SortedSet<T>.Node, SortedSet<T>.Node)> prefix,
            Seq<(SortedSet<T>.Node, SortedSet<T>.Node)> pending, Perm permission) => throw new InvalidOperationException();
        [SpecOp("SortedSetInductive.CloneStep.complete")]
        internal static SlProp Complete<T>(SortedSetLabels<T> source, SortedSet<T>.Node? target,
            Seq<(SortedSet<T>.Node, SortedSet<T>.Node)> prefix,
            Seq<(SortedSet<T>.Node, SortedSet<T>.Node)> pending, Perm permission) => throw new InvalidOperationException();
    }

    internal static class SortedSetCloneProof
    {
        [Lemma, Conditional("PAL")]
        [Requires("Cloning(source, target, Jobs(node, target), Size(source), Perm.Full)")]
        [Requires("pending.Length == 1 && pending[0].Item1 == node && pending[0].Item2 == target")]
        [Requires("Value(budget) == Size(source)")]
        [Ensures("Cloning(source, target, pending, Value(budget), Perm.Full)")]
        [PulseBody("SortedSetInductive.CloneState.start $(source) $(node) $(target) $(pending) $(budget) 1.0R")]
        internal static void Start<T>(Ghost<SortedSetLabels<T>> source, SortedSet<T>.Node node, SortedSet<T>.Node target,
            Ghost<Seq<(SortedSet<T>.Node, SortedSet<T>.Node)>> pending, Ghost<SortedSetCloneBudget> budget) { }

        [Lemma, Conditional("PAL")]
        [Requires("Owns(source, Perm.Full)"), Requires("Top(source) == node")]
        [Ensures("OpenedSource(source, node, Perm.Full)")]
        [PulseBody("SortedSetInductive.CloneStep.open_source $(source) $(node) 1.0R")]
        internal static void OpenSource<T>(Ghost<SortedSetLabels<T>> source, SortedSet<T>.Node node) { }

        [Lemma, Conditional("PAL"), GhostArg("SortedSetNodeSnapshot<T> record")]
        [Requires("Raw(node, record, Perm.Full)")]
        [Requires("Owns(LeftTree(source), Perm.Full)"), Requires("Owns(RightTree(source), Perm.Full)")]
        [Requires("Fresh(target, Item(record), Color(record))")]
        [Requires("Shape(source, node, record)")]
        [Ensures("Cloning(source, target, Jobs(node, target), Size(source), Perm.Full)")]
        [PulseBody("SortedSetInductive.CloneStep.seed_opened $(source) $(node) $(target) $(record) 1.0R")]
        internal static void Seed<T>(Ghost<SortedSetLabels<T>> source, SortedSet<T>.Node node, SortedSet<T>.Node target) { }

        [Lemma, Conditional("PAL")]
        [Requires("Owns(source, Perm.Full)"), Requires("Top(source) == null")]
        [Ensures("Cloning(source, null, Pal.EmptySeq<(SortedSet<T>.Node, SortedSet<T>.Node)>(), Size(source), Perm.Full)")]
        [Ensures("Size(source) == 0")]
        [PulseBody("SortedSetInductive.CloneStep.empty_source $(source) 1.0R")]
        internal static void EmptySource<T>(Ghost<SortedSetLabels<T>> source) { }

        [Lemma, GhostArg("Seq<(SortedSet<T>.Node, SortedSet<T>.Node)> before")]
        [Requires("Cloning(source, root, before, Value(budget), Perm.Full)")]
        [Requires("before.Length > 0 && prefix == Pal.Slice(before, 0, before.Length - 1)")]
        [Requires("Pal.Same(next, before[before.Length - 1])")]
        [Ensures("Todo(Focus(Result), next.Item2, Perm.Full)")]
        [Ensures("Restore(source, root, prefix, Offset(Result), Focus(Result), next.Item2, Perm.Full)")]
        [Ensures("Top(Focus(Result)) == next.Item1 && Size(Focus(Result)) > 0")]
        [Ensures("Value(budget) == Offset(Result) + Size(Focus(Result))")]
        [Ensures("prefix.Length <= Offset(Result)")]
        [Ensures("next.Item1 != null && next.Item2 != null")]
        [PulseBody("""
            FStar.Seq.snoc_slice_index $(before) 0 (FStar.Seq.length $(before) - 1);
            FStar.Seq.lemma_eq_intro $(before) (FStar.Seq.slice $(before) 0 (FStar.Seq.length $(before)));
            rewrite (SortedSetInductive.Clone.cloning $(source) $(root) $(before) (SortedSetInductive.CloneState.value $(budget)) 1.0R)
              as (SortedSetInductive.Clone.cloning $(source) $(root) (FStar.Seq.snoc $(prefix) $(next)) (SortedSetInductive.CloneState.value $(budget)) 1.0R);
            SortedSetInductive.ClonePop.pop $(source) $(root) $(prefix) $(next) (SortedSetInductive.CloneState.value $(budget)) 1.0R
            """)]
        internal static Ghost<SortedSetCloneWitness<T>> Pop<T>(Ghost<SortedSetLabels<T>> source, SortedSet<T>.Node root,
            Ghost<Seq<(SortedSet<T>.Node, SortedSet<T>.Node)>> prefix,
            (SortedSet<T>.Node, SortedSet<T>.Node) next, Ghost<SortedSetCloneBudget> budget) => throw new InvalidOperationException();

        [Lemma, Conditional("PAL")]
        [Requires("Todo(source, target, Perm.Full)"), Requires("Top(source) == node")]
        [Ensures("OpenedJob(source, node, target, Perm.Full)")]
        [PulseBody("SortedSetInductive.CloneClient.open_job $(source) $(node) $(target) 1.0R")]
        internal static void OpenJob<T>(Ghost<SortedSetLabels<T>> source, SortedSet<T>.Node node, SortedSet<T>.Node target) { }

        [Lemma, Conditional("PAL"), GhostArg("SortedSetNodeSnapshot<T> record"), GhostArg("SortedSetNodeSnapshot<T> copy")]
        [GhostArg("Seq<(SortedSet<T>.Node, SortedSet<T>.Node)> leftPending")]
        [Requires("Raw(node, record, Perm.Full)"), Requires("Raw(target, copy, Perm.Full)")]
        [Requires("Cloning(LeftTree(source), Left(copy), leftPending, Size(LeftTree(source)), Perm.Full)")]
        [Requires("leftPending == Jobs(Left(record), Left(copy))")]
        [Requires("Owns(RightTree(source), Perm.Full)")]
        [Requires("Shape(source, node, record) && Pal.Same(Entry(copy), Entry(record)) && Right(copy) == null")]
        [Requires("pending == Pal.Concat(prefix, Jobs(Top(LeftTree(source)), Left(copy)))")]
        [Ensures("LeftStage(source, target, prefix, pending, Perm.Full)")]
        [PulseBody("""
            rewrite (SortedSetInductive.Clone.cloning (Pulse.Lib.CSharp.Tree.left $(source)) (SortedSetInductive.Ownership.left $(copy))
              $(leftPending)
              (Pulse.Lib.CSharp.Tree.size (Pulse.Lib.CSharp.Tree.left $(source))) 1.0R)
              as (SortedSetInductive.Clone.cloning (Pulse.Lib.CSharp.Tree.left $(source)) (SortedSetInductive.Ownership.left $(copy))
                (SortedSetInductive.CloneStep.jobs (SortedSetInductive.Ownership.top (Pulse.Lib.CSharp.Tree.left $(source))) (SortedSetInductive.Ownership.left $(copy)))
                (Pulse.Lib.CSharp.Tree.size (Pulse.Lib.CSharp.Tree.left $(source))) 1.0R);
            SortedSetInductive.CloneClient.close_left $(source) $(node) $(target) $(record) $(copy) $(prefix) $(pending) 1.0R
            """)]
        internal static void CloseLeft<T>(Ghost<SortedSetLabels<T>> source, SortedSet<T>.Node node, SortedSet<T>.Node target,
            Ghost<Seq<(SortedSet<T>.Node, SortedSet<T>.Node)>> prefix, Ghost<Seq<(SortedSet<T>.Node, SortedSet<T>.Node)>> pending) { }

        [Lemma, Conditional("PAL")]
        [Requires("LeftStage(source, target, prefix, pending, Perm.Full)"), Requires("Top(source) == node")]
        [Ensures("LeftOpened(source, node, target, prefix, pending, Perm.Full)")]
        [PulseBody("SortedSetInductive.CloneClient.open_left $(source) $(node) $(target) $(prefix) $(pending) 1.0R")]
        internal static void OpenLeft<T>(Ghost<SortedSetLabels<T>> source, SortedSet<T>.Node node, SortedSet<T>.Node target,
            Ghost<Seq<(SortedSet<T>.Node, SortedSet<T>.Node)>> prefix, Ghost<Seq<(SortedSet<T>.Node, SortedSet<T>.Node)>> pending) { }

        [Lemma, Conditional("PAL"), GhostArg("SortedSetNodeSnapshot<T> record"), GhostArg("SortedSetNodeSnapshot<T> copy")]
        [GhostArg("Seq<(SortedSet<T>.Node, SortedSet<T>.Node)> rightPending")]
        [GhostArg("SortedSet<T>.Node? rightTarget")]
        [Requires("Raw(node, record, Perm.Full)"), Requires("Raw(target, copy, Perm.Full)")]
        [Requires("Cloning(LeftTree(source), Left(copy), Jobs(Top(LeftTree(source)), Left(copy)), Size(LeftTree(source)), Perm.Full)")]
        [Requires("Cloning(RightTree(source), rightTarget, rightPending, Size(RightTree(source)), Perm.Full)")]
        [Requires("rightTarget == Right(copy) && rightPending == Jobs(Right(record), Right(copy))")]
        [Requires("Shape(source, node, record) && Pal.Same(Entry(copy), Entry(record))")]
        [Requires("pending == Pal.Concat(Pal.Concat(prefix, Jobs(Top(LeftTree(source)), Left(copy))), Jobs(Top(RightTree(source)), Right(copy)))")]
        [Ensures("Complete(source, target, prefix, pending, Perm.Full)")]
        [PulseBody("""
            rewrite (SortedSetInductive.Clone.cloning (Pulse.Lib.CSharp.Tree.right $(source)) $(rightTarget)
              $(rightPending)
              (Pulse.Lib.CSharp.Tree.size (Pulse.Lib.CSharp.Tree.right $(source))) 1.0R)
              as (SortedSetInductive.Clone.cloning (Pulse.Lib.CSharp.Tree.right $(source)) (SortedSetInductive.Ownership.right $(copy))
                (SortedSetInductive.CloneStep.jobs (SortedSetInductive.Ownership.top (Pulse.Lib.CSharp.Tree.right $(source))) (SortedSetInductive.Ownership.right $(copy)))
                (Pulse.Lib.CSharp.Tree.size (Pulse.Lib.CSharp.Tree.right $(source))) 1.0R);
            SortedSetInductive.CloneClient.close_complete $(source) $(node) $(target) $(record) $(copy) $(prefix) $(pending) 1.0R
            """)]
        internal static void CloseComplete<T>(Ghost<SortedSetLabels<T>> source, SortedSet<T>.Node node, SortedSet<T>.Node target,
            Ghost<Seq<(SortedSet<T>.Node, SortedSet<T>.Node)>> prefix, Ghost<Seq<(SortedSet<T>.Node, SortedSet<T>.Node)>> pending) { }

        [Lemma, Conditional("PAL")]
        [Requires("Restore(source, root, prefix, Offset(witness), Focus(witness), target, Perm.Full)")]
        [Requires("Complete(Focus(witness), target, prefix, pending, Perm.Full)")]
        [Requires("Value(budget) == Offset(witness) + Size(Focus(witness))")]
        [Ensures("Cloning(source, root, pending, Value(Previous(budget)), Perm.Full)")]
        [PulseBody("SortedSetInductive.CloneState.finish_task $(source) $(root) (SortedSetInductive.ClonePop.focus $(witness)) $(target) $(prefix) $(pending) (SortedSetInductive.ClonePop.offset $(witness)) $(budget) 1.0R")]
        internal static void FinishTask<T>(Ghost<SortedSetLabels<T>> source, SortedSet<T>.Node root,
            Ghost<SortedSetCloneWitness<T>> witness, SortedSet<T>.Node target,
            Ghost<Seq<(SortedSet<T>.Node, SortedSet<T>.Node)>> prefix,
            Ghost<Seq<(SortedSet<T>.Node, SortedSet<T>.Node)>> pending, Ghost<SortedSetCloneBudget> budget) { }

        [Lemma, Conditional("PAL")]
        [Preserves("Cloning(source, root, pending, Value(budget), Perm.Full)")]
        [Ensures("pending.Length <= Value(budget) && Value(budget) <= Size(source)")]
        [Ensures("(pending.Length == 0) == (Value(budget) == 0)")]
        [PulseBody("SortedSetInductive.Clone.facts $(source) $(root) $(pending) (SortedSetInductive.CloneState.value $(budget)) 1.0R")]
        internal static void Facts<T>(Ghost<SortedSetLabels<T>> source, SortedSet<T>.Node root,
            Ghost<Seq<(SortedSet<T>.Node, SortedSet<T>.Node)>> pending, Ghost<SortedSetCloneBudget> budget) { }

        [Lemma, Conditional("PAL"), GhostArg("Seq<(SortedSet<T>.Node, SortedSet<T>.Node)> before")]
        [Requires("Cloning(source, root, before, Value(budget), Perm.Full)")]
        [Requires("pending.Length == 0 && pending == before")]
        [Ensures("Owns(source, Perm.Full)")]
        [Ensures("SortedSetConstruction.Holds(root, Values(source), Perm.Full)")]
        [PulseBody("""
            FStar.Seq.lemma_eq_intro $(before) $(pending);
            rewrite (SortedSetInductive.Clone.cloning $(source) $(root) $(before) (SortedSetInductive.CloneState.value $(budget)) 1.0R)
              as (SortedSetInductive.Clone.cloning $(source) $(root) $(pending) (SortedSetInductive.CloneState.value $(budget)) 1.0R);
            SortedSetInductive.Clone.finish $(source) $(root) $(pending) (SortedSetInductive.CloneState.value $(budget)) 1.0R
            """)]
        internal static void Finish<T>(Ghost<SortedSetLabels<T>> source, SortedSet<T>.Node root,
            Ghost<Seq<(SortedSet<T>.Node, SortedSet<T>.Node)>> pending, Ghost<SortedSetCloneBudget> budget) { }
    }
}
#endif
