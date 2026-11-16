using System;
using System.Diagnostics;
using PalLang;
using static System.Collections.Generic.SortedSetConstruction;

[assembly: IncludePulseFile("SortedSetInductive.Construction.fst")]

namespace System.Collections.Generic
{
    internal static class SortedSetConstruction
    {
        [SpecOp("SortedSetInductive.Construction.holds")]
        internal static SlProp Holds<T>(SortedSet<T>.Node? root, SpecTree<(T, bool)> tree, Perm permission) =>
            throw new InvalidOperationException();

        [SpecOp("SortedSetInductive.Construction.adopted")]
        internal static SortedSetOwnershipState<T> Adopted<T>(SortedSetOwnershipState<T> old,
            Ghost<SortedSetLabels<T>> labels) => throw new InvalidOperationException();

        [SpecOp("Pulse.Lib.CSharp.SortedBuild.leaf_of")]
        internal static SpecTree<(T, bool)> Leaf<T>(T item, bool red) => throw new InvalidOperationException();

        [SpecOp("SortedSetInductive.Construction.opened")]
        internal static SlProp Opened<T>(SortedSet<T>.Node? root, SpecTree<(T, bool)> tree) =>
            throw new InvalidOperationException();

        [System.Diagnostics.Conditional("PAL")]
        [SpecOp("SortedSetInductive.Construction.build_facts")]
        internal static void BuildFacts<T>(Seq<T> items, SpecInt lo, SpecInt hi, SpecTree<(T, bool)> red) =>
            throw new InvalidOperationException();

        [System.Diagnostics.Conditional("PAL")]
        [SpecOp("SortedSetInductive.Construction.build_step")]
        internal static void BuildStep<T>(Seq<T> items, SpecInt lo, SpecInt hi, SpecInt mid,
            bool even, SpecTree<(T, bool)> red) => throw new InvalidOperationException();
    }

    internal static class SortedSetConstructionProof
    {
        [Lemma, Conditional("PAL")]
        [Requires("root == null")]
        [Ensures("Holds(root, SpecTree.Leaf<(T, bool)>(), Perm.Full)")]
        [PulseBody("SortedSetInductive.Construction.empty $(root) 1.0R")]
        internal static void Empty<T>(Ghost<SortedSet<T>.Node?> root) { }

        [Lemma, Conditional("PAL")]
        [Preserves("Holds(root, tree, Perm.Full)")]
        [Ensures("(root == null) == tree.IsLeaf")]
        [PulseBody("SortedSetInductive.Construction.cases $(root) $(tree) 1.0R")]
        internal static void Cases<T>(Ghost<SortedSet<T>.Node?> root, Ghost<SpecTree<(T, bool)>> tree) { }

        [Lemma, GhostArg("SortedSetNodeSnapshot<T> record")]
        [Requires("SortedSetOwnership.Raw(root, record, Perm.Full)")]
        [Ensures("SortedSetOwnership.Raw(root, Result, Perm.Full)")]
        [Ensures("Pal.Same(Result, record)")]
        [PulseBody("hide $(record)")]
        internal static Ghost<SortedSetNodeSnapshot<T>> Snapshot<T>(Ghost<SortedSet<T>.Node?> root) =>
            throw new InvalidOperationException();

        [Lemma, Conditional("PAL")]
        [Requires("Holds(oldRoot, tree, Perm.Full)"), Requires("oldRoot == root")]
        [Ensures("Holds(root, tree, Perm.Full)")]
        [PulseBody("SortedSetInductive.Construction.reindex $(oldRoot) $(root) $(tree)")]
        internal static void Reindex<T>(Ghost<SortedSet<T>.Node?> oldRoot, Ghost<SortedSet<T>.Node?> root,
            Ghost<SpecTree<(T, bool)>> tree) { }

        [Lemma, Conditional("PAL"), GhostArg("T item"), GhostArg("NodeColor color")]
        [Requires("SortedSetOwnership.Fresh(root, item, color)")]
        [Ensures("Holds(root, Leaf(item, color == NodeColor.Red), Perm.Full)")]
        [PulseBody("SortedSetInductive.Construction.seal_fresh $(root) $(item) $(color)")]
        internal static void SealFresh<T>(Ghost<SortedSet<T>.Node> root) { }

        [Lemma, Conditional("PAL"), GhostArg("SortedSetNodeSnapshot<T> record")]
        [Requires("SortedSetOwnership.Raw(root, record, Perm.Full)")]
        [Requires("Holds(SortedSetOwnership.Left(record), left, Perm.Full)")]
        [Requires("Holds(SortedSetOwnership.Right(record), right, Perm.Full)")]
        [Ensures("Holds(root, SpecTree.Branch(left, SortedSetOwnership.Entry(record), right), Perm.Full)")]
        [PulseBody("SortedSetInductive.Construction.seal $(root) $(record) $(left) $(right)")]
        internal static void Seal<T>(Ghost<SortedSet<T>.Node?> root,
            Ghost<SpecTree<(T, bool)>> left, Ghost<SpecTree<(T, bool)>> right) { }

        [Lemma, Conditional("PAL"), GhostArg("SortedSetNodeSnapshot<T> record")]
        [Requires("SortedSetOwnership.Raw(root, record, Perm.Full)")]
        [Requires("Holds(SortedSetOwnership.Left(record), left, Perm.Full)")]
        [Requires("Holds(SortedSetOwnership.Right(record), right, Perm.Full)")]
        [Requires("tree == SpecTree.Branch(left, SortedSetOwnership.Entry(record), right)")]
        [Ensures("Holds(root, tree, Perm.Full)")]
        [PulseBody("SortedSetInductive.Construction.seal_as $(root) $(record) $(left) $(right) $(tree)")]
        internal static void SealAs<T>(Ghost<SortedSet<T>.Node?> root,
            Ghost<SpecTree<(T, bool)>> left, Ghost<SpecTree<(T, bool)>> right, Ghost<SpecTree<(T, bool)>> tree) { }

        [Lemma, Conditional("PAL"), GhostArg("SortedSetNodeSnapshot<T> record")]
        [Requires("SortedSetOwnership.Raw(root, record, Perm.Full)")]
        [Requires("Holds(oldLeft, left, Perm.Full)")]
        [Requires("Holds(SortedSetOwnership.Right(record), right, Perm.Full)")]
        [Requires("oldLeft == SortedSetOwnership.Left(record)")]
        [Requires("tree == SpecTree.Branch(left, SortedSetOwnership.Entry(record), right)")]
        [Ensures("Holds(root, tree, Perm.Full)")]
        [PulseBody("SortedSetInductive.Construction.seal_left_input $(root) $(oldLeft) $(record) $(left) $(right) $(tree)")]
        internal static void SealLeftInput<T>(Ghost<SortedSet<T>.Node?> root, Ghost<SortedSet<T>.Node?> oldLeft,
            Ghost<SpecTree<(T, bool)>> left, Ghost<SpecTree<(T, bool)>> right, Ghost<SpecTree<(T, bool)>> tree) { }

        [Lemma, Conditional("PAL"), GhostArg("SortedSetNodeSnapshot<T> parent"), GhostArg("SortedSetNodeSnapshot<T> child")]
        [Preserves("SortedSetOwnership.Raw(root, parent, Perm.Full)")]
        [Requires("SortedSetOwnership.Raw(SortedSetOwnership.Left(parent), child, Perm.Full)")]
        [Requires("Holds(oldLeft, left, Perm.Full)")]
        [Requires("Holds(SortedSetOwnership.Right(child), right, Perm.Full)")]
        [Requires("oldLeft == SortedSetOwnership.Left(child)")]
        [Requires("tree == SpecTree.Branch(left, SortedSetOwnership.Entry(child), right)")]
        [Ensures("Holds(SortedSetOwnership.Left(parent), tree, Perm.Full)")]
        [PulseBody("SortedSetInductive.Construction.seal_left_child $(root) $(oldLeft) $(parent) $(child) $(left) $(right) $(tree)")]
        internal static void SealLeftChild<T>(Ghost<SortedSet<T>.Node?> root, Ghost<SortedSet<T>.Node?> oldLeft,
            Ghost<SpecTree<(T, bool)>> left, Ghost<SpecTree<(T, bool)>> right, Ghost<SpecTree<(T, bool)>> tree) { }

        [Lemma, Conditional("PAL"), GhostArg("SortedSetNodeSnapshot<T> parent"), GhostArg("SortedSetNodeSnapshot<T> child")]
        [Preserves("SortedSetOwnership.Raw(root, parent, Perm.Full)")]
        [Requires("SortedSetOwnership.Raw(SortedSetOwnership.Right(parent), child, Perm.Full)")]
        [Requires("SortedSetOwnership.Left(child) == null && SortedSetOwnership.Right(child) == null")]
        [Requires("tree == SpecTree.Branch(SpecTree.Leaf<(T, bool)>(), SortedSetOwnership.Entry(child), SpecTree.Leaf<(T, bool)>())")]
        [Ensures("Holds(SortedSetOwnership.Right(parent), tree, Perm.Full)")]
        [PulseBody("SortedSetInductive.Construction.seal_right_leaf $(root) $(parent) $(child) $(tree)")]
        internal static void SealRightLeaf<T>(Ghost<SortedSet<T>.Node?> root, Ghost<SpecTree<(T, bool)>> tree) { }

        [Lemma, Conditional("PAL")]
        [Requires("Holds(root, red, Perm.Full)"), Requires("root == null && lo == hi + 1")]
        [Ensures("Holds(null, SpecSearchTree.Build(items, lo, hi, red), Perm.Full)")]
        [PulseBody("SortedSetInductive.Construction.empty_build $(root) $(red) $(items) $(lo) $(hi)")]
        internal static void EmptyBuild<T>(Ghost<SortedSet<T>.Node?> root, Ghost<SpecTree<(T, bool)>> red,
            Ghost<Seq<T>> items, Ghost<SpecInt> lo, Ghost<SpecInt> hi) { }

        [GhostArg("T item"), GhostArg("NodeColor color")]
        [Requires("SortedSetOwnership.Fresh(node, item, color)")]
        [Ensures("Holds(Result, Leaf(item, color == NodeColor.Red), Perm.Full)")]
        [Ensures("Result == node")]
        internal static SortedSet<T>.Node PrepareFresh<T>(SortedSet<T>.Node node)
        {
            SealFresh<T>(node);
            return node;
        }

        [Lemma, Conditional("PAL")]
        [Requires("Holds(root, tree, Perm.Full)"), Requires("!tree.IsLeaf")]
        [Ensures("Opened(root, tree)")]
        [PulseBody("SortedSetInductive.Construction.open_tree $(root) $(tree)")]
        internal static void Open<T>(Ghost<SortedSet<T>.Node?> root, Ghost<SpecTree<(T, bool)>> tree) { }

        [Lemma, Requires("Holds(root, tree, permission)")]
        [Ensures("SortedSetOwnership.Owns(Result, permission)")]
        [Ensures("SortedSetOwnership.Top(Result) == root && SortedSetOwnership.Values(Result) == tree")]
        [PulseBody("SortedSetInductive.Construction.label_tree $(root) $(tree) $(permission)")]
        internal static Ghost<SortedSetLabels<T>> Label<T>(SortedSet<T>.Node? root,
            Ghost<SpecTree<(T, bool)>> tree, Ghost<Perm> permission) => throw new InvalidOperationException();

        [Lemma, Conditional("PAL")]
        [Requires("SortedSetOwnership.Owns(labels, permission)")]
        [Ensures("Holds(SortedSetOwnership.Top(labels), SortedSetOwnership.Values(labels), permission)")]
        [PulseBody("SortedSetInductive.Construction.unlabel $(labels) $(permission)")]
        internal static void Unlabel<T>(Ghost<SortedSetLabels<T>> labels, Ghost<Perm> permission) { }

        [Lemma, Conditional("PAL"), GhostArg("SortedSet<T>.Node? ownedRoot")]
        [Requires("SortedSetOwnership.Owner(ownedRoot, old, Perm.Full)")]
        [Requires("oldRoot == ownedRoot")]
        [Requires("SortedSetOwnership.Owns(labels, Perm.Full)")]
        [Requires("SortedSetOwnership.Top(labels) == root")]
        [Ensures("SortedSetOwnership.Owner(root, Adopted(old, labels), Perm.Full)")]
        [Ensures("SortedSetOwnership.Good(SortedSetOwnership.Active(Adopted(old, labels)))")]
        [Ensures("Pal.Same(SortedSetOwnership.Active(Adopted(old, labels)), labels)")]
        [PulseBody("""
            rewrite (SortedSetInductive.Ownership.owner $(ownedRoot) $(old) 1.0R)
              as (SortedSetInductive.Ownership.owner $(oldRoot) $(old) 1.0R);
            SortedSetInductive.Construction.adopt $(oldRoot) $(root) $(old) (hide $(labels))
            """)]
        internal static void Adopt<T>(Ghost<SortedSet<T>.Node?> oldRoot, SortedSet<T>.Node? root,
            Ghost<SortedSetOwnershipState<T>> old, Ghost<SortedSetLabels<T>> labels) { }
    }
}
