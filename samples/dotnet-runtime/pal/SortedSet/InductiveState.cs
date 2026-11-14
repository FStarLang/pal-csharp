#if PAL
using System;
using System.Diagnostics;
using PalLang;

namespace System.Collections.Generic
{
    [SpecType("SortedSetInductive.State.observation")]
    internal readonly struct SortedSetObservation<T> { }

    internal static class SortedSetState
    {
        [SpecOp("SortedSetInductive.State.observe")]
        internal static SortedSetObservation<T> Observe<T>(SortedSetOwnershipState<T> state) => throw new InvalidOperationException();

        [SpecOp("SortedSetInductive.State.tree_at")]
        internal static SpecTree<(T, bool)> Tree<T>(SortedSetObservation<T> state, SortedSet<T>.Node? node) => throw new InvalidOperationException();

        [SpecOp("SortedSetInductive.State.mem")]
        internal static bool Member<T>(SortedSetObservation<T> state, SortedSet<T>.Node? node) => throw new InvalidOperationException();

        [SpecOp("SortedSetInductive.State.wf")]
        internal static bool WellFormed<T>(SortedSetObservation<T> state, SortedSet<T>.Node? node) => throw new InvalidOperationException();

        [SpecOp("SortedSetInductive.State.pending")]
        internal static Seq<T> Pending<T>(bool reverse, SortedSetObservation<T> state, Seq<SortedSet<T>.Node?> stack) => throw new InvalidOperationException();

        [SpecOp("SortedSetInductive.State.walkable")]
        internal static bool Walkable<T>(SortedSetObservation<T> state, Seq<SortedSet<T>.Node?> stack) => throw new InvalidOperationException();

        [SpecOp("SortedSetInductive.StateFacts.near")]
        internal static SortedSet<T>.Node? Near<T>(bool reverse, SortedSetObservation<T> state, SortedSet<T>.Node? node) => throw new InvalidOperationException();

        [SpecOp("SortedSetInductive.StateFacts.far")]
        internal static SortedSet<T>.Node? Far<T>(bool reverse, SortedSetObservation<T> state, SortedSet<T>.Node? node) => throw new InvalidOperationException();

        [SpecOp("SortedSetInductive.StateOwnerRead.observation")]
        internal static SortedSetObservation<T> SnapshotObservation<T>(SortedSetSnapshot<T> snapshot) => throw new InvalidOperationException();

        [SpecOp("SortedSetInductive.StateOwnerRead.window")]
        internal static SlProp Window<T>(SortedSet<T> owner, SortedSetSnapshot<T> snapshot,
            SortedSetObservation<T> state, SortedSet<T>.Node? node, Perm permission) => throw new InvalidOperationException();

        [SpecOp("SortedSetInductive.StateRead.read_window")]
        internal static SlProp OwnerWindow<T>(SortedSet<T>.Node? root, SortedSetOwnershipState<T> ownership,
            SortedSet<T>.Node? node, Perm permission) => throw new InvalidOperationException();

        [SpecOp("SortedSetInductive.StateOwnerRead.matches")]
        internal static bool Matches<T>(SortedSet<T>.Node? root, SortedSetOwnershipState<T> ownership,
            IComparer<T> comparer, SpecInt count, SpecInt version, SortedSetSnapshot<T> snapshot) => throw new InvalidOperationException();
    }

    internal static class SortedSetStateProof
    {
        [Lemma, Conditional("PAL")]
        [PulseBody("SortedSetInductive.StateActive.active $(ownership)")]
        [Requires("SortedSetOwnership.Good(SortedSetOwnership.Active(ownership))")]
        [Ensures("SortedSetState.WellFormed(SortedSetState.Observe(ownership), SortedSetOwnership.Top(SortedSetOwnership.Active(ownership)))")]
        [Ensures("SortedSetState.Tree(SortedSetState.Observe(ownership), SortedSetOwnership.Top(SortedSetOwnership.Active(ownership))) == SortedSetOwnership.Values(SortedSetOwnership.Active(ownership))")]
        internal static void Active<T>(SortedSetOwnershipState<T> ownership) { }

        [Lemma, Conditional("PAL")]
        [PulseBody("SortedSetInductive.StateRead.open_read $(root) $(ownership) $(node) $(permission)")]
        [Requires("SortedSetOwnership.Owner(root, ownership, permission)")]
        [Requires("SortedSetState.Member(SortedSetState.Observe(ownership), node)")]
        [Ensures("SortedSetState.OwnerWindow(root, ownership, node, permission)")]
        internal static void OpenOwner<T>(SortedSet<T>.Node? root, SortedSetOwnershipState<T> ownership,
            SortedSet<T>.Node? node, Ghost<Perm> permission) { }

        [Lemma, Conditional("PAL")]
        [PulseBody("SortedSetInductive.StateRead.close_read $(root) $(ownership) $(node) $(permission)")]
        [Requires("SortedSetState.OwnerWindow(root, ownership, node, permission)")]
        [Ensures("SortedSetOwnership.Owner(root, ownership, permission)")]
        internal static void CloseOwner<T>(SortedSet<T>.Node? root, SortedSetOwnershipState<T> ownership,
            SortedSet<T>.Node? node, Ghost<Perm> permission) { }

        [Lemma, Conditional("PAL")]
        [GhostArg("SortedSet<T> owner"), GhostArg("SortedSetSnapshot<T> snapshot")]
        [PulseBody("SortedSetInductive.StateOwnerRead.root_facts $(owner) $(snapshot) $(state) $(tree) $(permission)")]
        [Requires("SortedSetOwnership.SetInv(owner, snapshot, permission)")]
        [Requires("Pal.Same(state, SortedSetState.SnapshotObservation(snapshot)) && Pal.Same(tree, SortedSetOwnership.SnapshotLabels(snapshot))")]
        [Ensures("SortedSetOwnership.SetInv(owner, snapshot, permission)")]
        [Ensures("SortedSetState.WellFormed(state, SortedSetOwnership.Top(tree)) && SortedSetState.Tree(state, SortedSetOwnership.Top(tree)) == SortedSetOwnership.Values(tree)")]
        internal static void RootFacts<T>(Ghost<SortedSetObservation<T>> state, Ghost<SortedSetLabels<T>> tree, Ghost<Perm> permission) { }

        [Lemma, Conditional("PAL")]
        [PulseBody("SortedSetInductive.StateFacts.null $(state) $(node)")]
        [Requires("node == null")]
        [Ensures("SortedSetState.WellFormed(state, node) && SortedSetState.Tree(state, node).IsLeaf")]
        internal static void Null<T>(Ghost<SortedSetObservation<T>> state, SortedSet<T>.Node? node) { }

        [Lemma, Conditional("PAL")]
        [PulseBody("SortedSetInductive.StateWalk.empty $(reverse) $(state) $(stack)")]
        [Requires("stack.Length == 0")]
        [Ensures("SortedSetState.Walkable(state, stack) && SortedSetState.Pending(reverse, state, stack).Length == 0")]
        internal static void Empty<T>(bool reverse, Ghost<SortedSetObservation<T>> state, Ghost<Seq<SortedSet<T>.Node?>> stack) { }

        [Lemma, Conditional("PAL")]
        [PulseBody("SortedSetInductive.StateWalk.length $(reverse) $(state) $(stack)")]
        [Requires("SortedSetState.Walkable(state, stack)")]
        [Ensures("stack.Length <= SortedSetState.Pending(reverse, state, stack).Length")]
        internal static void Length<T>(bool reverse, Ghost<SortedSetObservation<T>> state, Ghost<Seq<SortedSet<T>.Node?>> stack) { }

        [Lemma, Conditional("PAL")]
        [PulseBody("SortedSetInductive.StateWalk.descend $(reverse) $(state) $(stack) $(node)")]
        [Requires("SortedSetState.WellFormed(state, node) && node != null && SortedSetState.Walkable(state, stack)")]
        [Ensures("SortedSetState.Member(state, node) && !SortedSetState.Tree(state, node).IsLeaf")]
        [Ensures("SortedSetState.WellFormed(state, SortedSetState.Near(reverse, state, node)) && SortedSetState.WellFormed(state, SortedSetState.Far(reverse, state, node))")]
        [Ensures("SortedSetState.Walkable(state, Pal.Snoc(stack, node))")]
        [Ensures("SortedSetState.Tree(state, SortedSetState.Near(reverse, state, node)).Size < SortedSetState.Tree(state, node).Size && SortedSetState.Tree(state, SortedSetState.Far(reverse, state, node)).Size < SortedSetState.Tree(state, node).Size")]
        [Ensures("stack.Length < SpecWalk.Keys(reverse, SortedSetState.Tree(state, node)).Length + SortedSetState.Pending(reverse, state, stack).Length")]
        [Ensures("Pal.Concat(SpecWalk.Keys(reverse, SortedSetState.Tree(state, node)), SortedSetState.Pending(reverse, state, stack)) == Pal.Concat(SpecWalk.Keys(reverse, SortedSetState.Tree(state, SortedSetState.Near(reverse, state, node))), SortedSetState.Pending(reverse, state, Pal.Snoc(stack, node)))")]
        internal static void Descend<T>(bool reverse, Ghost<SortedSetObservation<T>> state, Ghost<Seq<SortedSet<T>.Node?>> stack, SortedSet<T>.Node node) { }

        [Lemma, Conditional("PAL")]
        [PulseBody("SortedSetInductive.StateWalk.pop_at $(reverse) $(state) $(stack) $(keys) $(offset)")]
        [Requires("stack.Length > 0 && SortedSetState.Walkable(state, stack) && 0 <= offset && offset <= keys.Length && SortedSetState.Pending(reverse, state, stack) == Pal.Slice(keys, offset, keys.Length)")]
        [Ensures("offset < keys.Length && stack[stack.Length - 1] != null && SortedSetState.Member(state, stack[stack.Length - 1]) && SortedSetState.WellFormed(state, stack[stack.Length - 1])")]
        [Ensures("SortedSetState.Walkable(state, Pal.Slice(stack, 0, stack.Length - 1)) && SortedSetState.WellFormed(state, SortedSetState.Far(reverse, state, stack[stack.Length - 1]))")]
        [Ensures("Pal.Same(SpecSearchTree.RootKey(SortedSetState.Tree(state, stack[stack.Length - 1]), keys[offset]), keys[offset])")]
        [Ensures("Pal.Concat(SpecWalk.Keys(reverse, SortedSetState.Tree(state, SortedSetState.Far(reverse, state, stack[stack.Length - 1]))), SortedSetState.Pending(reverse, state, Pal.Slice(stack, 0, stack.Length - 1))) == Pal.Slice(keys, offset + 1, keys.Length)")]
        internal static void PopAt<T>(bool reverse, Ghost<SortedSetObservation<T>> state, Ghost<Seq<SortedSet<T>.Node?>> stack, Ghost<Seq<T>> keys, SpecInt offset) { }

        [Lemma, Conditional("PAL")]
        [GhostArg("SortedSet<T> owner"), GhostArg("SortedSetSnapshot<T> snapshot")]
        [PulseBody("SortedSetInductive.StateOwnerRead.open_set $(owner) $(snapshot) $(state) $(node) $(permission)")]
        [Requires("SortedSetOwnership.SetInv(owner, snapshot, permission)")]
        [Requires("Pal.Same(state, SortedSetState.SnapshotObservation(snapshot)) && SortedSetState.Member(state, node)")]
        [Ensures("SortedSetState.Window(owner, snapshot, state, node, permission)")]
        internal static void Open<T>(Ghost<SortedSetObservation<T>> state, SortedSet<T>.Node? node, Ghost<Perm> permission) { }

        [Lemma, Conditional("PAL")]
        [GhostArg("SortedSet<T> owner"), GhostArg("SortedSetSnapshot<T> snapshot")]
        [PulseBody("SortedSetInductive.StateOwnerRead.close_set $(owner) $(snapshot) $(state) $(node) $(permission)")]
        [Requires("SortedSetState.Window(owner, snapshot, state, node, permission)")]
        [Ensures("SortedSetOwnership.SetInv(owner, snapshot, permission)")]
        internal static void Close<T>(Ghost<SortedSetObservation<T>> state, SortedSet<T>.Node? node, Ghost<Perm> permission) { }
    }
}
#endif
