using System.Collections.Generic;
using PalLang;

namespace PalCSharp.Tests.Inductive;

public static partial class RbTree
{
    [Requires("RbCursorSpec.Owns(nodes)")]
    [Requires("RbCursorSpec.Good(nodes) && root == RbCursorSpec.Top(nodes)")]
    [Requires("SpecSearchTree.IsRedBlack(RbCursorSpec.Strip(nodes)) && Pal.StrictlySorted(comparer, SpecSearchTree.Keys(RbCursorSpec.Strip(nodes)))")]
    [Ensures("RbRemoveSpec.Labelled(Result, comparer, SpecSearchTree.Keys(RbCursorSpec.Strip(nodes)), key)")]
    [Ensures("RbSpec.Detached(removed)")]
    [Ensures("Pal.Iff(removed == null, Pal.KeyIndex(comparer, SpecSearchTree.Keys(RbCursorSpec.Strip(nodes)), key) < 0)")]
    private static RbNode<T>? RemoveTopDown<T>(RbNode<T>? root, T key, IComparer<T> comparer,
        out RbNode<T>? removed, Ghost<RbLabels<T>> nodes = default)
    {
#if PAL
        Ghost<Seq<T>> keys = SpecSearchTree.Keys(RbCursorSpec.Strip(nodes.Value));
        RbState<T> state = RbState.Start(nodes);
#endif
        RbNode<T>? result = root;
        RbNode<T>? current = root;
        RbNode<T>? parent = root;
        RbNode<T>? grandParent = root;
        RbNode<T>? match = root;
        RbNode<T>? parentOfMatch = root;
        parent = null;
        grandParent = null;
        match = null;
        parentOfMatch = null;
        bool foundMatch = false;
        RbRemoveProof.Start(comparer, key, nodes);
        while (current != null)
        {
#if PAL
            Pal.Decreases(RbRemoveSpec.Measure(RbState.Labels(state), current));
            Pal.Invariant(comparer == Pal.Old(comparer));
            Pal.Invariant(RbCursorSpec.Owns(RbState.Labels(state)));
            Pal.Invariant(result == RbCursorSpec.Top(RbState.Labels(state)));
            Pal.Invariant(RbRemoveSpec.Inv(comparer, keys.Value, key, RbState.Labels(state),
                current, parent, grandParent, match, parentOfMatch, foundMatch));
            Ghost<RbLabels<T>> before = RbState.Labels(state);
            RbCursorProof.Change<T>(RbState.Labels(state), before);
            Ghost<SpecInt> measure = RbRemoveSpec.Measure(before.Value, current);
            RbRemoveProof.AtCur(comparer, keys, key, before, current, parent, grandParent, match, parentOfMatch, foundMatch);
#endif
            if (Is2At(current))
            {
                if (parent == null)
                {
#if PAL
                    RbRemoveProof.Root(comparer, keys, key, before, current, parent, grandParent, match, parentOfMatch, foundMatch);
                    RbBalanceProof.TopColor(current, true, before);
#endif
                    RecolorAt(current, true);
#if PAL
                    state = RbState.Recolor(state, current, true);
                    RbCursorProof.Change<T>(RbMutationSpec.Recolor(before.Value, current, true), RbState.Labels(state));
#endif
                }
                else
                {
#if PAL
                    RbRemoveProof.AtSibling(comparer, keys, key, before, current, parent, grandParent, match, parentOfMatch, foundMatch);
#endif
                    RbNode<T>? sibling = SiblingAt(parent, current);
                    if (IsRedAt(sibling))
                    {
#if PAL
                        RbRemoveProof.Lift(comparer, keys, key, before, current, parent, grandParent, match, parentOfMatch, foundMatch);
#endif
                        result = LiftSibling(result, parent, grandParent, sibling!);
#if PAL
                        Ghost<RbLabels<T>> lifted = RbRemoveSpec.Lifted(before.Value, parent, current);
                        state = RbState.Start(lifted);
                        RbCursorProof.Change<T>(RbLiftSpec.Whole(before.Value, parent, sibling!), RbState.Labels(state));
#endif
                        grandParent = sibling;
                        if (parent == match)
                            parentOfMatch = sibling;
#if PAL
                        RbRemoveProof.AtMid(comparer, keys, key, RbState.Labels(state), current, parent, grandParent, match, parentOfMatch, foundMatch, measure.Value);
#endif
                        sibling = SiblingAt(parent, current);
                    }
#if PAL
                    else
                    {
                        RbRemoveProof.Direct(comparer, keys, key, before, current, parent, grandParent, match, parentOfMatch, foundMatch);
                        RbCursorProof.Change<T>(before, RbState.Labels(state));
                    }
                    Pal.Join(RbCursorSpec.Owns(RbState.Labels(state)));
                    Pal.Join(result == RbCursorSpec.Top(RbState.Labels(state)));
                    Pal.Join(RbRemoveSpec.Mid(comparer, keys.Value, key, RbState.Labels(state),
                        current, parent, grandParent, match, parentOfMatch, foundMatch, measure.Value));
                    Pal.Join(current != null && parent != null && sibling != null);
                    Pal.Join(sibling == RbRemoveSpec.Sibling(RbState.Labels(state), parent, current));
                    Ghost<RbLabels<T>> middle = RbState.Labels(state);
                    RbCursorProof.Change<T>(RbState.Labels(state), middle);
                    RbRemoveProof.AtMid(comparer, keys, key, middle, current, parent, grandParent, match, parentOfMatch, foundMatch, measure.Value);
#endif
                    if (Is2At(sibling!))
                    {
#if PAL
                        RbRemoveProof.Merge(comparer, keys, key, middle, current, parent, grandParent, match, parentOfMatch, foundMatch, measure.Value);
#endif
                        Merge2At(parent!);
#if PAL
                        Ghost<RbLabels<T>> merged = RbRemoveSpec.Merged(middle.Value, parent);
                        state = RbState.Start(merged);
                        RbCursorProof.Change<T>(RbLinkSpec.Replace(middle.Value, parent, RbRemoveLocalSpec.Merge(RbLinkSpec.Sub(middle.Value, parent))),
                            RbState.Labels(state));
#endif
                    }
                    else
                    {
#if PAL
                        RbRemoveProof.Borrow(comparer, keys, key, middle, current, parent, grandParent, match, parentOfMatch, foundMatch, measure.Value);
#endif
                        RbRemovalRotation rotation = GetRemovalRotation(parent!, current!, sibling!);
#if PAL
                        Pal.Assert(rotation == RbRemoveSpec.Rotation(middle.Value, parent, current));
#endif
                        RbNode<T> newGrandParent = parent!;
                        result = BorrowAt(result, parent!, grandParent, current!, rotation, out newGrandParent);
#if PAL
                        Ghost<RbLabels<T>> borrowed = RbRemoveSpec.Borrowed(middle.Value, parent, current);
                        state = RbState.Start(borrowed);
                        RbCursorProof.Change<T>(RbLinkSpec.Replace(middle.Value, parent, RbBorrowSpec.Borrowed(RbLinkSpec.Sub(middle.Value, parent), current!, rotation)),
                            RbState.Labels(state));
#endif
                        if (parent == match)
                            parentOfMatch = newGrandParent;
                    }
#if PAL
                    Pal.Join(RbCursorSpec.Owns(RbState.Labels(state)));
                    Pal.Join(result == RbCursorSpec.Top(RbState.Labels(state)));
                    Pal.Join(RbRemoveSpec.Fixed(comparer, keys.Value, key, RbState.Labels(state),
                        current, parent, match, parentOfMatch, foundMatch, measure.Value));
#endif
                }
#if PAL
                Pal.Join(RbCursorSpec.Owns(RbState.Labels(state)));
                Pal.Join(result == RbCursorSpec.Top(RbState.Labels(state)));
                Pal.Join(RbRemoveSpec.Fixed(comparer, keys.Value, key, RbState.Labels(state),
                    current, parent, match, parentOfMatch, foundMatch, measure.Value));
#endif
            }
#if PAL
            else
            {
                RbRemoveProof.Not2(comparer, keys, key, before, current, parent, grandParent, match, parentOfMatch, foundMatch);
                RbCursorProof.Change<T>(before, RbState.Labels(state));
            }
            Pal.Join(RbCursorSpec.Owns(RbState.Labels(state)));
            Pal.Join(result == RbCursorSpec.Top(RbState.Labels(state)));
            Pal.Join(RbRemoveSpec.Fixed(comparer, keys.Value, key, RbState.Labels(state),
                current, parent, match, parentOfMatch, foundMatch, measure.Value));
            Ghost<RbLabels<T>> after = RbState.Labels(state);
            RbCursorProof.Change<T>(RbState.Labels(state), after);
            RbRemoveProof.AtFixed(comparer, keys, key, after, current, parent, match, parentOfMatch, foundMatch, measure.Value);
#endif
            int order = RemovalOrder(current!, key, comparer, foundMatch);
#if PAL
            RbRemoveProof.Advance(comparer, keys, key, after, current, parent, match, parentOfMatch, foundMatch, measure.Value, order);
#endif
            if (order == 0)
            {
                foundMatch = true;
                match = current;
                parentOfMatch = parent;
            }
            grandParent = parent;
            parent = current;
#if PAL
            RbCursorProof.Open(current!, after);
#endif
            RbNode<T>? next = order < 0 ? current!.left : current!.right;
#if PAL
            RbCursorProof.Close(current!, after);
            RbCursorProof.Change<T>(after, RbState.Labels(state));
#endif
            current = next;
        }
#if PAL
        Ghost<RbLabels<T>> descentModel = RbState.Labels(state);
        RbCursorProof.Change<T>(RbState.Labels(state), descentModel);
        RbRemoveProof.End(comparer, keys, key, descentModel, parent, grandParent, match, parentOfMatch, foundMatch);
#endif
        bool hasMatch = match != null;
        if (hasMatch)
        {
            result = ReplaceNode(result, match!, parentOfMatch, parent!, grandParent);
#if PAL
            Ghost<RbLabels<T>> replaced = RbSuccessorSpec.Delete(descentModel.Value, match!);
            state = RbState.Start(replaced);
            RbCursorProof.Change<T>(RbSuccessorSpec.Delete(descentModel.Value, match!), RbState.Labels(state));
#endif
        }
        else
        {
            RbRemoveProof.NullDetached(match);
#if PAL
            RbCursorProof.Change<T>(descentModel, RbState.Labels(state));
#endif
        }
#if PAL
        Pal.Join(RbCursorSpec.Owns(RbState.Labels(state)));
        Pal.Join(RbSpec.Detached(match));
        Pal.Join(result == RbCursorSpec.Top(RbState.Labels(state)));
        Pal.Join(RbAddSpec.Ok(comparer, RbRemoveSpec.Expected(comparer, keys.Value, key), RbState.Labels(state)));
        Pal.Join(Pal.Iff(match == null, Pal.KeyIndex(comparer, keys.Value, key) < 0));
        Ghost<RbLabels<T>> final = RbState.Labels(state);
        RbCursorProof.Change<T>(RbState.Labels(state), final);
        RbRemoveProof.Finish(comparer, keys, key, final);
#endif
        RecolorAt(result, false);
#if PAL
        RbCursorProof.Change<T>(RbMutationSpec.Recolor(final.Value, result, false), RbSplitSpec.Color(final.Value, false));
#endif
        removed = match;
        return result;
    }
}
