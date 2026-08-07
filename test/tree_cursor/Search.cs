using PalLang;

namespace PalCSharp.Tests;

/// <summary>
/// An iterative lookup in a search tree, and the two operations that build one for it to
/// look in.
///
/// <para>Compare <c>test/generic_tree</c>, where every operation recurses. That was not a
/// choice about trees: §10's derived invariant gives a caller no way to name the part of a
/// structure a loop has already passed, so a loop over one cannot be specified and recursion
/// is all that is left (§10.7). <c>test/list_cursor</c> removed that limitation for a chain.
/// This file is the claim that it was removed for *structures*, not for chains — the
/// predicate underneath is a one-hole context rather than a segment, and the C# above it is
/// the same three-part invariant, the same lemma-call-per-step, and the same absence of raw
/// Pulse.</para>
/// </summary>
public static class Search
{
    /// <summary>The empty tree.</summary>
    [Ensures("Descent.Holds(Result, SpecTree.Leaf<SpecKv<T>>())")]
    public static Knot<T>? Empty<T>()
    {
        DescentProof.Empty<T>();
        return null;
    }

    /// <summary>
    /// A node over two trees the caller already owns. Together with <see cref="Empty"/> this
    /// is enough to build any tree at all, which is all a lookup needs — an insertion that
    /// preserves the search order is a separate exercise, and one that wants the ordering
    /// hypothesis this file is careful not to need.
    /// </summary>
    [Requires("Descent.Holds(left, lt)")]
    [Requires("Descent.Holds(right, rt)")]
    [Ensures("Descent.Holds(Result, SpecTree.Branch(lt, SpecTree.Entry(key, value), rt))")]
    public static Knot<T> Node<T>(int key, T value, Knot<T>? left, Knot<T>? right,
                                  Ghost<SpecTree<SpecKv<T>>> lt = default,
                                  Ghost<SpecTree<SpecKv<T>>> rt = default)
    {
        Knot<T> node = new Knot<T> { key = key, value = value, left = left, right = right };
        DescentProof.Node(node, key, value, left, right, lt, rt);
        return node;
    }

    /// <summary>
    /// Look <paramref name="key"/> up by descending from the root, and return
    /// <paramref name="fallback"/> if it is not there.
    ///
    /// <para>The postcondition is <c>SpecTree.Get</c> — the library's model of a lookup, not
    /// a paraphrase of what the loop happens to do. That is the whole point of the
    /// exercise: the caller gets a fact about the map, and never has to know that a spine or
    /// a step counter existed.</para>
    ///
    /// <para><b>No ordering hypothesis appears anywhere in this file.</b> That is not an
    /// omission. <c>SpecTree.Get</c> on a branch is *defined* by comparing the key with the
    /// entry, so a descent that follows that comparison is following the definition, and
    /// agrees with it whether or not the tree is sorted. A search tree that is out of order
    /// makes the lookup useless, not unsound, and this specification says exactly that.</para>
    ///
    /// <para>Three lines carry the loop, and they are <see cref="Walks.Count"/>'s three lines
    /// with a context in place of a prefix:</para>
    /// <list type="bullet">
    ///   <item>the spine already descended, <c>Ctx(t, key, n)</c>;</item>
    ///   <item>the subtree still to search, <c>Sub(t, key, n)</c>;</item>
    ///   <item>the arithmetic relating <c>n</c> to both.</item>
    /// </list>
    /// <para>A descent's path is not a prefix of anything — but the path a *search* takes is
    /// determined by the tree and the key, and both are fixed for the whole loop. So the two
    /// halves are functions of the counter just as <c>Take</c> and <c>Drop</c> are, and R5.8
    /// quantifies them with no new machinery.</para>
    ///
    /// <para>The other new thing is the <c>live</c> flag. A search has two exits — the bottom
    /// of the tree, and a hit — and C# would write the second as <c>break</c>, which R5.10
    /// does not implement. An <c>int</c> flag as the loop condition needs no new rule, and
    /// the measure <c>Sub(t, key, n).Size + live</c> falls on both exits: a descent shrinks
    /// the subtree, a stop clears the flag. Note that it *has* to be the subtree's size and
    /// not the counter — a tree has no length for <c>n</c> to be bounded by, which is the one
    /// place where being a tree really does cost something.</para>
    /// </summary>
    [Requires("Descent.Holds(root, t)")]
    [Requires("t.Size < 2147483647")]
    [Ensures("Descent.Holds(root, t)")]
    [Ensures("Pal.Same(Result, SpecTree.Get(t, key, fallback))")]
    public static T Find<T>(Knot<T>? root, int key, T fallback,
                            Ghost<SpecTree<SpecKv<T>>> t = default)
    {
        DescentProof.Start(root, key, t);
        Knot<T>? cur = root;
        int n = 0;
        T found = fallback;
        int live = 1;
        while (live != 0)
        {
            Pal.Invariant(Descent.Spine(root, cur, Descent.Ctx(t.Value, key, n)));
            Pal.Invariant(Descent.Holds(cur, Descent.Sub(t.Value, key, n)));
            Pal.Invariant(0 <= n && (live == 0 || live == 1));
            Pal.Invariant(t.Value.Size < 2147483647);
            Pal.Invariant(n + Descent.Sub(t.Value, key, n).Size <= t.Value.Size);
            Pal.Invariant(Pal.Implies(live == 0,
                Pal.Same(found, SpecTree.Get(t.Value, key, fallback))));
            Pal.Decreases(Descent.Sub(t.Value, key, n).Size + live);

            DescentProof.AtEnd(cur, key, n, t);
            if (cur == null)
            {
                // The bottom: the remaining subtree is a leaf, so the key is not in the tree
                // (`AtEnd`) and a key the map does not hold reads back as the fallback
                // (`Absent`).
                DescentProof.Absent(key, fallback, t);
                found = fallback;
                live = 0;
            }
            else
            {
                DescentProof.Open(cur, Descent.Sub(t.Value, key, n));
                int nk = cur.key;
                T nv = cur.value;
                Knot<T>? nl = cur.left;
                Knot<T>? nr = cur.right;
                if (key == nk)
                {
                    DescentProof.Found(cur, nv, nl, nr, key, n, fallback, t);
                    found = nv;
                    live = 0;
                }
                else if (key < nk)
                {
                    DescentProof.Left(root, cur, nv, nl, nr, key, n, t);
                    cur = nl;
                    n = n + 1;
                }
                else
                {
                    DescentProof.Right(root, cur, nv, nl, nr, key, n, t);
                    cur = nr;
                    n = n + 1;
                }
            }
        }

        // One `Close`, for both exits. The spine and the remaining subtree compose at every
        // point on the path, so where the descent stopped does not matter — the same line
        // that ends a search at the bottom ends one that found what it was looking for.
        DescentProof.Close(root, cur, key, n, t);
        return found;
    }
}
