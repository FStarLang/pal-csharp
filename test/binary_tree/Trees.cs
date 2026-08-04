using PalLang;

namespace PalCSharp.Tests;

public static class Trees
{
    /// <summary>
    /// R10.7 with two windows' worth of content in one. The single null test opens the
    /// node, and both subtrees are then reachable and separately owned, so the two
    /// recursive calls need nothing said about how they do not interfere.
    /// </summary>
    [Requires("t.Elements.Size < 1073741823")]
    [Ensures("Result == t.Elements.Size")]
    [Decreases("t.Elements")]
    public static int Size(TreeNode? t)
    {
        if (t == null)
        {
            return 0;
        }
        return 1 + Size(t.left) + Size(t.right);
    }

    /// <summary>
    /// R10.9. An in-place binary-search-tree insert, and the case §10 is really about: the
    /// write goes through one subtree's field while the <em>other</em> subtree's invariant
    /// sits untouched in the context. Nothing has to be said about the two not interfering,
    /// because separating conjunction is what the invariant is built out of.
    ///
    /// <para>The postcondition is the whole of correctness — the tree afterwards is
    /// <em>the</em> tree the mathematical insertion produces, not merely a tree that
    /// contains <c>v</c>. Per §0 rule 3 that model comes from the reusable library
    /// (<c>Pulse.Lib.CSharp.Tree.insert</c>), which is where a proof gets help when the
    /// user's annotations are not the right place for it.</para>
    ///
    /// <para>R5.4. Each arm ends in its own <c>return</c> rather than falling through to a
    /// shared one, because the arms leave the object in <em>different</em> states — one
    /// subtree has been replaced — and a statement-position <c>if</c> has to leave a single
    /// one. Writing the branches as tail positions is the ordinary C# for that, and it is
    /// what lets each arm close the window at the state it actually reached.</para>
    /// </summary>
    [Ensures("Result.Elements == SpecTree.Insert(t.Elements, v)")]
    [Decreases("t.Elements")]
    public static TreeNode? Insert([Consumes] TreeNode? t, int v)
    {
        if (t == null)
        {
            return new TreeNode(v, null, null);
        }
        else if (v < t.value)
        {
            t.left = Insert(t.left, v);
            return t;
        }
        else if (v > t.value)
        {
            t.right = Insert(t.right, v);
            return t;
        }
        else
        {
            return t;
        }
    }
}
