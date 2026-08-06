using PalLang;

namespace PalCSharp.Tests;

/// <summary>
/// §15's generic recursive class at arity two: <c>test/binary_tree</c>'s <c>TreeNode</c>
/// with its payload abstracted. The type parameter is the <em>value</em> type only — the
/// order lives in an <c>int</c> key beside it, because R15.4 refuses a constrained type
/// parameter and so <c>where T : IComparable&lt;T&gt;</c> is not available to say what
/// order a search tree is in.
///
/// <para>That is not a workaround for the refusal. A C# tree ordered by
/// <c>IComparable&lt;T&gt;</c> is ordered by a method the caller may override, and its
/// specification would have to quantify over what that method does; a tree ordered by an
/// <c>int</c> key is ordered by arithmetic, and <c>Pulse.Lib.CSharp.Tree.kv</c> can say so
/// in one line. The map is the specifiable half of the two.</para>
/// </summary>
public sealed class TreeNode<T>
{
    internal int key;
    internal T value;
    internal TreeNode<T>? left;
    internal TreeNode<T>? right;

    /// <summary>
    /// R10.5 at arity three, R15.5 at the payload. <c>SpecTree.Entry(key, value)</c> is a
    /// pure function of two fields and so becomes a pure conjunct of the node's invariant;
    /// only <c>left</c> and <c>right</c> are recursive arguments, and only they become
    /// sub-invariants.
    /// </summary>
    [Model]
    private SpecTree<SpecKv<T>> Contents =>
        SpecTree.Branch(left!.Contents, SpecTree.Entry(key, value), right!.Contents);

    /// <summary>R3.10b. How a client names the whole model.</summary>
    [Spec]
    public SpecTree<SpecKv<T>> Elements => Contents;

    [Ensures("@this.Elements == SpecTree.Branch(l.Elements, SpecTree.Entry(k, v), r.Elements)")]
    public TreeNode(int k, T v, TreeNode<T>? l, TreeNode<T>? r)
    {
        key = k;
        value = v;
        left = l;
        right = r;
    }
}
