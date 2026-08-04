using PalLang;

namespace PalCSharp.Tests;

/// <summary>
/// §10 with two recursive fields. Nothing in the scheme is about lists: the model member
/// is inverted the same way whatever its constructor's arity, and the number of recursive
/// arguments is the number of sub-invariants each node owns.
///
/// <para>Two subtrees is where separating conjunction earns its keep. Writing through
/// <c>left</c> while <c>right</c>'s invariant sits untouched in the context is a step that
/// needs no framing lemma at all — it is what <c>**</c> means.</para>
/// </summary>
public sealed class TreeNode
{
    internal int value;
    internal TreeNode? left;
    internal TreeNode? right;

    /// <summary>
    /// R10.5, at arity three. The recursive arguments are <c>left</c> and <c>right</c>;
    /// everything else in the application is a pure function of the fields, and becomes a
    /// pure conjunct of the node's invariant.
    /// </summary>
    [Model]
    private SpecTree<SpecInt> Contents => SpecTree.Branch(left!.Contents, value, right!.Contents);

    /// <summary>R3.10b. How a client names the whole model.</summary>
    [Spec]
    public SpecTree<SpecInt> Elements => Contents;

    [Ensures("@this.Elements == SpecTree.Branch(l.Elements, v, r.Elements)")]
    public TreeNode(int v, TreeNode? l, TreeNode? r)
    {
        value = v;
        left = l;
        right = r;
    }
}
