using PalLang;

namespace PalCSharp.Tests;

/// <summary>
/// A generic search tree keyed by <c>int</c>. Every postcondition here is functional
/// correctness against <c>Pulse.Lib.CSharp.Tree</c>'s keyed layer — the tree a method
/// returns is <em>the</em> tree the mathematical operation produces, and the value a lookup
/// returns is <em>the</em> value the mathematical lookup produces — never merely a
/// structural property of the result.
/// </summary>
public static class Maps
{
    /// <summary>
    /// R10.7 with two subtrees under one window. The single null test opens the node and
    /// both subtrees become separately owned, so the two recursive calls need nothing said
    /// about how they fail to interfere: that is what <c>**</c> already means.
    /// </summary>
    [Requires("t.Elements.Size < 1073741823")]
    [Ensures("Result == t.Elements.Size")]
    [Decreases("t.Elements")]
    public static int Size<T>([Frac("p")] TreeNode<T>? t)
    {
        if (t == null)
        {
            return 0;
        }
        return 1 + Size(t.left) + Size(t.right);
    }

    /// <summary>The longest path to a leaf.</summary>
    [Requires("t.Elements.Height < 1073741823")]
    [Ensures("Result == t.Elements.Height")]
    [Decreases("t.Elements")]
    public static int Height<T>([Frac("p")] TreeNode<T>? t)
    {
        if (t == null)
        {
            return 0;
        }
        int l = Height(t.left);
        int r = Height(t.right);
        if (l > r)
        {
            return 1 + l;
        }
        return 1 + r;
    }

    /// <summary>
    /// Whether the map holds <paramref name="k"/>. The three-way comparison is the one
    /// <c>Pulse.Lib.CSharp.Tree.kfind</c> makes, in the same order, which is what lets the
    /// postcondition be an equality rather than an implication.
    /// </summary>
    [Ensures("Result == SpecTree.HasKey(t.Elements, k)")]
    [Decreases("t.Elements")]
    public static bool ContainsKey<T>([Frac("p")] TreeNode<T>? t, int k)
    {
        if (t == null)
        {
            return false;
        }
        if (k < t.key)
        {
            return ContainsKey(t.left, k);
        }
        if (k > t.key)
        {
            return ContainsKey(t.right, k);
        }
        return true;
    }

    /// <summary>
    /// The value at <paramref name="k"/>, or <paramref name="fallback"/>. A lookup that
    /// returns a value rather than a nullable reference, because <c>T</c> is unconstrained
    /// and so has no <c>null</c> — and R15.6's <c>Pal.Same</c> states the postcondition,
    /// because C# refuses <c>==</c> on an unconstrained <c>T</c> for the same reason.
    /// </summary>
    [Ensures("Pal.Same(Result, SpecTree.Get(t.Elements, k, fallback))")]
    [Decreases("t.Elements")]
    public static T GetOr<T>([Frac("p")] TreeNode<T>? t, int k, T fallback)
    {
        if (t == null)
        {
            return fallback;
        }
        if (k < t.key)
        {
            return GetOr(t.left, k, fallback);
        }
        if (k > t.key)
        {
            return GetOr(t.right, k, fallback);
        }
        return t.value;
    }

    /// <summary>
    /// R10.9 at a generic class: an in-place insertion, where the write goes through one
    /// subtree's field while the <em>other</em> subtree's invariant sits untouched in the
    /// context.
    ///
    /// <para>R5.4. Each arm ends in its own <c>return</c>, because the arms leave the node
    /// in different states — a different subtree has been replaced in each — and a
    /// statement-position <c>if</c> has to leave a single one.</para>
    /// </summary>
    [Ensures("Result.Elements == SpecTree.Insert(t.Elements, k, v)")]
    [Decreases("t.Elements")]
    public static TreeNode<T>? Insert<T>([Consumes] TreeNode<T>? t, int k, T v)
    {
        if (t == null)
        {
            return new TreeNode<T>(k, v, null, null);
        }
        else if (k < t.key)
        {
            t.left = Insert(t.left, k, v);
            return t;
        }
        else if (k > t.key)
        {
            t.right = Insert(t.right, k, v);
            return t;
        }
        else
        {
            t.value = v;
            return t;
        }
    }

    /// <summary>
    /// A fresh tree with the same entries, in the persistent style
    /// <c>test/generic_list</c>'s operations use: what it returns it allocated, so its
    /// argument stays <c>[Frac]</c>-observed.
    /// </summary>
    [Ensures("Result.Elements == t.Elements")]
    [Decreases("t.Elements")]
    public static TreeNode<T>? Copy<T>([Frac("p")] TreeNode<T>? t)
    {
        if (t == null)
        {
            return null;
        }
        return new TreeNode<T>(t.key, t.value, Copy(t.left), Copy(t.right));
    }
}
