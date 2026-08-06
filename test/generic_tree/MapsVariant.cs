using PalLang;

namespace PalCSharp.Tests;

/// <summary>
/// §7.2's variant of <see cref="Maps"/>. The null tests are at the opposite polarity, the
/// key comparisons are written with their operands the other way round and in the opposite
/// order, the recursive results are bound to locals before being combined, the height's
/// maximum is taken the other way, and the type parameter is spelled differently. Same
/// programs, different C#; no emitter change.
/// </summary>
public static class MapsVariant
{
    [Requires("node.Elements.Size < 1073741823")]
    [Ensures("Result == node.Elements.Size")]
    [Decreases("node.Elements")]
    public static int Count<V>([Frac("q")] TreeNode<V>? node)
    {
        if (node != null)
        {
            int a = Count(node.right);
            int b = Count(node.left);
            return a + b + 1;
        }
        return 0;
    }

    [Requires("node.Elements.Height < 1073741823")]
    [Ensures("Result == node.Elements.Height")]
    [Decreases("node.Elements")]
    public static int Depth<V>([Frac("q")] TreeNode<V>? node)
    {
        if (node != null)
        {
            int a = Depth(node.left);
            int b = Depth(node.right);
            if (b >= a)
            {
                return b + 1;
            }
            return a + 1;
        }
        return 0;
    }

    [Ensures("Result == SpecTree.HasKey(node.Elements, id)")]
    [Decreases("node.Elements")]
    public static bool Holds<V>([Frac("q")] TreeNode<V>? node, int id)
    {
        if (node != null)
        {
            if (node.key < id)
            {
                return Holds(node.right, id);
            }
            if (node.key > id)
            {
                return Holds(node.left, id);
            }
            return true;
        }
        return false;
    }

    [Ensures("Pal.Same(Result, SpecTree.Get(node.Elements, id, none))")]
    [Decreases("node.Elements")]
    public static V Lookup<V>([Frac("q")] TreeNode<V>? node, int id, V none)
    {
        if (node != null)
        {
            if (node.key < id)
            {
                return Lookup(node.right, id, none);
            }
            if (node.key > id)
            {
                return Lookup(node.left, id, none);
            }
            return node.value;
        }
        return none;
    }

    [Ensures("Result.Elements == SpecTree.Insert(node.Elements, id, val)")]
    [Decreases("node.Elements")]
    public static TreeNode<V>? Put<V>([Consumes] TreeNode<V>? node, int id, V val)
    {
        if (node != null)
        {
            if (node.key > id)
            {
                node.left = Put(node.left, id, val);
                return node;
            }
            if (node.key < id)
            {
                node.right = Put(node.right, id, val);
                return node;
            }
            node.value = val;
            return node;
        }
        return new TreeNode<V>(id, val, null, null);
    }

    [Ensures("Result.Elements == node.Elements")]
    [Decreases("node.Elements")]
    public static TreeNode<V>? Clone<V>([Frac("q")] TreeNode<V>? node)
    {
        if (node != null)
        {
            TreeNode<V>? l = Clone(node.left);
            TreeNode<V>? r = Clone(node.right);
            return new TreeNode<V>(node.key, node.value, l, r);
        }
        return null;
    }
}
