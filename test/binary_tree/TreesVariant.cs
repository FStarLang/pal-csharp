using PalLang;

namespace PalCSharp.Tests;

/// <summary>
/// §7.2's variant of <see cref="Trees"/>. The null tests are at the opposite polarity, the
/// comparisons are written with their operands the other way round, the recursive sums are
/// bound to locals and re-associated, and the insertion's arms are ordered differently.
/// Same programs, different C#; no emitter change.
/// </summary>
public static class TreesVariant
{
    [Requires("node.Elements.Size < 1073741823")]
    [Ensures("Result == node.Elements.Size")]
    [Decreases("node.Elements")]
    public static int Count(TreeNode? node)
    {
        if (node != null)
        {
            int below = Count(node.left) + Count(node.right);
            return below + 1;
        }
        else
        {
            return 0;
        }
    }

    [Ensures("Result.Elements == SpecTree.Insert(node.Elements, key)")]
    [Decreases("node.Elements")]
    public static TreeNode? Add([Consumes] TreeNode? node, int key)
    {
        if (node != null)
        {
            if (node.value > key)
            {
                node.left = Add(node.left, key);
                return node;
            }
            else if (node.value < key)
            {
                node.right = Add(node.right, key);
                return node;
            }
            else
            {
                return node;
            }
        }
        else
        {
            return new TreeNode(key, null, null);
        }
    }
}
