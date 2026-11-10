// R30.42, R30.43. Joined `if`s whose conditions are not a single plain test: a
// short-circuit `&&` with a call on its right, which R35.15 nests, keeps its join on the
// outer `if`; and a null test of a field, which narrows nothing, can be joined.
using PalLang;
#pragma warning disable CS0649

internal delegate bool JoinVisit<T>(JoinTree<T>.JNode node);

[Spec]
public struct JoinTreeModel<T>
{
    public SpecTree<(T, bool)> Tree;
}

public sealed class JoinTree<T>
{
    private JNode? root;

    [Model]
    private JoinTreeModel<T> Model => new JoinTreeModel<T> { Tree = Pal.Tree<(T, bool)>(root) };

    [Spec] public SpecTree<(T, bool)> SpecNodes => Model.Tree;

    [Ensures("@this.SpecNodes.IsLeaf")]
    public JoinTree()
    {
        root = null;
    }

    // R30.43: `r.Left != null` is joined. R30.42: `r.Right != null && IsRed(r.Right)` is
    // nested; the join is on its outer test, itself a field's null test.
    [Ensures("0 <= Result && Result <= 2")]
    [Ensures("@this.SpecNodes == Pal.Old(@this.SpecNodes)")]
    [Frac("p")]
    internal int Children()
    {
        JNode? r = root;
        if (r == null)
        {
            return 0;
        }
        int n = 0;
        if (r.Left != null)
        {
            n = n + 1;
        }
        Pal.Join(0 <= n && n <= 1);
        if (r.Right != null && JNode.IsRedNode(r.Right))
        {
            n = n + 1;
        }
        Pal.Join(0 <= n && n <= 2);
        return n;
    }

    // R30.42. A callback on the right of `&&`: the trace the arm leaves is the join's
    // existential, and what follows is checked once, against the join's facts.
    [Requires("1 <= Pal.CallBound(action)")]
    [Ensures("Pal.Implies(Result != 2, Pal.Trace<(T, bool), bool>(action).Length == (b ? 1 : 0))")]
    [Ensures("Pal.Implies(Result == 1, b)")]
    [Frac("p")]
    internal int VisitRoot(bool b, [Callback(Bounded = true)] JoinVisit<T> action)
    {
        JNode? r = root;
        if (r == null)
        {
            return 2;
        }
        int k = 0;
        if (b && !action(r))
        {
            k = 1;
        }
        Pal.Join(Pal.Trace<(T, bool), bool>(action).Length == (b ? 1 : 0));
        Pal.Join(Pal.Implies(k == 1, b) && 0 <= k && k <= 1);
        k = k + 0;
        return k;
    }

    [Region]
    internal sealed class JNode
    {
        public T Item;
        public JNode? Left;
        public JNode? Right;
        public bool IsRed;

        public JNode(T item, bool isRed)
        {
            Item = item;
            IsRed = isRed;
        }

        [Model]
        private (T, bool) View => (Item, IsRed);

        [Requires("node == null || Pal.InRegion(node)")]
        [Ensures("Result == (node != null && Pal.InRegion(node) && SpecSearchTree.IsRed(Pal.Tree<(T, bool)>(node)))")]
        public static bool IsRedNode(JNode? node) => node != null && node.IsRed;
    }
}
