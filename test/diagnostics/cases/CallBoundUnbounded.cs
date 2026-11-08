// EXPECT: PALCS0800
// R32.11. A lambda states a bound on its calls, but the parameter it is passed to does not
// take one: the callee never promised to call fewer times than that bound.
using PalLang;

internal delegate bool Visit<T>(Tree<T>.Node node);

[Spec]
public struct TreeModel<T>
{
    public SpecTree<(T, bool)> Nodes;
}

public sealed class Tree<T>
{
    private Node? root;

    [Model] private TreeModel<T> Model => new TreeModel<T> { Nodes = Pal.Tree<(T, bool)>(root) };

    public Tree() { root = null; }

    [Ensures("true")]
    [Frac("p")]
    internal bool Walk([Callback] Visit<T> action)
    {
        return true;
    }

    [Ensures("true")]
    internal void Count()
    {
        int n = 0;
        Walk(node =>
        {
            Pal.Protocol<(T, bool), bool>(tr => true, 3);
            n++;
            return true;
        });
    }

    [Region]
    internal sealed class Node
    {
        public T Item;
        public Node? Left;
        public Node? Right;
        public bool IsRed;

        public Node(T item, bool isRed)
        {
            Item = item;
            IsRed = isRed;
        }

        [Model]
        private (T, bool) View => (Item, IsRed);
    }
}
