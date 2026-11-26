using PalLang;

public static class Clients
{
    [Ensures("Result")]
    public static bool RoundTrip<T>(T item)
    {
        RbTree<T> tree = new RbTree<T>();
        bool first = tree.Add(item);
        bool duplicate = tree.Add(item);
        bool present = tree.Contains(item);
        int one = tree.Count;
        bool removed = tree.Remove(item);
        bool missing = tree.Remove(item);
        bool absent = !tree.Contains(item);
        int zero = tree.Count;
        return first && !duplicate && present && one == 1 &&
               removed && !missing && absent && zero == 0;
    }

    [Ensures("Result")]
    public static bool ClearAndReuse<T>(T first, T second)
    {
        RbTree<T> tree = new RbTree<T>();
        tree.Add(first);
        tree.Clear();
        bool empty = tree.Count == 0 && !tree.Contains(first);
        bool inserted = tree.Add(second);
        return empty && inserted && tree.Contains(second) && tree.Count == 1;
    }
}
