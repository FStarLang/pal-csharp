using System.Collections.Generic;
using PalLang;

public static class HelperClient
{
    [Ensures("Result")]
    public static bool Run<T>(T value, IComparer<T> first, IComparer<T> second)
    {
        var receiver = new Packet<T>(value, first);
        var source = new Packet<T>(value, second);
        bool ordinary = receiver.CompareObserved(source);
        var sourceView = source.EmptyView(second);
        bool views = receiver.CompareObserved(sourceView);
        int count = sourceView.Count;
        IComparer<T> order = sourceView.Comparer;
        return ordinary && views && count == 0 && order == second;
    }
}
