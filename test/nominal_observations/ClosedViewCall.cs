using System.Collections.Generic;
using PalLang;

public static class ClosedViewCall
{
    [Ensures("Result")]
    public static bool Run<T>(T value, IComparer<T> first, IComparer<T> second)
    {
        var receiver = new Packet<T>(value, first);
        var view = receiver.EmptyView(first);
        var source = new Packet<T>(value, second);
        return view.CompareObserved(source);
    }
}
