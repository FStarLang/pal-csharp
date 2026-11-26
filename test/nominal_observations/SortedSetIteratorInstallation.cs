using PalLang;

namespace System.Collections.Generic;

// Two independent owners: this probe makes no self-aliasing or overlapping-view
// claim. The actual public call demands installation of the view's inherited
// enumeration protocol and its concrete iterator implementations.
internal static class SortedSetIteratorInstallation
{
    [Ensures("!Result")]
    internal static bool ListFalse()
    {
        var source = SortedSetPublicRegression.CreateSet();
        var view = source.GetViewBetween(2, 5);
        var other = new List<int>();
        other.Add(2);
        other.Add(3);
        other.Add(4);
        other.Add(9);
        SortedSetCount.RangeMisses(source.SpecComparer, 2, 5, true, true,
            source.SpecItems, other.Items, 3);
        return view.SetEquals(other);
    }

    [Requires("receiver.SpecItems.Length <= 126 && source.SpecItems.Length <= 126")]
    [Requires("source.SpecVersion != -1")]
    [Requires("receiver.SpecComparer == Comparer<int>.Default && source.SpecComparer == Comparer<int>.Default")]
    internal static bool View(SortedSet<int> receiver, SortedSet<int> source)
    {
        var view = source.GetViewBetween(2, 5);
        return receiver.SetEquals(view);
    }

    [Requires("receiver.SpecItems.Length <= 126")]
    [Requires("receiver.SpecComparer == Comparer<int>.Default")]
    internal static bool Ordinary(SortedSet<int> receiver)
    {
        var source = new SortedSet<int>();
        source.Add(2);
        return receiver.SetEquals(source);
    }
}
