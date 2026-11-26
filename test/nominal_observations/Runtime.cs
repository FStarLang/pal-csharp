using System;
using System.Collections.Generic;

// Executed by the CLR with proof assertions erased.
public static class Runtime
{
    public static int Main()
    {
        IComparer<int> first = Comparer<int>.Create((x, y) => x.CompareTo(y));
        IComparer<int> second = Comparer<int>.Create((x, y) => y.CompareTo(x));
        bool ordinary = ObservationClient.Ordinary(7, first);
        bool borrowed = ObservationClient.View(7, first, second);
        bool helpers = HelperClient.Run(7, first, second);
        bool misses = MissClient.Ordinary(7, first) && MissClient.View(7, first)
            && SequenceProtocolClient.Miss(7);
        bool iterators = SequenceProtocolClient.Hit(7);
        var owner = new Packet<int>(7, first);
        Packet<int> view = owner.EmptyView(second);
        IEnumerable<int> source = view;
        Packet<int> cast = source as Packet<int>;
        using IEnumerator<int> iterator = source.GetEnumerator();
        bool actual = ReferenceEquals(cast, view) && cast.Count == 0 &&
            ReferenceEquals(cast.Comparer, second) && owner.Count == 1 &&
            ReferenceEquals(owner.Comparer, first) && !iterator.MoveNext();
        bool viewHelper = ((Packet<int>.Empty)view).CompareHere(new Packet<int>(7, first));
        Console.WriteLine($"ordinary={ordinary}; view={borrowed}; identity-and-slots={actual}; helpers={helpers && viewHelper}; misses={misses}; iterators={iterators}");
        return ordinary && borrowed && actual && helpers && viewHelper && misses && iterators ? 0 : 1;
    }
}
