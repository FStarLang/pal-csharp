using PalLang;

namespace System.Collections.Generic
{
    internal static class SortedSetPublicRegression
    {
        [Ensures("Result.SpecComparer == Comparer<int>.Default")]
        [Ensures("Result.SpecItems.Length <= 10 && Result.SpecVersion == 10")]
        internal static SortedSet<int> CreateSet()
        {
            var set = new SortedSet<int>();
            for (int i = 0; i < 10; i++)
            {
                Pal.Invariant(0 <= i && i <= 10);
                Pal.Invariant(set.SpecItems.Length <= i && set.SpecVersion == i);
                Pal.Invariant(set.SpecComparer == Comparer<int>.Default);
                set.Add(i);
            }
            return set;
        }

        [Ensures("Result.Items.Length == 4 && Result.Items[0] == 2 && Result.Items[1] == 3 && Result.Items[2] == 4 && Result.Items[3] == 9")]
        internal static List<int> CreateOther()
        {
            var other = new List<int>();
            other.Add(2);
            other.Add(3);
            other.Add(4);
            other.Add(9);
            return other;
        }

        [Ensures("!Result")]
        internal static bool ViewSetEqualsListFalse()
        {
            var set = CreateSet();
            var view = set.GetViewBetween(2, 5);
            var other = new List<int>();
            other.Add(2);
            other.Add(3);
            other.Add(4);
            other.Add(9);
            SortedSetCount.RangeMisses(set.SpecComparer, 2, 5, true, true,
                set.SpecItems, other.Items, 3);
            return view.SetEquals(other);
        }

        [Ensures("!Result")]
        internal static bool ViewExcludesNine()
        {
            var set = CreateSet();
            int lower = 2;
            int upper = 5;
            var view = set.GetViewBetween(lower, upper);
            var other = CreateOther();
            SortedSetCount.RangeMisses(set.SpecComparer, lower, upper, true, true,
                set.SpecItems, other.Items, 3);
            Pal.Assert(!SortedSetCount.AllHit(view.SpecComparer, view.SpecItems, other.Items));
            return view.Contains(9);
        }
    }
}
