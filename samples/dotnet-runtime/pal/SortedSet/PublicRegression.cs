using PalLang;

[assembly: IncludePulseFile("SortedSetPublicRegression.fst")]

namespace System.Collections.Generic
{
    internal static class SortedSetPublicRegression
    {
        [SpecOp("SortedSetPublicRegression.prefix")]
        internal static bool Prefix(Seq<int> items, SpecInt length) => throw new InvalidOperationException();

        [System.Diagnostics.Conditional("PAL"), SpecOp("SortedSetPublicRegression.grow")]
        internal static void Grow(Seq<int> items, int next) { }

        [System.Diagnostics.Conditional("PAL"), SpecOp("SortedSetPublicRegression.snoc")]
        internal static void Snoc(Seq<int> items, int next) { }

        [System.Diagnostics.Conditional("PAL"), SpecOp("SortedSetPublicRegression.same")]
        internal static void Same(Seq<int> left, Seq<int> right, SpecInt length) { }

        [System.Diagnostics.Conditional("PAL"), SpecOp("SortedSetPublicRegression.same_hits")]
        internal static void SameHits(IComparer<int> comparer, Seq<int> left, Seq<int> right) { }

        [Ensures("Result.SpecComparer == Comparer<int>.Default && Prefix(Result.SpecItems, 256) && Result.SpecVersion == 256")]
        internal static SortedSet<int> CreateLargeSet()
        {
            var set = new SortedSet<int>();
            for (int i = 0; i < 256; i++)
            {
                Pal.Invariant(0 <= i && i <= 256 && Prefix(set.SpecItems, i));
                Pal.Invariant(set.SpecComparer == Comparer<int>.Default);
                Pal.Invariant(set.SpecVersion == i);
                Pal.Assert(SpecWrap.Int32(i + 1) == i + 1);
                Grow(set.SpecItems, i);
                set.Add(i);
                Pal.Assert(set.SpecVersion == i + 1);
            }
            return set;
        }

        [Requires("other.Items.Length == 0")]
        [Ensures("other.Items.Length == 6 && other.Items[5] == 300")]
        internal static void FillLargeOther(List<int> other)
        {
            other.Add(2);
            other.Add(3);
            other.Add(4);
            Pal.Assert(other.Items.Length == 3);
            other.Add(4);
            other.Add(5);
            other.Add(300);
        }

        [Ensures("!Result")]
        internal static bool LargeViewSetEqualsListFalse()
        {
            var set = CreateLargeSet();
            var view = set.GetViewBetween(0, 255);
            var other = new List<int>();
            FillLargeOther(other);
            SortedSetCount.RangeMisses(set.SpecComparer, 0, 255, true, true,
                set.SpecItems, other.Items, 5);
            return view.SetEquals(other);
        }

        [Ensures("Result")]
        internal static bool LargeSetEqualsListTrue()
        {
            var set = CreateLargeSet();
            var other = new List<int>();
            for (int i = 0; i < 256; i++)
            {
                Pal.Invariant(0 <= i && i <= 256 && Prefix(other.Items, i));
                Snoc(other.Items, i);
                other.Add(i);
            }
            Same(set.SpecItems, other.Items, 256);
            bool result = set.SetEquals(other);
            SameHits(set.SpecComparer, set.SpecItems, other.Items);
            return result;
        }

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
