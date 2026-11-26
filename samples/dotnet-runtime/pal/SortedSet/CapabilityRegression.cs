using PalLang;

namespace System.Collections.Generic
{
    internal static class SortedSetCapabilityRegression
    {
        [Ensures("!Result")]
        internal static bool StaticView()
        {
            var set = SortedSetPublicRegression.CreateSet();
            var view = set.GetViewBetween(2, 5);
            return view.Contains(9);
        }
    }
}
