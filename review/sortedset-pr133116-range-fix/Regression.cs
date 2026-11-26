using System.Collections.Generic;
using System.Linq;
using Xunit;

public class ViewRangeRegression
{
    // BEGIN UPSTREAM TEST
    [Theory]
    [InlineData(false, 0)]
    [InlineData(false, 9)]
    [InlineData(true, 0)]
    [InlineData(true, 9)]
    public void SetComparisons_GetViewBetween_ExcludeOutOfRangeElements(bool fromEnumerable, int outside)
    {
        SortedSet<int> set;
        if (fromEnumerable)
        {
            set = new SortedSet<int>(Enumerable.Range(0, 10));
        }
        else
        {
            set = new SortedSet<int>();
            for (int i = 0; i < 10; i++)
                set.Add(i);
        }

        SortedSet<int> view = set.GetViewBetween(2, 5);
        List<int> sameCount = new List<int> { 2, 3, 4, outside };

        Assert.False(view.SetEquals(sameCount));
        Assert.False(view.IsSubsetOf(sameCount));
        Assert.False(view.IsProperSubsetOf(new List<int> { 2, 3, 4, outside, 10 }));
        Assert.False(view.IsProperSupersetOf(new List<int> { 2, 3, outside }));
    }
    // END UPSTREAM TEST
}
