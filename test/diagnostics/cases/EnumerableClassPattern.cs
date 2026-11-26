// EXPECT: PALCS0865
using System.Collections;
using System.Collections.Generic;
using PalLang;

[assembly: TranslateAnnotatedOnly]

public sealed class EnumerablePatternCell : IEnumerable<int>
{
    private int value;
    [Model] private SpecInt Model => value;
    public IEnumerator<int> GetEnumerator() => throw new System.NotImplementedException();
    IEnumerator IEnumerable.GetEnumerator() => GetEnumerator();
}

public static class EnumerableClassPattern
{
    [Ensures("true")]
    public static bool Test(IEnumerable<int> other) =>
        other is EnumerablePatternCell cell;
}
