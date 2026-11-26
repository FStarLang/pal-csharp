// EXPECT: PALCS0865
using System.Collections;
using System.Collections.Generic;
using PalLang;

[assembly: TranslateAnnotatedOnly]

public class EnumerableTestBase : IEnumerable<int>
{
    private int value;
    [Model] private SpecInt Model => value;
    public IEnumerator<int> GetEnumerator() => throw new System.NotImplementedException();
    IEnumerator IEnumerable.GetEnumerator() => GetEnumerator();
}

public static class EnumerableClassIs
{
    // This must include possible subclasses, not just exact runtime equality.
    [Ensures("true")]
    public static bool Test(IEnumerable<int> other) => other is EnumerableTestBase;
}
