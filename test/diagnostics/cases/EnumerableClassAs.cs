// EXPECT: PALCS0865
using System.Collections;
using System.Collections.Generic;
using PalLang;

[assembly: TranslateAnnotatedOnly]

public sealed class EnumerableCastCell : IEnumerable<int>
{
    private int value;
    [Model] private SpecInt Model => value;
    public IEnumerator<int> GetEnumerator() => throw new System.NotImplementedException();
    IEnumerator IEnumerable.GetEnumerator() => GetEnumerator();
}

public static class EnumerableClassAs
{
    // Neither assume failure nor fabricate an owned cell from an item snapshot.
    [Ensures("true")]
    public static bool Test(IEnumerable<int> other) =>
        (other as EnumerableCastCell) != null;
}
