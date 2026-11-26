// EXPECT: PALCS0865
using System.Collections;
using System.Collections.Generic;
using PalLang;
[assembly: TranslateAnnotatedOnly]
public sealed class FirstCastTarget : IEnumerable<int>
{
    private int[] items;
    [Model] private Seq<int> Model => Pal.Contents(items);
    public IEnumerator<int> GetEnumerator() => throw new System.NotImplementedException();
    IEnumerator IEnumerable.GetEnumerator() => GetEnumerator();
}
public sealed class SecondCastTarget : IEnumerable<int>
{
    private int[] items;
    [Model] private Seq<int> Model => Pal.Contents(items);
    public IEnumerator<int> GetEnumerator() => throw new System.NotImplementedException();
    IEnumerator IEnumerable.GetEnumerator() => GetEnumerator();
}
public static class EnumerableCastMultipleTargets
{
    [Ensures("true")]
    public static void Test(IEnumerable<int> other)
    {
        if (other is FirstCastTarget first) { }
        if (other is SecondCastTarget second) { }
    }
}
