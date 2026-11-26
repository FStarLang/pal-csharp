// EXPECT: PALCS0866
using System.Collections;
using System.Collections.Generic;
using PalLang;
[assembly: TranslateAnnotatedOnly]
public sealed class ReuseCastTarget : IEnumerable<int>
{
    private int[] items;
    [Model] private Seq<int> Model => Pal.Contents(items);
    public IEnumerator<int> GetEnumerator() => throw new System.NotImplementedException();
    IEnumerator IEnumerable.GetEnumerator() => GetEnumerator();
}
public static class EnumerableCastSourceReuse
{
    [Ensures("true")]
    public static void Test(IEnumerable<int> other)
    {
        if (other is ReuseCastTarget found)
        {
            using IEnumerator<int> e = other.GetEnumerator();
        }
    }
}
