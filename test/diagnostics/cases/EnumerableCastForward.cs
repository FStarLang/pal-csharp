// EXPECT: PALCS0866
using System.Collections;
using System.Collections.Generic;
using PalLang;
[assembly: TranslateAnnotatedOnly]
public sealed class ForwardCastTarget : IEnumerable<int>
{
    private int[] items;
    [Model] private Seq<int> Model => Pal.Contents(items);
    public IEnumerator<int> GetEnumerator() => throw new System.NotImplementedException();
    IEnumerator IEnumerable.GetEnumerator() => GetEnumerator();
}
public static class EnumerableCastForward
{
    [Ensures("true")]
    public static bool Test(IEnumerable<int> other)
    {
        bool answer = false;
        if (other is ForwardCastTarget found) { answer = true; }
        return answer;
    }
    [Ensures("true")]
    public static bool Forward(IEnumerable<int> unknown) => Test(unknown);
}
