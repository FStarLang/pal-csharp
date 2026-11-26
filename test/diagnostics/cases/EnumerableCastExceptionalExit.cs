// EXPECT: PALCS0866
using System.Collections;
using System.Collections.Generic;
using PalLang;
[assembly: TranslateAnnotatedOnly]
public sealed class EarlyCastTarget : IEnumerable<int>
{
    private int[] items;
    [Model] private Seq<int> Model => Pal.Contents(items);
    public IEnumerator<int> GetEnumerator() => throw new System.NotImplementedException();
    IEnumerator IEnumerable.GetEnumerator() => GetEnumerator();
}
public static class EnumerableCastExceptionalExit
{
    [Ensures("true")]
    public static bool Test(IEnumerable<int> other)
    {
        if (other is EarlyCastTarget found) throw new System.InvalidOperationException();
        return false;
    }
}
