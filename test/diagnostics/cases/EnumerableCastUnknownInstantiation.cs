// EXPECT: PALCS0866
using System.Collections;
using System.Collections.Generic;
using PalLang;
[assembly: TranslateAnnotatedOnly]
public sealed class GenericCastBox<T> : IEnumerable<int>
{
    private int[] items;
    [Model] private Seq<int> Model => Pal.Contents(items);
    public IEnumerator<int> GetEnumerator() => throw new System.NotImplementedException();
    IEnumerator IEnumerable.GetEnumerator() => GetEnumerator();
}
public static class EnumerableCastUnknownInstantiation
{
    [Ensures("true")]
    public static bool Test(IEnumerable<int> other)
    {
        if (other is GenericCastBox<int> found) return true;
        return false;
    }
    [Ensures("true")]
    public static bool Unknown<T>(GenericCastBox<T> source) => Test(source);
}
