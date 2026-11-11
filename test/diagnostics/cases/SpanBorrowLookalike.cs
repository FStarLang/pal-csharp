// EXPECT: PALCS0590
using PalLang;

[assembly: TranslateAnnotatedOnly]

public static class ArrayBorrowLookalike
{
    public static System.Span<int> AsSpan(this int[] array) => new(array, 0, 0);
}

public static class SpanBorrowLookalike
{
    [Requires("Contents(array).Length > 0")]
    [Ensures("Result == Contents(array).Length")]
    public static int Count(int[] array)
    {
        var window = array.AsSpan();
        int length = window.Length;
        Pal.Restore(window);
        return length;
    }
}
