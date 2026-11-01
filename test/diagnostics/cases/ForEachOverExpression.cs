// EXPECT: PALCS0620
using PalLang;

public static class ForEachOverExpression
{
    public static int Bad()
    {
        int n = 0;
        foreach (var x in new int[3]) { n = x; }
        return n;
    }
}
