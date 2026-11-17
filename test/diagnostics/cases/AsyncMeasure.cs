// EXPECT: PALCS0001
using System.Threading.Tasks;
using PalLang;

public static class AsyncMeasure
{
    [Requires("n >= 0")]
    public static async Task Count(int n)
    {
        while (n > 0)
        {
            Pal.Invariant(n >= 0);
            Pal.Decreases(n);
            await Task.Delay(1);
            n--;
        }
    }
}
