// EXPECT: PALCS0001
using System.Threading.Tasks;
using PalLang;

public static class AsyncVoid
{
    [Ensures("true")]
    public static async void Lost() { await Task.Delay(1); }
}
