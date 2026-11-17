// EXPECT: PALCS0001
using System.Threading.Tasks;
using PalLang;

public static class AsyncRecovery
{
    [Ensures("true")]
    public static async Task Recover()
    {
        try { await Task.Delay(1); }
        catch { }
    }
}
