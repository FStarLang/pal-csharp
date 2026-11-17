// EXPECT-PULSE: 7
using System.Threading.Tasks;
using PalLang;

public static class TaskFalsePromise
{
    [Ensures("Result == 7")]
    public static async Task<int> Wrong()
    {
        await Task.Delay(1);
        // MARKER
        return 8;
    }
}
