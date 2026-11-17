// EXPECT-PULSE: pending
using System.Threading.Tasks;
using PalLang;

public static class TaskDoubleAwait
{
    [Ensures("true")]
    public static async Task Twice()
    {
        Task pending = Task.Delay(1);
        Task alias = pending;
        await pending;
        // MARKER
        await alias;
    }
}
