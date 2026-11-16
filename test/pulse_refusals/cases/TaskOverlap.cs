// EXPECT-PULSE: pts_to
using System.Threading.Tasks;
using PalLang;

public static class TaskOverlap
{
    [Requires("a.Length > 0")]
    [Ensures("a[0] == 9")]
    public static async Task Change(int[] a)
    {
        await Task.Delay(1);
        a[0] = 9;
    }

    [Requires("a.Length > 0")]
    public static async Task Race(int[] a)
    {
        Task first = Change(a);
        // MARKER
        Task second = Change(a);
        await first;
        await second;
    }
}
