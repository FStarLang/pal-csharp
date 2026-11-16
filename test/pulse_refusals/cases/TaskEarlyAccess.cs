// EXPECT-PULSE: pts_to
using System.Threading.Tasks;
using PalLang;

public static class TaskEarlyAccess
{
    [Requires("a.Length > 0")]
    [Ensures("a[0] == 9")]
    public static async Task Change(int[] a)
    {
        await Task.Delay(1);
        a[0] = 9;
    }

    [Requires("a.Length > 0")]
    public static async Task<int> Premature(int[] a)
    {
        Task pending = Change(a);
        // MARKER
        int x = a[0];
        await pending;
        return x;
    }
}
