using System.Threading.Tasks;
using PalLang;

public static class Downloads
{
    [Ensures("Result == x")]
    public static Task<int> Ready(int x) => Task.FromResult(x);

    [Ensures("Result == x")]
    public static async Task<int> Later(int x)
    {
        await Task.Delay(1);
        return await Ready(x);
    }

    [Requires("a.Length > 0")]
    [Ensures("a[0] == x")]
    public static async Task Put(int[] a, int x)
    {
        await Task.Delay(1);
        a[0] = x;
    }

    [Requires("a.Length > 0")]
    [Ensures("a[0] == x")]
    public static Task Forward(int[] a, int x) => Put(a, x);

    [Requires("a.Length > 0 && b.Length > 0")]
    [Ensures("a[0] == 17 && b[0] == 29")]
    public static async Task Pair(int[] a, int[] b)
    {
        Task first = Forward(a, 17);
        Task alias = first;
        Task second = Put(b, 29);
        await second;
        await alias;
    }

    [Ensures("Result == 42")]
    public static async Task<int> Nested()
    {
        int x = await Later(42);
        await Task.CompletedTask;
        return x;
    }
}
