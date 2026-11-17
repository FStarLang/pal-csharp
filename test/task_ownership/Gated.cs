using System;
using System.Threading.Tasks;
using PalLang;

[assembly: TranslateAnnotatedOnly]

public static class Suspension
{
    public static Func<Task> Wait = () => Task.CompletedTask;

#pragma warning disable PALCS0904
    [Implements("()")]
    [Ensures("true")]
    public static Task Pause() => Wait();
#pragma warning restore PALCS0904
}

public static class Chunked
{
#pragma warning disable PALCS0904
    [Implements("A.write $&(a) 0l $(value)")]
    [Requires("a.Length > 0")]
    [Ensures("a[0] == value")]
    public static async Task BoundWrite(byte[] a, byte value)
    {
        await Suspension.Pause();
        a[0] = value;
    }
#pragma warning restore PALCS0904

    [Ensures("Pal.Forall((int i) => Pal.Implies(0 <= i && i < a.Length, a[i] == value))")]
    public static async Task Populate(byte[] a, byte value)
    {
        int i = 0;
        while (i < a.Length)
        {
            Pal.Invariant(0 <= i && i <= a.Length);
            Pal.Invariant(Pal.Forall((int j) => Pal.Implies(0 <= j && j < i, a[j] == value)));
            await Suspension.Pause();
            a[i] = value;
            i++;
        }
    }

    [Ensures("Pal.Forall((int i) => Pal.Implies(0 <= i && i < a.Length, a[i] == 3))")]
    [Ensures("Pal.Forall((int i) => Pal.Implies(0 <= i && i < b.Length, b[i] == 7))")]
    public static async Task Both(byte[] a, byte[] b)
    {
        Task first = Populate(a, 3);
        Task second = Populate(b, 7);
        await second;
        await first;
    }
}
