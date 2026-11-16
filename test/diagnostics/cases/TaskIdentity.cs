// EXPECT: PALCS0001
using System.Threading.Tasks;
using PalLang;

public static class TaskIdentity
{
    [Ensures("true")]
    public static bool Observe() => Task.CompletedTask == Task.CompletedTask;
}
