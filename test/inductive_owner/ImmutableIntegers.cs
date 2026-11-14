using PalLang;

namespace PalCSharp.Tests;

public static class ImmutableIntegers
{
    [Requires("0 <= calls && calls < int.MaxValue")]
    [Ensures("calls == Pal.Old(calls) + 1 && Result == value")]
    public static int Observe(int value, ref int calls)
    {
        calls++;
        return value;
    }

    [Requires("0 <= calls && calls < int.MaxValue")]
    [Ensures("calls == Pal.Old(calls) + 1 && Result == (left ? 7 : 11)")]
    public static int Once(bool left, ref int calls)
    {
        int result;
        if (left)
        {
            int local = Observe(7, ref calls);
            result = local;
        }
        else
        {
            int local = Observe(11, ref calls);
            result = local;
        }
        Pal.Join(calls == Pal.Old(calls) + 1 && result == (left ? 7 : 11));
        return result;
    }

    [Requires("0 <= calls && calls < int.MaxValue")]
    [Ensures("calls == Pal.Old(calls) + 1")]
    [Ensures("OwnerSpec.Held(Result, left ? 7 : 11)")]
    public static OwnedCell Make(bool left, ref int calls)
    {
        if (left)
        {
            int local = Observe(7, ref calls);
            return new OwnedCell(local);
        }
        else
        {
            int local = Observe(11, ref calls);
            return new OwnedCell(local);
        }
    }

    [Requires("value < int.MaxValue")]
    [Ensures("value == Pal.Old(value) + 1")]
    public static void Bump(ref int value) { value++; }

    [Ensures("Result == Pal.Old(value) && value == Pal.Old(value)")]
    public static int Peek(in int value) => value;

    [Ensures("value == 8")]
    public static void Set(out int value) { value = 8; }

    [Ensures("Result == 8")]
    public static int ByRef()
    {
        int local = 7;
        Bump(ref local);
        return local;
    }

    [Ensures("Result == 8")]
    public static int Assigned()
    {
        int local = 7;
        local = 8;
        return local;
    }

    [Ensures("Result == (write ? 8 : 7)")]
    public static int Nested(bool write)
    {
        int local = 7;
        if (write) { { local = 8; } }
        return local;
    }

    [Ensures("Result == 7")]
    public static int InCall()
    {
        int local = 7;
        return Peek(in local);
    }

    [Ensures("Result == 8")]
    public static int OutCall()
    {
        int local = 7;
        Set(out local);
        return local;
    }

    [Ensures("Result == 7")]
    public static int RawScope()
    {
        int local = 7;
        Pal.GhostStmt("assert (pure (True))");
        return local;
    }
}
