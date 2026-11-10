using System;
using System.Diagnostics;
using PalLang;

public static class Semantics
{
    [Ensures("Result == (x ^ y)")]
    public static bool Xor(bool x, bool y) => x ^ y;

    [Ensures("Result == (x & y)")]
    public static bool And(bool x, bool y) => x & y;

    [Ensures("Result == (x | y)")]
    public static bool Or(bool x, bool y) => x | y;

    [Ensures("Result == 1")]
    public static int EagerAnd(bool x)
    {
        int n = 0;
        bool ignored = x & (++n == 1);
        return n;
    }

    [Ensures("Result == (x ? 1 : 0)")]
    public static int ShortAnd(bool x)
    {
        int n = 0;
        bool ignored = x && (++n == 1);
        return n;
    }

    [Ensures("Result == first")]
    public static int First(int first, int second) => first;

    [Ensures("Result == 1")]
    public static int Named() => First(first: 1, second: 2);

    public static byte Narrow(int x) => (byte)x;

    [Ensures("Result == x")]
    public static int Widen(byte x) => checked((int)x);

    [Ensures("Result == 0")]
    public static int DebugErasure()
    {
        int n = 0;
        Debug.Assert(++n == 1);
        Debug.Fail($"erased message {++n}");
        return n;
    }

    [Ensures("Result == 10")]
    public static int ArrayOps()
    {
        int[] a = new int[3];
        a[1] = 7;
        return a[1] + a.Length;
    }

    [Ensures("Result == 10")]
    public static int ArrayAndSpan()
    {
        int[] a = new int[3];
        Span<int> s = a.AsSpan(1, 2);
        s[0] = 7;
        int n = s.Length;
        Pal.Restore(s);
        return a[1] + a.Length;
    }
}
