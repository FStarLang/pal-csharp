// EXPECT: PALCS0614
// Pulse's `try` has no clause that runs on every exit (R19.4).
using System;
using PalLang;

public sealed class Oops : Exception
{
}

public static class UsesFinally
{
    public static int F(int x)
    {
        int r = 0;
        try
        {
            r = x;
        }
        finally
        {
            r = 1;
        }
        return r;
    }
}
