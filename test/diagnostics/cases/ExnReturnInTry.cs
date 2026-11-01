// EXPECT: PALCS0614
// A `return` inside a `try` would leave the try by a path its `ensures` does not
// describe (R19.3); assign a local and return after the try instead.
using System;
using PalLang;

public sealed class Oops2 : Exception
{
}

public static class ReturnsFromTry
{
    public static int F(int x)
    {
        try
        {
            return x;
        }
        catch (Oops2)
        {
            return 0;
        }
    }
}
