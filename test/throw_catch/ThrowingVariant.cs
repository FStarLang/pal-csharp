// The §7.2 contortion detector for §19: the same contracts as Throwing.cs, written
// differently. The throw becomes the value of an `else` (a tail, R19.2), the loop a
// `while`, and the base-class handler a catch-all with no variable.
using System;
using PalLang;

public static class ThrowingVariant
{
    [Ensures("Result == x && x >= 0")]
    [Throws(typeof(RangeError), "x < 0 && Thrown.Code == 1 && Thrown.Index == 0")]
    public static int NonNegative(int x)
    {
        if (x >= 0)
        {
            return x;
        }
        else
        {
            throw new RangeError(1, 0);
        }
    }

    [Requires("a.Length <= 1000")]
    [Ensures("Result >= 0")]
    [Throws(typeof(LimitError), "a.Length > 25 && Thrown.Code == 25")]
    [Throws(typeof(RangeError), "Thrown.Code == 2 && 0 <= Thrown.Index && Thrown.Index < a.Length && Contents(a)[Thrown.Index] < 0")]
    public static int CheckAll(int[] a)
    {
        if (!(a.Length <= 25))
        {
            throw new LimitError();
        }
        int i = 0;
        while (i < a.Length)
        {
            Pal.Invariant(0 <= i && i <= a.Length);
            Pal.Decreases(a.Length - i);
            if (!(a[i] >= 0))
            {
                throw new RangeError(2, i);
            }
            i = i + 1;
        }
        return i;
    }

    [Requires("a.Length <= 1000")]
    [Ensures("Result >= 0 - 2")]
    public static int Classify(int[] a)
    {
        int result = 0;
        try
        {
            Pal.Invariant(result >= 0 - 2);
            result = CheckAll(a);
        }
        catch (Exception)
        {
            result = 0 - 1;
        }
        return result;
    }
}
