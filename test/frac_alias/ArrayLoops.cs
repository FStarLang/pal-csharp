using PalLang;

namespace PalCSharp.Tests;

public static class ReadOnlyArrayLoops
{
    public static int Length([Frac("p")] int[] a) => a.Length;

    public static void BodyCall([Frac("p")] int[] a)
    {
        int i = 0;
        while (i < 2)
        {
            Pal.Invariant(0 <= i && i <= 2);
            Pal.Decreases(2 - i);
            Length(a);
            i++;
        }
    }

    public static void GuardCall([Frac("p")] int[] a)
    {
        int i = 0;
        while (i < 2 && Length(a) > 0)
        {
            Pal.Invariant(0 <= i && i <= 2);
            Pal.Decreases(2 - i);
            i++;
        }
    }

    public static void StepCall([Frac("p")] int[] a)
    {
        int length = Length(a);
        for (int i = 0; i < 2 && i < length; i++, Length(a))
        {
            Pal.Invariant(0 <= i && i <= 2);
            Pal.Decreases(2 - i);
            if (i == 0)
            {
                continue;
            }
        }
    }

    public static void NestedLoops([Frac("p")] int[] a)
    {
        for (int i = 0; i < 2; i++)
        {
            Pal.Invariant(0 <= i && i <= 2);
            for (int j = 0; j < 2; j++)
            {
                Pal.Invariant(0 <= j && j <= 2);
                Length(a);
            }
        }
    }

    [Requires("output.Length > 0")]
    [Ensures("Contents(output).Length == Old(Contents(output)).Length")]
    [Ensures("Contents(output)[0] == 1")]
    public static void MixedPermissions([Frac("p")] int[] input, int[] output)
    {
        int i = 0;
        while (i < 2)
        {
            Pal.Invariant(0 <= i && i <= 2);
            Pal.Invariant(output.Length > 0);
            Pal.Invariant(Pal.Contents(output).Length == Pal.Old(Pal.Contents(output)).Length);
            Pal.Invariant(Pal.Implies(i > 0, Pal.Contents(output)[0] == i - 1));
            Pal.Decreases(2 - i);
            Length(input);
            output[0] = i;
            i++;
        }
    }
}
