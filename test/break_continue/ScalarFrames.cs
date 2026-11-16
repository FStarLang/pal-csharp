using PalLang;

public static class ScalarFrames
{
    [Ensures("Result == x")]
    public static int Identity(int x) => x;

    [Ensures("Result == 9")]
    public static int Nested()
    {
        int total = 0;
        for (int i = 0; i < 3; i++)
        {
            Pal.Invariant(0 <= i && i <= 3 && total == 3 * i);
            for (int j = 0; j < 3; j++)
            {
                Pal.Invariant(0 <= i && i < 3 && 0 <= j && j <= 3 && total == 3 * i + j);
                int ignored = Identity(i);
                total++;
            }
        }
        return total;
    }

    [Ensures("Result == value")]
    public static int Parameter(int value)
    {
        for (int i = 0; i < 3; i++)
        {
            Pal.Invariant(0 <= i && i <= 3);
            int ignored = Identity(value);
        }
        return value;
    }

    [Requires("0 <= limit && limit < 1000")]
    [Ensures("Result == limit")]
    public static int GuardAndStep(int limit)
    {
        int i = 0;
        int stride = 1;
        for (; i < Identity(limit); i = i + Identity(stride))
        {
            Pal.Invariant(0 <= i && i <= limit);
            Pal.Decreases(limit - i);
        }
        return i;
    }

    [Requires("0 <= x && x < 1000")]
    [Ensures("x == Old(x) + 1")]
    public static void Increment(ref int x)
    {
        x++;
    }

    [Ensures("Result == 3")]
    public static int WrittenByReference()
    {
        int total = 0;
        for (int i = 0; i < 3; i++)
        {
            Pal.Invariant(0 <= i && i <= 3 && total == i);
            Increment(ref total);
        }
        return total;
    }

    [Ensures("copy == value")]
    public static void Copy(int value, out int copy)
    {
        copy = value;
    }

    [Ensures("Result == 3")]
    public static int WrittenByOut()
    {
        int total = 0;
        for (int i = 0; i < 3; i++)
        {
            Pal.Invariant(0 <= i && i <= 3 && total == i);
            Copy(i + 1, out total);
        }
        return total;
    }
}
