using PalLang;

namespace PalCSharp.Tests;

public static class PlainPatterns
{
    [Preserves("OwnerSpec.Held(cell, value)")]
    public static void ResourceLoop(OwnedCell cell, int value, bool choose)
    {
        int i = 0;
        while (i < 1)
        {
            Pal.Invariant(0 <= i && i <= 1);
            Pal.Invariant(OwnerSpec.Held(cell, value));
            Pal.Decreases(1 - i);
            i++;
            if (choose) { Pal.Assert(i == 1); }
            else { Pal.Assert(i == 1); }
            Pal.Join(OwnerSpec.Held(cell, value));
        }
    }

    [Ensures("Result == (cell != null)")]
    public static bool Present(OwnedCell? cell)
    {
        if (cell is OwnedCell bound) { return true; }
        return false;
    }

    [Ensures("Result == (cell != null)")]
    public static bool TypeOnly(OwnedCell? cell) => cell is OwnedCell;

    [Requires("calls < int.MaxValue")]
    [Ensures("Result == (cell != null) && calls == Pal.Old(calls) + 1")]
    public static bool Observed(OwnedCell? cell, ref int calls)
    {
        if (PlainLocals.Observe(cell, ref calls) is OwnedCell bound)
        {
            Pal.Assert(bound == cell);
            return true;
        }
        return false;
    }

    [Requires("calls < int.MaxValue")]
    [Ensures("Result == (cell != null) && calls == Pal.Old(calls) + 1")]
    public static bool Joined(OwnedCell? cell, ref int calls)
    {
        bool found;
        if (PlainLocals.Observe(cell, ref calls) is OwnedCell bound)
        {
            Pal.Assert(bound == cell);
            found = true;
        }
        else { found = false; }
        Pal.Join(found == (cell != null));
        return found;
    }

    [Ensures("Result == cell")]
    public static CallbackCell<T>? Generic<T>(CallbackCell<T>? cell)
    {
        if (cell is CallbackCell<T> bound)
        {
            Pal.Assert(bound == cell);
            return bound;
        }
        return null;
    }
}
