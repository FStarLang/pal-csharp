using PalLang;

namespace PalCSharp.Tests;

public static class MixedSwitch
{
    [Requires("0 <= visits && visits <= int.MaxValue - 4")]
    [Preserves("OwnerSpec.Held(cell, expected)")]
    [Ensures("visits == Pal.Old(visits) + (selector == 0 && choose ? 3 : 4)")]
    [Ensures("Result == expected")]
    public static int Joined(int selector, bool choose, ref int visits, OwnedCell cell, int expected)
    {
        int before = visits;
        int result;
        switch (Observe(selector, ref visits))
        {
            case 0:
                if (choose) { visits++; }
                else { visits += 2; }
                Pal.Join(OwnerSpec.Held(cell, expected));
                Pal.Join(visits == before + (choose ? 2 : 3));
                result = cell.Current;
                visits++;
                return result;
            default:
                visits += 2;
                result = expected;
                break;
        }
        visits++;
        return result;
    }

    [Requires("0 <= visits && visits < int.MaxValue")]
    [Ensures("visits == Pal.Old(visits) + 1 && Result == selector")]
    public static int Observe(int selector, ref int visits)
    {
        visits++;
        return selector;
    }

    [Requires("0 <= visits && visits <= int.MaxValue - 4")]
    [Ensures("visits == Pal.Old(visits) + (selector == 0 ? 1 : 4)")]
    [Ensures("Result == (selector == 0 ? 10 : 20)")]
    public static int Bare(int selector, ref int visits)
    {
        int result;
        switch (Observe(selector, ref visits))
        {
            case 0:
                return 10;
            default:
                visits += 2;
                result = 20;
                break;
        }
        visits++;
        return result;
    }

    [Requires("0 <= visits && visits <= int.MaxValue - 4")]
    [Requires("OwnerSpec.Held(cell, expected)")]
    [Ensures("OwnerSpec.Cell(cell)")]
    [Ensures("visits == Pal.Old(visits) + (selector == 0 ? 2 : 4)")]
    [Ensures("Result == expected")]
    public static int WithWitness(int selector, ref int visits, OwnedCell cell, int expected)
    {
        int result;
        switch (Observe(selector, ref visits))
        {
            case 0:
#if PAL
                Ghost<CellSnapshot> early = WitnessProof.UnpackKnown(cell, expected);
                WitnessProof.Pack(cell, early);
#endif
                visits++;
                return expected;
            default:
                visits += 2;
                result = expected;
                break;
        }
#if PAL
        Ghost<CellSnapshot> later = WitnessProof.UnpackKnown(cell, expected);
        WitnessProof.Pack(cell, later);
#endif
        visits++;
        return result;
    }
}
