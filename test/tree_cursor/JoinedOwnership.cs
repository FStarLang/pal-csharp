using PalLang;

namespace PalCSharp.Tests;

public static class JoinedOwnership
{
    [Requires("Descent.Held(node, oldKey, value, left, right)")]
    [Ensures("Descent.Held(node, Result, value, left, right)")]
    [Ensures("Result == (chooseFirst ? first : second)")]
    public static int ChooseKey<T>(Knot<T> node, int oldKey, T value,
        Knot<T>? left, Knot<T>? right, int first, int second, bool chooseFirst)
    {
        int selected = oldKey;
        if (chooseFirst)
        {
            node.key = first;
            selected = first;
        }
        else
        {
            node.key = second;
            selected = second;
        }
        Pal.Join(Descent.Held(node, selected, value, left, right));
        Pal.Join(selected == (chooseFirst ? first : second));
        return node.key;
    }
}
