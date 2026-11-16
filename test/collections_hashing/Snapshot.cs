using System.Runtime.CompilerServices;
using PalLang;

// R30.29: a method that returns a `ref` to an element, or `Unsafe.NullRef` when there is
// none, is translated as one returning the element's value as an option; its `ref` locals
// are option locals, and a caller's `ref` local holds a snapshot of the value. This is the
// shape of `Dictionary<TKey, TValue>.FindValue`: labels jumped to from inside a loop, one of
// them by a backward `goto`, and a `ref` local declared under a label and rebound.
public static class Snapshot
{
    [Requires("keys.Length == values.Length")]
    [Ensures("Pal.Iff(Unsafe.IsNullRef(ref Result), Pal.Forall((int k) => Pal.Implies(0 <= k && k < keys.Length, Contents(keys)[k] != x)))")]
    [Ensures("Pal.Implies(!Unsafe.IsNullRef(ref Result), Pal.Exists((int k) => 0 <= k && k < keys.Length && k < values.Length && Contents(keys)[k] == x && Contents(values)[k] == Result))")]
    [Ensures("Contents(keys) == Old(Contents(keys)) && Contents(values) == Old(Contents(values))")]
    public static ref int Find(int[] keys, int[] values, int x)
    {
        ref int entry = ref Unsafe.NullRef<int>();
        int i = 0;
        while (i < keys.Length)
        {
            Pal.Invariant(0 <= i && i <= keys.Length);
            Pal.Invariant(Pal.Implies(!Pal.Returned(), Pal.Forall((int k) => Pal.Implies(0 <= k && k < i, Pal.Contents(keys)[k] != x))));
            Pal.Invariant(Pal.Implies(Pal.Returned(), !Unsafe.IsNullRef(ref Pal.ResultRef<int>()) && i < keys.Length && Pal.Contents(keys)[i] == x && Pal.Contents(values)[i] == Pal.ResultRef<int>()));
            Pal.Decreases(keys.Length - i);
            if (keys[i] == x)
            {
                entry = ref values[i];
                goto ReturnFound;
            }
            i++;
        }
        goto ReturnNotFound;

    ReturnFound:
        ref int value = ref entry;
    Return:
        return ref value;
    ReturnNotFound:
        value = ref Unsafe.NullRef<int>();
        goto Return;
    }

    [Requires("keys.Length == values.Length")]
    [Ensures("Result == Pal.Exists((int k) => 0 <= k && k < keys.Length && Contents(keys)[k] == x)")]
    [Ensures("Contents(keys) == Old(Contents(keys)) && Contents(values) == Old(Contents(values))")]
    public static bool Contains(int[] keys, int[] values, int x) =>
        !Unsafe.IsNullRef(ref Find(keys, values, x));

    // The caller's snapshot is read after a call that writes nothing.
    [Requires("keys.Length == values.Length")]
    [Ensures("Pal.Implies(Result != -1, Pal.Exists((int k) => 0 <= k && k < keys.Length && k < values.Length && Contents(keys)[k] == x && Contents(values)[k] == Result))")]
    public static int GetOr(int[] keys, int[] values, int x)
    {
        ref int v = ref Find(keys, values, x);
        bool found = Contains(keys, values, x);
        if (!Unsafe.IsNullRef(ref v) && v != -1)
        {
            return v;
        }
        return -1;
    }
}
