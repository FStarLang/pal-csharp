// EXPECT: PALCS0751
// R30.29. A snapshot is read where the element may have changed since it was taken: the
// array is written while the `ref` local is live, so the snapshot would be stale.
using System.Runtime.CompilerServices;
using PalLang;

public static class SnapshotStale
{
    public static ref int Find(int[] values, int i)
    {
        if (0 <= i && i < values.Length) return ref values[i];
        return ref Unsafe.NullRef<int>();
    }

    public static int Get(int[] values, int i)
    {
        ref int v = ref Find(values, i);
        values[0] = 7;
        return Unsafe.IsNullRef(ref v) ? 0 : v;
    }
}
