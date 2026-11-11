// EXPECT: PALCS0751
// R30.29. A caller's `ref` local of a method that may return `Unsafe.NullRef` holds a
// snapshot of the element's value; writing through it would write the snapshot, not the
// element, so it is refused.
using System.Runtime.CompilerServices;
using PalLang;

public static class SnapshotWriteThrough
{
    public static ref int Find(int[] values, int i)
    {
        if (0 <= i && i < values.Length) return ref values[i];
        return ref Unsafe.NullRef<int>();
    }

    public static void Set(int[] values, int i)
    {
        ref int v = ref Find(values, i);
        if (!Unsafe.IsNullRef(ref v)) v = 3;
    }
}
