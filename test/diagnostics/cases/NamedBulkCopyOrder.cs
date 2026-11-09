// EXPECT: PALCS0001
using System;

public static class NamedBulkCopyOrder
{
    public static void Wrong(int[] src, int[] dst) =>
        Array.Copy(destinationArray: dst, sourceArray: src, length: 1);
}
