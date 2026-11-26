// EXPECT-PULSE: A.pts_to
using PalLang;

namespace PalCSharp.Tests;

public sealed class ArrayKeeper
{
    private int[] data;

    [Model]
    private Seq<int> Model => Pal.Contents(data);

    public ArrayKeeper([Consumes] int[] source)
    {
        data = source;
    }
}

public static class SharedArrayTransfer
{
    // MARKER
    public static ArrayKeeper Refused([Consumes, Frac("p")] int[] source)
    {
        return new ArrayKeeper(source);
    }
}
