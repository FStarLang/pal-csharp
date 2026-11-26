// EXPECT: PALCS0550
using PalLang;

public sealed class BufferOwner
{
    private int[] items;

    [Model]
    private Seq<int> Model => Pal.Contents(items);

    public BufferOwner([Consumes] int[] source)
    {
        items = source;
    }
}

public static class ArrayTransferUse
{
    public static int ReadAfterTransfer()
    {
        int[] source = new int[1];
        BufferOwner owner = new BufferOwner(source);
        return source[0];
    }

    public static BufferOwner TransferParameterTwice([Consumes] int[] source)
    {
        BufferOwner first = new BufferOwner(source);
        return new BufferOwner(source);
    }
}
