using PalLang;

namespace PalCSharp.Tests;

public sealed class OwnedBuffer
{
    private int[] data;

    [Model]
    private Seq<int> Model => Pal.Contents(data);

    [Spec]
    public Seq<int> Values => Model;

    [Ensures("@this.Values == Old(Contents(source))")]
    public OwnedBuffer([Consumes] int[] source)
    {
        data = source;
    }

    [Ensures("@this.Values == Old(Contents(source))")]
    public OwnedBuffer([Consumes] int[] source, bool chained) : this(source)
    {
    }

    [Ensures("@this.Values == Old(Contents(source))")]
    public OwnedBuffer([Consumes] int[] source, [Frac("p")] int[] observed)
    {
        data = source;
    }

    [Requires("source.Length > 0")]
    [Ensures("@this.Values == SetAt(Old(Contents(source)), 0, value)")]
    public OwnedBuffer([Consumes] int[] source, int value)
    {
        data = source;
        data[0] = value;
    }

    [Requires("0 <= i && i < @this.Values.Length")]
    [Ensures("Result == @this.Values[i]")]
    public int At(int i) => data[i];
}

public static class BufferTransfer
{
    [Ensures("Result.Values.Length == 2 && Result.Values[0] == 7")]
    public static OwnedBuffer FromFreshArray()
    {
        int[] source = new int[2];
        source[0] = 7;
        OwnedBuffer buffer = new OwnedBuffer(source);
        Pal.Assert(buffer.Values.Length == 2);
        return buffer;
    }

    [Ensures("Result.Values == Old(Contents(source))")]
    public static OwnedBuffer ForwardArray([Consumes] int[] source)
    {
        return new OwnedBuffer(source);
    }

    [Ensures("Result.Values == Old(Contents(source))")]
    public static OwnedBuffer TransferAndObserve([Consumes] int[] source, [Frac("p")] int[] observed)
    {
        OwnedBuffer buffer = new OwnedBuffer(source, observed);
        Pal.Assert(Pal.Contents(observed) == Pal.Old(Pal.Contents(observed)));
        int length = observed.Length;
        Pal.Assert(length >= 0);
        return buffer;
    }

    [Ensures("Result.Values == Old(Contents(source))")]
    public static OwnedBuffer EitherConstructor([Consumes] int[] source, bool chained)
    {
        if (chained)
        {
            return new OwnedBuffer(source, true);
        }
        else
        {
            return new OwnedBuffer(source);
        }
    }

    [Ensures("Result.Values.Length == 1 && Result.Values[0] == value")]
    public static OwnedBuffer InitialiseAndTransfer(int value)
    {
        int[] source = new int[1];
        return new OwnedBuffer(source, value);
    }
}
