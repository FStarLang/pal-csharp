using PalLang;

namespace PalCSharp.Tests;

[Invariant("items.Length > 0")]
public sealed class ArrayOwner
{
    private int[] items;

    [Refine("Result.Length > 0")]
    [Model]
    private Seq<int> Model => Pal.Contents(items);

    [Spec]
    public Seq<int> Values => Model;

    [Ensures("@this.Values.Length == 1 && @this.Values[0] == 0")]
    public ArrayOwner()
    {
        items = new int[1];
    }

    [Ensures("Result == @this.Values[0]")]
    public int Read() => ArrayOwnerCalls.ReadFirst((this.items));

    [Ensures("Result == @this.Values[0]")]
    public int ReadForwarded() => Read();

    [Ensures("Result == @this.Values[0]")]
    public int ReadWithOther([Frac("q")] int[] other) =>
        ArrayOwnerCalls.ReadWithOther(other: other, a: items);

    [Ensures("@this.Values[0] == value")]
    public void Write(int value)
    {
        ArrayOwnerCalls.WriteFirst(items, value);
    }
}

public static class ArrayOwnerCalls
{
    [Requires("a.Length > 0")]
    [Ensures("Result == Contents(a)[0]")]
    public static int ReadFirst([Frac("p")] int[] a) => a[0];

    [Requires("a.Length > 0")]
    [Ensures("Result == Contents(a)[0]")]
    public static int ReadWithOther([Frac("q")] int[] other, [Frac("p")] int[] a) => a[0];

    [Requires("a.Length > 0")]
    [Ensures("Contents(a) == SetAt(Old(Contents(a)), 0, value)")]
    public static void WriteFirst(int[] a, int value)
    {
        a[0] = value;
    }

    [Ensures("Result == owner.Values[0]")]
    public static int Observe([Frac("p")] ArrayOwner owner, [Frac("q")] int[] other)
    {
        int first = owner.Read();
        int forwarded = owner.ReadForwarded();
        int withOther = owner.ReadWithOther(other);
        Pal.Assert(first == forwarded && forwarded == withOther);
        return first;
    }

    [Ensures("Result == (a.Values[0] == b.Values[0])")]
    public static bool SameFirst([Frac("p")] ArrayOwner a, [Frac("q")] ArrayOwner b)
    {
        return a.Read() == b.Read();
    }

    [Ensures("Result && owner.Values[0] == value")]
    public static bool ShareReadGatherWrite(ArrayOwner owner, int value)
    {
        Pal.Share(owner);
        bool same = SameFirst(owner, owner);
        Pal.Gather(owner);
        owner.Write(value);
        return same;
    }
}
