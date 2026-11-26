// EXPECT-PULSE: class_ArrayWriter__inv
using PalLang;

namespace PalCSharp.Tests;

[Invariant("items.Length > 0")]
public sealed class ArrayWriter
{
    private int[] items;

    [Refine("Result.Length > 0")]
    [Model]
    private Seq<int> Model => Pal.Contents(items);

    [Spec]
    public Seq<int> Values => Model;

    public ArrayWriter()
    {
        items = new int[1];
    }

    public void Write([Frac("p")] int[] other)
    {
        ArrayWriteCalls.Write(other, items);
    }
}

public static class ArrayWriteCalls
{
    [Requires("a.Length > 0")]
    public static void Write([Frac("p")] int[] other, int[] a)
    {
        a[0] = 1;
    }

    public static void Refused([Frac("p")] ArrayWriter owner, [Frac("q")] int[] other)
    {
        // MARKER
        owner.Write(other);
    }
}
