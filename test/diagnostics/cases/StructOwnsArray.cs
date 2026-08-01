// EXPECT: PALCS0511
// R3.4. A C# struct is a value, and a value cannot own a resource. A field holding an
// array would make every copy of the struct a second owner of the same memory, which is
// exactly the situation separation logic exists to rule out. PAL needs fold/unfold
// predicates here because a C struct can be pointed into; a C# struct cannot.
using PalLang;

public struct CircularBuffer
{
    public int[] Data;
    public int Head;
    public int Count;
}

public static class Buffers
{
    [Ensures("Result >= 0")]
    public static int Size(CircularBuffer b)
    {
        return b.Count;
    }
}
