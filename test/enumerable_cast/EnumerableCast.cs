using System;
using System.Collections;
using System.Collections.Generic;
using PalLang;

[assembly: TranslateAnnotatedOnly]

[Invariant("_items.Length == 1")]
public sealed class Packet : IEnumerable<int>
{
    private int[] _items;
    [Model] private Seq<int> Model => Pal.Contents(_items);
    [Spec] public Seq<int> Items => Model;

    [Ensures("@this.Items.Length == 1 && @this.Items[0] == value")]
    public Packet(int value)
    {
        _items = new int[1];
        _items[0] = value;
    }

    [Ensures("Result == @this.Items.Length")]
    public int Count => _items.Length;

    [Requires("index >= 0 && index + @this.Items.Length <= Pal.Contents(array).Length")]
    [Ensures("Pal.Contents(array) == Pal.Splice(Pal.Old(Pal.Contents(array)), index, index + @this.Items.Length, @this.Items)")]
    [Frac("p")]
    public void CopyTo(int[] array, int index) =>
        Array.Copy(_items, 0, array, index, _items.Length);

    [Ensures("@this.Items.Length == 1 && Pal.Yielded<int>().Length == 1 && Pal.Yielded<int>()[0] == @this.Items[0]")]
    public IEnumerator<int> GetEnumerator()
    {
        yield return _items[0];
    }

    IEnumerator IEnumerable.GetEnumerator() => GetEnumerator();
}

// Nominally distinct, even though its representation and logical model have the
// same shape. Disjointness follows from sealed CLR classes, not that shape.
[Invariant("_items.Length == 1")]
public sealed class Envelope : IEnumerable<int>
{
    private int[] _items;
    [Model] private Seq<int> Model => Pal.Contents(_items);
    [Spec] public Seq<int> Items => Model;

    [Ensures("@this.Items.Length == 1 && @this.Items[0] == value")]
    public Envelope(int value)
    {
        _items = new int[1];
        _items[0] = value;
    }

    [Ensures("Result == @this.Items.Length")]
    public int Count => _items.Length;

    [Requires("index >= 0 && index + @this.Items.Length <= Pal.Contents(array).Length")]
    [Ensures("Pal.Contents(array) == Pal.Splice(Pal.Old(Pal.Contents(array)), index, index + @this.Items.Length, @this.Items)")]
    [Frac("p")]
    public void CopyTo(int[] array, int index) =>
        Array.Copy(_items, 0, array, index, _items.Length);

    [Ensures("@this.Items.Length == 1 && Pal.Yielded<int>().Length == 1 && Pal.Yielded<int>()[0] == @this.Items[0]")]
    public IEnumerator<int> GetEnumerator()
    {
        yield return _items[0];
    }

    IEnumerator IEnumerable.GetEnumerator() => GetEnumerator();
}

public static class EnumerableCast
{
    [Requires("Pal.Contents(other).Length == 1")]
    [Ensures("Result == (other is Packet)")]
    public static bool IsPacket(IEnumerable<int> other)
    {
        bool result = false;
        if (other is Packet packet)
        {
            // A real concrete member call under transferred ownership.
            int n = packet.Count;
            Pal.Assert(packet.Items.Length == 1);
            Pal.Assert(n == 1);
            result = n == 1;
        }
        else
        {
            // A failed cast still retains the source and its checked snapshot.
            using IEnumerator<int> e = other.GetEnumerator();
            bool more = e.MoveNext();
            int item = e.Current;
            result = !more;
        }
        return result;
    }

    [Ensures("Result == true")]
    public static bool Successful()
    {
        Packet packet = new Packet(7);
        bool result = IsPacket(packet);
        // Both the source and its logical contents were restored.
        Pal.Assert(packet.Items.Length == 1 && packet.Items[0] == 7);
        return result;
    }

    [Ensures("Result == false")]
    public static bool Failed()
    {
        Envelope envelope = new Envelope(7);
        bool result = IsPacket(envelope);
        Pal.Assert(envelope.Items.Length == 1 && envelope.Items[0] == 7);
        return result;
    }
}
