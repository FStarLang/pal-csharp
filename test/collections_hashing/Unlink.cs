using System.Collections.Generic;
using PalLang;

#pragma warning disable CS0649, CS0414

// §24. Unlinking an entry the way `HashSet<T>.Remove` does, exercising the rules that needs:
// `x!` on a nullable comparer read as its value and `item is not null` at a type parameter
// (R24.23), an immutable local named by a loop invariant (R24.22), a field of an array
// element written (R24.21), an `int` snapshot measuring a loop that writes a field (R24.12),
// and an `if` one of whose arms writes a field before `return` (R24.24), whose arms write
// different arrays (R24.25).
[Spec]
public struct UnlinkModel<T>
{
    public SpecInt Free;
    public IEqualityComparer<T>? Comparer;
}

[Invariant("(_heads == null) == (_nodes == null)")]
[Invariant("_heads.Length == _nodes.Length")]
[Invariant("_comparer != null")]
public class Unlink<T>
{
    private int[]? _heads;
    private Node[]? _nodes;
    private int _free;
    private IEqualityComparer<T>? _comparer;

    [Model]
    private UnlinkModel<T> Model => new UnlinkModel<T> { Free = _free, Comparer = _comparer };

    [Spec] public SpecInt SpecFree => Model.Free;

    [Ensures("Result || @this.SpecFree == Old(@this.SpecFree)")]
    public bool Drop(T item)
    {
        Node[]? nodes = _nodes;
        if (nodes == null) return false;
        IEqualityComparer<T>? comparer = _comparer;
        int h = item is not null ? comparer!.GetHashCode(item) : 0;
        Ghost<int> length0 = nodes.Length;
        int free0 = _free;
        int i = 0;
        int last = -1;
        while (i < nodes.Length)
        {
            Pal.Invariant(_nodes != null && _heads != null && _heads.Length == nodes.Length);
            Pal.Invariant(_comparer == comparer && _comparer != null);
            Pal.Invariant(nodes.Length == length0.Value);
            Pal.Invariant(0 <= i && i <= nodes.Length && -1 <= last && last < i);
            Pal.Invariant(Pal.Implies(!Pal.Returned(), _free == free0));
            Pal.Invariant(Pal.Implies(Pal.Returned(), Pal.Result<bool>()));
            Pal.Decreases(length0.Value - i);
            if (nodes[i].Hash == h)
            {
                if (last < 0)
                {
                    _heads![0] = nodes[i].Next;
                }
                else
                {
                    nodes[last].Next = nodes[i].Next;
                }
                _free = i;
                return true;
            }
            last = i;
            i++;
        }
        return false;
    }

    private struct Node
    {
        public int Hash;
        public int Next;
        public T Value;
    }
}
