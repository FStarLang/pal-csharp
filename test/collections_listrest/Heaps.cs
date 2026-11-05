using System.Collections.Generic;
using PalLang;

// §26. R26.10. A 4-ary min-heap's root is a least node.
public static class Heaps
{
    [Requires("0 < n && n <= nodes.Length")]
    [Requires("Pal.IsHeap(Pal.Slice(Pal.Contents(nodes), 0, n), comparer)")]
    [Ensures("Pal.Same(Result, Pal.Old(Pal.Contents(nodes))[0])")]
    [Ensures("Pal.HeapMin(Pal.Slice(Pal.Old(Pal.Contents(nodes)), 0, n), Result, comparer)")]
    public static (TE, TP) Min<TE, TP>((TE, TP)[] nodes, int n, IComparer<TP>? comparer) => nodes[0];
}
